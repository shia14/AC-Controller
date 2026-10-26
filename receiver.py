#!/usr/bin/env python3
"""
AC Phone Controller - PC receiver (Windows)

  iPhone (Safari) --wss--> this script --> virtual Xbox 360 pad --> Assetto Corsa
  Assetto Corsa --UDP 9996--> this script --wss--> phone dashboard + haptics

Setup:
  1. Install ViGEmBus  (https://github.com/nefarius/ViGEmBus/releases)
  2. pip install aiohttp vgamepad cryptography
  3. python receiver.py
"""
import argparse
import asyncio
import datetime
import ipaddress
import json
import math
import socket
import ssl
import struct
import threading
import time
from pathlib import Path

from aiohttp import web, WSMsgType
import vgamepad as vg

HERE = Path(__file__).resolve().parent
AC_ADDR = ("127.0.0.1", 9996)
SEND_HZ = 30

# ---- Tunables for the receiver-side assists (live-adjustable ones are in DEFAULTS) ----
DEFAULTS = dict(expo=0.25, speedSens=0.35, smooth=15.0, ramp=6.0, tc=0.6, abs=0.6)
LIMITS = dict(expo=(0, 1), speedSens=(0, 1), smooth=(0, 100), ramp=(1, 50), tc=(0, 1), abs=(0, 1))
MIN_STEER_SCALE = 0.25     # speed sensitivity never reduces steering below this fraction
BRAKE_GAMMA = 1.3          # >1 = finer control at the start of the pedal travel
TC_SLIP_START = 0.18       # rear slip ratio where the throttle cut begins
TC_SLIP_RANGE = 0.30       # ...and the extra slip over which it reaches full strength
ABS_SLIP_START = 0.25      # front slip ratio where brake release begins
ABS_SLIP_RANGE = 0.35
STALE_TELEMETRY = 0.5      # seconds before telemetry is considered gone
INPUT_TIMEOUT = 0.4        # seconds without phone input before the pad is zeroed

# Phone button bit -> Xbox button
BUTTONS = [
    (0, vg.XUSB_BUTTON.XUSB_GAMEPAD_RIGHT_SHOULDER),  # shift up
    (1, vg.XUSB_BUTTON.XUSB_GAMEPAD_LEFT_SHOULDER),   # shift down
    (2, vg.XUSB_BUTTON.XUSB_GAMEPAD_A),               # pit limiter
    (3, vg.XUSB_BUTTON.XUSB_GAMEPAD_X),               # headlights
    (4, vg.XUSB_BUTTON.XUSB_GAMEPAD_Y),               # change view
]


def clamp(x, lo, hi):
    return lo if x < lo else hi if x > hi else x


def gear_label(g):
    # AC remote telemetry: 0 = reverse, 1 = neutral, 2 = first gear.
    # If your dash is off by one, change this function.
    return "R" if g == 0 else "N" if g == 1 else str(g - 1)


def parse_rtcarinfo(d):
    """Decode the 328-byte RTCarInfo packet (natural C alignment)."""
    return dict(
        v=struct.unpack_from("<f", d, 8)[0],                       # km/h
        ab=struct.unpack_from("<?", d, 21)[0],                     # ABS in action
        tc=struct.unpack_from("<?", d, 22)[0],                     # TC in action
        pit=struct.unpack_from("<?", d, 24)[0],
        lim=struct.unpack_from("<?", d, 25)[0],                    # engine limiter
        gl=struct.unpack_from("<f", d, 32)[0],                     # lateral g
        lt=struct.unpack_from("<i", d, 40)[0],
        ll=struct.unpack_from("<i", d, 44)[0],
        bl=struct.unpack_from("<i", d, 48)[0],
        lap=struct.unpack_from("<i", d, 52)[0],
        rpm=struct.unpack_from("<f", d, 68)[0],
        gear=struct.unpack_from("<i", d, 76)[0],
        sr=struct.unpack_from("<4f", d, 132),                      # slip ratio FL FR RL RR
    )


class Controller:
    def __init__(self):
        self.pad = vg.VX360Gamepad()
        self.cfg = dict(DEFAULTS)
        self.tel = {}
        self.tel_time = 0.0
        self.t_prev = time.perf_counter()
        self.last_input = 0.0
        self.steer_f = 0.0
        self.thr_f = 0.0
        self.buttons = 0
        self.assist_h = 0.0
        self.tel_h = 0.0
        self.max_rpm = 1000.0
        self.last_gear = None
        self.events = []
        self.clients = set()
        self._gmax, self._n, self._w0 = 0.0, 0, time.perf_counter()
        self.gap_ms, self.rate = 0, 0

    # ---------------- phone -> pad ----------------
    def set_cfg(self, d):
        for k, v in d.items():
            if k in LIMITS and isinstance(v, (int, float)):
                lo, hi = LIMITS[k]
                self.cfg[k] = clamp(float(v), lo, hi)

    def on_input(self, steer, thr, brk, btn):
        now = time.perf_counter()
        dt = clamp(now - self.t_prev, 0.001, 0.05)
        self.t_prev = now
        prev, self.last_input = self.last_input, now
        if prev:
            self._gmax = max(self._gmax, now - prev)     # longest silence between phone packets
        self._n += 1
        if now - self._w0 >= 1.0:
            self.gap_ms, self.rate = int(self._gmax * 1000), self._n
            self._gmax, self._n, self._w0 = 0.0, 0, now
        c = self.cfg
        t = self.tel if (now - self.tel_time) < STALE_TELEMETRY else {}
        speed = t.get("v", 0.0)

        # Steering: softer centre, speed-sensitive lock, light smoothing
        s = clamp(steer, -1.0, 1.0)
        s = (1 - c["expo"]) * s + c["expo"] * s * s * s
        s *= max(MIN_STEER_SCALE, 1.0 / (1.0 + c["speedSens"] * (speed / 100.0) ** 2))
        tau = c["smooth"] / 1000.0
        a = 1.0 if tau <= 0 else 1.0 - math.exp(-dt / tau)
        self.steer_f += (s - self.steer_f) * a

        # Throttle: rise-rate limit, then traction assist on rear wheelspin
        th = clamp(thr, 0.0, 1.0)
        if th > self.thr_f:
            self.thr_f = min(th, self.thr_f + c["ramp"] * dt)
        else:
            self.thr_f = th
        tc_cut = 0.0
        if c["tc"] > 0 and speed > 5 and "sr" in t:
            rear = max(abs(t["sr"][2]), abs(t["sr"][3]))
            tc_cut = clamp((rear - TC_SLIP_START) / TC_SLIP_RANGE, 0, 1) * c["tc"]
        th_out = self.thr_f * (1.0 - tc_cut)

        # Brake: progressive curve, release when the front wheels start to lock
        b = clamp(brk, 0.0, 1.0) ** BRAKE_GAMMA
        abs_rel = 0.0
        if c["abs"] > 0 and speed > 10 and b > 0.05 and "sr" in t:
            front = max(abs(t["sr"][0]), abs(t["sr"][1]))
            abs_rel = clamp((front - ABS_SLIP_START) / ABS_SLIP_RANGE, 0, 1) * c["abs"]
            b *= 1.0 - abs_rel
        self.assist_h = 0.8 * max(tc_cut, abs_rel)

        p = self.pad
        p.left_joystick_float(x_value_float=clamp(self.steer_f, -1, 1), y_value_float=0.0)
        p.right_trigger_float(value_float=th_out)
        p.left_trigger_float(value_float=b)
        changed = btn ^ self.buttons
        if changed:
            for bit, xb in BUTTONS:
                if changed & (1 << bit):
                    if btn & (1 << bit):
                        p.press_button(button=xb)
                    else:
                        p.release_button(button=xb)
            self.buttons = btn
        p.update()

    def neutral(self):
        self.steer_f = self.thr_f = 0.0
        self.assist_h = 0.0
        p = self.pad
        p.left_joystick_float(x_value_float=0.0, y_value_float=0.0)
        p.right_trigger_float(value_float=0.0)
        p.left_trigger_float(value_float=0.0)
        for _, xb in BUTTONS:
            p.release_button(button=xb)
        self.buttons = 0
        p.update()

    # ---------------- AC -> phone ----------------
    def on_telemetry(self, t):
        self.tel = t
        self.tel_time = time.perf_counter()
        self.max_rpm = max(self.max_rpm, t["rpm"])
        if self.last_gear is not None and t["gear"] != self.last_gear:
            self.events.append("shift")
        self.last_gear = t["gear"]

        # Haptic intensity 0..1 (the phone turns this into a pulse rate)
        speed = t["v"]
        if t["lim"]:
            h = 0.9
        elif t["ab"]:
            h = 0.7
        elif t["tc"]:
            h = 0.6
        else:
            slip = max(abs(x) for x in t["sr"]) if speed > 5 else 0.0
            h = clamp((slip - 0.2) / 0.6, 0, 1) * 0.8
            h = max(h, clamp((abs(t["gl"]) - 1.5) / 2.0, 0, 1) * 0.4)
        self.tel_h = h

    def snapshot(self):
        live = (time.perf_counter() - self.tel_time) < STALE_TELEMETRY
        msg = {"live": live, "so": round(self.steer_f, 3), "gp": self.gap_ms, "rt": self.rate}
        if live:
            t = self.tel
            msg.update(
                v=round(t["v"], 1), rpm=int(t["rpm"]), mx=int(self.max_rpm),
                g=gear_label(t["gear"]), gl=round(t["gl"], 2),
                ab=int(t["ab"]), tc=int(t["tc"]), lim=int(t["lim"]), pit=int(t["pit"]),
                lt=t["lt"], ll=t["ll"], bl=t["bl"], lap=t["lap"],
                hz=round(max(self.tel_h, self.assist_h), 2),
            )
        if self.events:
            msg["ev"], self.events = self.events, []
        return json.dumps(msg, separators=(",", ":"))


class ACTelemetry(threading.Thread):
    """Assetto Corsa remote telemetry on a plain blocking socket (reliable on Windows)."""

    def __init__(self, ctrl):
        super().__init__(daemon=True)
        self.ctrl = ctrl

    def run(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind(("127.0.0.1", 0))
        sock.settimeout(0.5)
        seen, last_hs, last_msg, warned = set(), 0.0, 0.0, False
        while True:
            now = time.perf_counter()
            if now - self.ctrl.tel_time > 2.0:
                if now - last_hs > 1.0:        # keep asking until AC answers
                    last_hs = now
                    try:
                        sock.sendto(struct.pack("<iii", 1, 1, 0), AC_ADDR)
                    except OSError:
                        pass
                if now - last_msg > 10.0:
                    last_msg = now
                    print("[AC telemetry] waiting for Assetto Corsa to answer on 127.0.0.1:9996 ...")
            try:
                data, _ = sock.recvfrom(2048)
            except socket.timeout:
                continue
            except OSError:
                time.sleep(0.05)               # Windows: "connection reset" while AC isn't listening yet
                continue
            try:
                if len(data) not in seen:
                    seen.add(len(data))
                    print(f"[AC telemetry] received a {len(data)}-byte packet from AC")
                if len(data) == 328:
                    self.ctrl.on_telemetry(parse_rtcarinfo(data))
                else:                          # handshake response -> subscribe to updates
                    self.ctrl.max_rpm = 1000.0
                    sock.sendto(struct.pack("<iii", 1, 1, 1), AC_ADDR)
            except Exception as e:
                if not warned:
                    warned = True
                    print("[AC telemetry] could not read a packet:", repr(e))


# ---------------- HTTPS / WebSocket ----------------
async def ws_handler(request):
    ctrl = request.app["ctrl"]
    ws = web.WebSocketResponse(compress=False, max_msg_size=4096)
    await ws.prepare(request)
    try:   # send every packet immediately instead of letting TCP batch them
        request.transport.get_extra_info("socket").setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
    except Exception:
        pass
    ctrl.clients.add(ws)
    try:
        async for msg in ws:
            if msg.type != WSMsgType.TEXT:
                continue
            try:
                m = json.loads(msg.data)
                if isinstance(m, list) and len(m) == 4:
                    ctrl.on_input(float(m[0]), float(m[1]), float(m[2]), int(m[3]))
                elif isinstance(m, dict):
                    if "cfg" in m and isinstance(m["cfg"], dict):
                        ctrl.set_cfg(m["cfg"])
                    if "ping" in m:
                        await ws.send_str(json.dumps({"pong": m["ping"]}))
            except (ValueError, TypeError):
                continue
    finally:
        ctrl.clients.discard(ws)
        if not ctrl.clients:
            ctrl.neutral()
    return ws


async def index(request):
    return web.FileResponse(HERE / "index.html", headers={"Cache-Control": "no-store"})


async def sender(ctrl):
    while True:
        await asyncio.sleep(1 / SEND_HZ)
        if ctrl.clients:
            s = ctrl.snapshot()
            await asyncio.gather(*(ws.send_str(s) for ws in list(ctrl.clients)), return_exceptions=True)


async def watchdog(ctrl):
    while True:
        await asyncio.sleep(0.2)
        now = time.perf_counter()
        if ctrl.last_input and now - ctrl.last_input > INPUT_TIMEOUT:
            ctrl.neutral()
            ctrl.last_input = 0.0


# ---------------- certificate ----------------
def local_ips(extra):
    ips = {"127.0.0.1"}
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ips.add(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(info[4][0])
    except OSError:
        pass
    ips.update(extra)
    return sorted(ips)


def ensure_cert(ips, regen):
    cert_p, key_p, meta_p = HERE / "cert.pem", HERE / "key.pem", HERE / "cert.ips"
    if not regen and cert_p.exists() and key_p.exists() and meta_p.exists():
        if set(ips) <= set(meta_p.read_text().split()):
            return
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa
    from cryptography.x509.oid import ExtendedKeyUsageOID, NameOID

    key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "AC Phone Controller")])
    now = datetime.datetime.now(datetime.timezone.utc)
    san = [x509.DNSName("localhost")] + [x509.IPAddress(ipaddress.ip_address(i)) for i in ips]
    cert = (
        x509.CertificateBuilder()
        .subject_name(name).issuer_name(name).public_key(key.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(now - datetime.timedelta(days=1))
        .not_valid_after(now + datetime.timedelta(days=365))
        .add_extension(x509.SubjectAlternativeName(san), critical=False)
        .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
        .add_extension(x509.ExtendedKeyUsage([ExtendedKeyUsageOID.SERVER_AUTH]), critical=False)
        .sign(key, hashes.SHA256())
    )
    cert_p.write_bytes(cert.public_bytes(serialization.Encoding.PEM))
    key_p.write_bytes(key.private_bytes(
        serialization.Encoding.PEM, serialization.PrivateFormat.TraditionalOpenSSL,
        serialization.NoEncryption()))
    meta_p.write_text("\n".join(ips))
    print("Generated a new certificate for:", ", ".join(ips))


async def run(args):
    ips = local_ips(args.ip)
    ensure_cert(ips, args.regen_cert)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(str(HERE / "cert.pem"), str(HERE / "key.pem"))

    ctrl = Controller()
    ACTelemetry(ctrl).start()

    app = web.Application()
    app["ctrl"] = ctrl
    app.add_routes([web.get("/", index), web.get("/ws", ws_handler)])
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", args.port, ssl_context=ctx).start()

    async def cert_page(request):
        return web.Response(
            text="<meta name=viewport content='width=device-width'>"
                 "<body style='font:20px system-ui;padding:24px'>"
                 "<a href='/ac.crt'>Install the controller certificate</a>",
            content_type="text/html")

    async def cert_file(request):
        return web.Response(body=(HERE / "cert.pem").read_bytes(),
                            content_type="application/x-x509-ca-cert")

    app2 = web.Application()
    app2.add_routes([web.get("/", cert_page), web.get("/ac.crt", cert_file)])
    runner2 = web.AppRunner(app2)
    await runner2.setup()
    await web.TCPSite(runner2, "0.0.0.0", args.http_port).start()

    print("\nOpen on the iPhone (Safari):")
    for ip in ips:
        if not ip.startswith("127."):
            print(f"  https://{ip}:{args.port}      (certificate: http://{ip}:{args.http_port})")
    print("\nWaiting for the phone and Assetto Corsa. Ctrl+C to quit.")

    tasks = [asyncio.create_task(sender(ctrl)), asyncio.create_task(watchdog(ctrl))]
    try:
        await asyncio.Event().wait()
    finally:
        for t in tasks:
            t.cancel()
        ctrl.neutral()


def main():
    ap = argparse.ArgumentParser(description="AC phone controller receiver")
    ap.add_argument("--port", type=int, default=8443, help="HTTPS/WebSocket port")
    ap.add_argument("--http-port", type=int, default=8080, help="plain HTTP port used only to install the certificate")
    ap.add_argument("--ip", action="append", default=[], help="extra IP to put in the certificate (repeatable)")
    ap.add_argument("--regen-cert", action="store_true")
    args = ap.parse_args()
    try:
        asyncio.run(run(args))
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()