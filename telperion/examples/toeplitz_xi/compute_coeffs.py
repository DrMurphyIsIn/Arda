"""Reproduce a_coeffs.json: exact rational enclosures of a_k = [z^{2k}] xi(1/2+z),
k=0..7 (mpmath; the transcendental import, out of the sympy-only core).

    python3 examples/toeplitz_xi/compute_coeffs.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
KMAX, DPS, SCALE, AGREE = 7, 60, 10 ** 25, 1e-38


def compute() -> dict:
    import mpmath as mp

    def xi(s):
        return mp.mpf("0.5") * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

    def acoef(r):
        mp.mp.dps = DPS
        c = mp.taylor(lambda z: xi(mp.mpf("0.5") + z), 0, 2 * KMAX + 1, method="quad", radius=mp.mpf(r))
        return [mp.re(c[2 * k]) for k in range(KMAX + 1)]

    a1, a2 = acoef("1.0"), acoef("3.0")
    enc = {}
    for k in range(KMAX + 1):
        if not abs(a1[k] - a2[k]) < mp.mpf(str(AGREE)):
            raise RuntimeError(f"a_{k}: cross-radius disagreement too large")
        n = int(mp.floor(a1[k] * SCALE))
        if not (mp.mpf(n) / SCALE < a1[k] < mp.mpf(n + 1) / SCALE):
            raise RuntimeError(f"a_{k}: straddle failed")
        enc[str(k)] = [str(Fr(n, SCALE)), str(Fr(n + 1, SCALE))]
    return {"enclosures": enc,
            "meta": {"source": "a_k = [z^{2k}] xi(1/2+z)", "dps": DPS,
                     "radius_crosscheck": ["1.0", "3.0"], "scale": SCALE}}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    data = compute()
    path = HERE / "a_coeffs.json"
    if args.check:
        ok = json.loads(path.read_text())["enclosures"] == data["enclosures"]
        print("check:", "OK" if ok else "DRIFT")
        return 0 if ok else 1
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"wrote {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
