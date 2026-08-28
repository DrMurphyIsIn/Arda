"""Reproduce gammas.json: exact rational enclosures lo_k < gamma_k < hi_k of the
EGF/Jensen coefficients  gamma_k = k! * a_k,  a_k = [z^{2k}] xi(1/2+z).

This is the transcendental import (mpmath), kept OUT of the sympy-only core.
Normalization note: gamma_k = k! a_k is the EGF coefficient sequence of
G(u) = sum_k a_k u^k, whose Laguerre-Polya membership is equivalent to RH; it is
the sequence whose Jensen polynomials are hyperbolic <=> RH.  (Empirically: (2k)!
a_k is NOT the right one -- its Jensen polynomials are not hyperbolic.)

    python3 examples/jensen_xi/compute_gammas.py [--check]
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
KMAX = 5                      # gamma_0 .. gamma_5  (certifies cubic shifts n=0,1,2)
DPS = 60
SCALE = 10 ** 25
AGREE = 1e-40


def _a(mp, k_max, digits, radius):
    mp.mp.dps = digits

    def xi(s):
        return mp.mpf("0.5") * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

    c = mp.taylor(lambda z: xi(mp.mpf("0.5") + z), 0, 2 * k_max + 1,
                  method="quad", radius=mp.mpf(radius))
    return [c[2 * k] for k in range(k_max + 1)]


def compute() -> dict:
    import mpmath as mp

    a1 = _a(mp, KMAX, DPS, "1.0")
    a2 = _a(mp, KMAX, DPS, "3.0")
    enc = {}
    for k in range(KMAX + 1):
        if not abs(a1[k] - a2[k]) < mp.mpf(str(AGREE)):
            raise RuntimeError(f"a_{k}: cross-radius disagreement too large")
        g = mp.factorial(k) * a1[k]                 # gamma_k = k! a_k
        n = int(mp.floor(g * SCALE))
        lo, hi = Fr(n, SCALE), Fr(n + 1, SCALE)
        if not (mp.mpf(n) / SCALE < g < mp.mpf(n + 1) / SCALE):
            raise RuntimeError(f"gamma_{k}: enclosure straddle failed")
        enc[str(k)] = [str(lo), str(hi)]
    return {
        "enclosures": enc,
        "meta": {
            "source": "gamma_k = k! * a_k, a_k = [z^{2k}] xi(1/2+z) (EGF/Jensen normalization)",
            "why": "RH <=> G(u)=sum a_k u^k in Laguerre-Polya <=> Jensen polys of gamma_k=k!a_k hyperbolic",
            "dps": DPS, "radius_crosscheck": ["1.0", "3.0"], "scale": SCALE,
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    data = compute()
    path = HERE / "gammas.json"
    if args.check:
        ok = json.loads(path.read_text())["enclosures"] == data["enclosures"]
        print("check:", "OK" if ok else "DRIFT")
        return 0 if ok else 1
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"wrote {path} ({KMAX + 1} enclosures)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
