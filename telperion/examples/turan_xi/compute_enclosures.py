"""Reproduce enclosures.json: exact rational windows lo_k < a_k < hi_k around the
even Taylor coefficients a_k = [z^{2k}] xi(1/2 + z) of the Riemann xi function.

This is the TRANSCENDENTAL IMPORT step, deliberately kept OUT of the
dependency-light (sympy-only) Telperion core: it needs mpmath.  The enclosures
it emits are the only numeric input the certificate trusts; everything
downstream is exact rational arithmetic + kernel-checked Lean.

Method.  xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s) is entire; the even
Taylor coefficients of xi(1/2 + z) are extracted by a Cauchy contour integral
(mpmath `taylor(..., method='quad')`), which is numerically stable.  We compute
at two independent contour radii and REQUIRE agreement to >40 digits before
forming rational windows of width 1e-25 (>> the ~1e-40 disagreement floor).

    python3 examples/turan_xi/compute_enclosures.py [--check]

Without --check: (re)writes enclosures.json.  With --check: recomputes and
diffs against the committed file (nonzero exit on drift).
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
K = 4                       # coefficients a_0 .. a_4  (certifies Turan k=1,2,3)
DPS = 60
SCALE = 10 ** 25            # rational window granularity
AGREE = 1e-40               # required cross-radius disagreement ceiling


def _a_coeffs(mp, k_max, digits, radius):
    mp.mp.dps = digits

    def xi(s):
        return mp.mpf("0.5") * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

    def f(z):
        return xi(mp.mpf("0.5") + z)

    c = mp.taylor(f, 0, 2 * k_max + 1, method="quad", radius=mp.mpf(radius))
    return [c[2 * k] for k in range(k_max + 1)]


def compute() -> dict:
    import mpmath as mp

    a1 = _a_coeffs(mp, K, DPS, "1.0")
    a2 = _a_coeffs(mp, K, DPS, "3.0")          # independent contour radius
    enc = {}
    for k in range(K + 1):
        disagree = abs(a1[k] - a2[k])
        if not disagree < mp.mpf(str(AGREE)):
            raise RuntimeError(f"a_{k}: cross-radius disagreement {disagree} too large")
        n = int(mp.floor(a1[k] * SCALE))
        lo, hi = Fr(n, SCALE), Fr(n + 1, SCALE)
        if not (mp.mpf(n) / SCALE < a1[k] < mp.mpf(n + 1) / SCALE):
            raise RuntimeError(f"a_{k}: enclosure straddle failed")
        enc[str(k)] = [str(lo), str(hi)]
    return {
        "enclosures": enc,
        "meta": {
            "source": "a_k = [z^{2k}] xi(1/2+z), even Taylor coeffs of Riemann xi",
            "method": "mpmath taylor(method='quad'), Cauchy contour integral",
            "dps": DPS,
            "radius_crosscheck": ["1.0", "3.0"],
            "cross_agreement": ">40 digits",
            "scale": SCALE,
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    data = compute()
    path = HERE / "enclosures.json"
    if args.check:
        committed = json.loads(path.read_text())
        ok = committed["enclosures"] == data["enclosures"]
        print("check:", "OK" if ok else "DRIFT")
        return 0 if ok else 1
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"wrote {path} ({K + 1} enclosures)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
