"""Beurling reduction, Hermite-function facts (scout claim 5): numerical and Arb checks.

conjecture1_proved = False.  Nothing here is kernel-checked.

Claim checked.  For an even positive measure M = c0 delta_0 + sum_nu w_nu (delta_nu + delta_{-nu})
with gap (0,1) in its support and M^ = eps M (the Poisson-type form of a zeta-shape FE),
pair M with Hermite functions h_n(x) = H_n(y) e^{-pi x^2}, y = sqrt(2 pi) x, which satisfy
h_n^ = (-i)^n h_n for the transform f^(xi) = int f(x) e^{-2 pi i x xi} dx.
  * f_plus = h_4 - 12 h_0 = 16 y^2 (y^2 - 3) e^{-pi x^2} is a (+1)-eigenfunction, vanishes at
    0 and is > 0 for |x| > sqrt(3/(2 pi)) = 0.69099; so <M, f_plus> > 0, forcing eps = +1.
  * h_2 = (8 pi x^2 - 2) e^{-pi x^2} is a (-1)-eigenfunction; with eps = +1 the pairing
    vanishes: c0 = sum_nu w_nu (8 pi nu^2 - 2) e^{-pi nu^2}.  For zeta (M = Dirac comb, c0 = 1)
    this is the theta identity sum_{n>=1} (8 pi n^2 - 2) e^{-pi n^2} = 1, which follows from
    differentiating theta(1/t) = sqrt(t) theta(t) at t = 1.

This script: (1) encloses the theta sum in Arb with an explicit tail bound; (2) checks the
eigen-relations by mpmath quadrature at sample frequencies; (3) checks the positivity
threshold of f_plus and the sign of <Dirac comb, f_plus>.
"""
from __future__ import annotations

import json
import os

import mpmath as mp
from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))


def theta_identity_arb(N: int = 12, prec: int = 256) -> dict:
    ctx.prec = prec
    pi = arb.pi()
    s = arb(0)
    for n in range(1, N + 1):
        s += (8 * pi * n * n - 2) * (-pi * n * n).exp()
    # tail: for n >= N+1 >= 2, (8 pi n^2 - 2) e^{-pi n^2} <= 8 pi n^2 e^{-pi n^2}
    #   <= 8 pi e^{-pi n^2 / 2}  (since n^2 <= e^{pi n^2 / 2}),
    # and sum_{n >= N+1} e^{-pi n^2/2} <= e^{-pi (N+1)^2 / 2} / (1 - e^{-pi (N+1)}).
    M = N + 1
    tail = 8 * pi * (-(pi * M * M) / 2).exp() / (1 - (-(pi * M)).exp())
    # every tail term is positive, so the full sum lies in [s, s + tail]
    s_enclosure = s.union(s + tail)
    return {"N": N, "partial_sum": str(s), "tail_upper_bound": str(tail),
            "enclosure_of_full_sum": str(s_enclosure),
            "contains_1": bool(s_enclosure.contains(1)),
            "width": str(s_enclosure.rad())}


def eigen_checks() -> list:
    mp.mp.dps = 30

    def h(n, x):
        y = mp.sqrt(2 * mp.pi) * x
        return mp.hermite(n, y) * mp.exp(-mp.pi * x * x)

    def ft(f, xi):
        re = mp.quad(lambda x: f(x) * mp.cos(2 * mp.pi * x * xi), [-mp.inf, 0, mp.inf])
        im = -mp.quad(lambda x: f(x) * mp.sin(2 * mp.pi * x * xi), [-mp.inf, 0, mp.inf])
        return mp.mpc(re, im)

    fplus = lambda x: h(4, x) - 12 * h(0, x)
    h2 = lambda x: h(2, x)
    rows = []
    for xi in (mp.mpf("0.3"), mp.mpf("0.9"), mp.mpf("1.7")):
        rows.append({"xi": float(xi),
                     "|f_plus^(xi) - f_plus(xi)|": mp.nstr(abs(ft(fplus, xi) - fplus(xi)), 5),
                     "|h2^(xi) + h2(xi)|": mp.nstr(abs(ft(h2, xi) + h2(xi)), 5)})
    return rows


def main() -> None:
    out = {"conjecture1_proved": False}
    out["theta_identity_arb"] = theta_identity_arb()
    out["hermite_eigen_quadrature"] = eigen_checks()
    mp.mp.dps = 30
    thr = mp.sqrt(3 / (2 * mp.pi))
    out["f_plus_positivity_threshold sqrt(3/(2pi))"] = mp.nstr(thr, 12)
    fplus = lambda x: 16 * (2 * mp.pi * x * x) * (2 * mp.pi * x * x - 3) * mp.exp(-mp.pi * x * x)
    comb = 2 * mp.nsum(lambda n: fplus(n), [1, mp.inf])
    out["<Dirac comb, f_plus>"] = mp.nstr(comb, 20)
    out["<Dirac comb, f_plus> > 0"] = bool(comb > 0)
    with open(os.path.join(HERE, "hermite_theta_check.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
