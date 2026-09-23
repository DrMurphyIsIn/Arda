"""Negative control F(s) = zeta(s) (1 + 4*2^{-s} + 2*4^{-s}): exact and numerical cross-checks.

conjecture1_proved = False.  The load-bearing facts are kernel-checked in
examples/li_positivity/lean/Crux/Crux_axiso_literature.lean (section A).  This script adds:

  1. exact von Mangoldt coefficients Lambda_F(n), n <= N, solving Lambda_F * a = a . log with
     logs as integer vectors over the primes (no floating point), checked against the closed
     form: Lambda_F(p^k) = log p for odd p, Lambda_F(2^k) = (1 - p_k) log 2 with
     p_k = (-2+sqrt2)^k + (-2-sqrt2)^k (Newton recursion p_k = -4 p_{k-1} - 2 p_{k-2}),
     and Lambda_F(n) = 0 off prime powers.  Lambda_F(4^j) < 0 for every j >= 1;
  2. the growth |Lambda_F(2^k)| ~ (2+sqrt2)^k log 2, i.e. Lambda_F(n) is of size
     n^{log_2(2+sqrt2)} = n^{1.7716} on powers of 2: Selberg's axiom (theta < 1/2) fails
     while the coefficients a(n) are bounded (Ramanujan holds);
  3. mpmath (40 digits) evaluation of F at s_0 = log_2(2+sqrt2) + i pi/log 2 and of the
     functional-equation residual (4/pi)^{s/2} Gamma(s/2) F(s) - (same at 1 - s).
"""
from __future__ import annotations

import json
import os

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))


def coef(n: int) -> int:
    return 1 + (4 if n % 2 == 0 else 0) + (2 if n % 4 == 0 else 0)


def exact_vonmangoldt(N: int):
    spf = list(range(N + 1))
    for p in range(2, int(N ** 0.5) + 1):
        if spf[p] == p:
            for m in range(p * p, N + 1, p):
                if spf[m] == m:
                    spf[m] = p

    def logvec(n):
        v = {}
        while n > 1:
            p = spf[n]
            v[p] = v.get(p, 0) + 1
            n //= p
        return v

    divs = [[] for _ in range(N + 1)]
    for d in range(2, N + 1):
        for m in range(2 * d, N + 1, d):
            divs[m].append(d)
    L = [dict() for _ in range(N + 1)]
    for n in range(2, N + 1):
        acc = {p: coef(n) * e for p, e in logvec(n).items()}
        for d in divs[n]:
            for p, e in L[d].items():
                acc[p] = acc.get(p, 0) - e * coef(n // d)
        L[n] = {p: e for p, e in acc.items() if e != 0}
    return L, logvec


def main() -> None:
    out = {"conjecture1_proved": False, "object": "F(s) = zeta(s)(1 + 4*2^{-s} + 2*4^{-s})"}
    N = 1 << 12
    L, logvec = exact_vonmangoldt(N)
    # closed form on powers of 2
    pk = [2, -4]
    for k in range(2, 13):
        pk.append(-4 * pk[-1] - 2 * pk[-2])
    mism = []
    for n in range(2, N + 1):
        lv = logvec(n)
        if len(lv) == 1:
            p = next(iter(lv))
            k = lv[p]
            exp = {2: 1 - pk[k]} if p == 2 else {p: 1}
        else:
            exp = {}
        if L[n] != exp:
            mism.append(n)
    out["closed_form_mismatches_n_le_4096"] = mism
    table = []
    for k in range(1, 13):
        v = L[2 ** k].get(2, 0)
        table.append({"k": k, "n": 2 ** k, "Lambda_F(2^k)/log2": v,
                      "sign": "negative" if v < 0 else "positive",
                      "growth_exponent log|v|/log(2^k)":
                          float(mp.log(abs(v)) / (k * mp.log(2))) if v else None})
    out["Lambda_F_on_powers_of_2"] = table
    out["negative_indices_n_le_4096"] = [n for n in range(2, N + 1) if L[n].get(2, 0) < 0]
    out["limit_exponent log_2(2+sqrt2)"] = float(mp.log(2 + mp.sqrt(2), 2))

    # mpmath checks
    mp.mp.dps = 40
    s0 = mp.log(2 + mp.sqrt(2)) / mp.log(2) + 1j * mp.pi / mp.log(2)

    def P(s):
        return 1 + 4 * mp.power(2, -s) + 2 * mp.power(4, -s)

    def F(s):
        return mp.zeta(s) * P(s)

    def LamF(s):
        return mp.power(4 / mp.pi, s / 2) * mp.gamma(s / 2) * F(s)

    out["s0"] = mp.nstr(s0, 25)
    out["2^{-s0}"] = mp.nstr(mp.power(2, -s0), 25)
    out["-1+sqrt2/2"] = mp.nstr(-1 + mp.sqrt(2) / 2, 25)
    out["|F(s0)|"] = mp.nstr(abs(F(s0)), 5)
    out["|zeta(s0)|"] = mp.nstr(abs(mp.zeta(s0)), 20)
    out["|Lambda_F(1-s0)|"] = mp.nstr(abs(LamF(1 - s0)), 5)
    fe = []
    for s in [mp.mpc(0.3, 2.0), mp.mpc(2.5, -7.0), mp.mpc(-0.7, 13.0)]:
        fe.append({"s": mp.nstr(s, 6), "|Lambda_F(s) - Lambda_F(1-s)|": mp.nstr(abs(LamF(s) - LamF(1 - s)), 5),
                   "|Lambda_F(s)|": mp.nstr(abs(LamF(s)), 8)})
    out["functional_equation_residuals"] = fe
    # Dirichlet series sanity at s = 3: direct partial sum to M plus the tail bound 7/(2 M^2)
    import math
    M = 200000
    part = math.fsum(coef(n) / n ** 3 for n in range(1, M + 1))
    out["dirichlet_series_at_3"] = {
        "partial_sum_to_M": repr(part), "M": M, "tail_bound": 7 / (2 * M * M),
        "F(3)": mp.nstr(F(3), 20),
        "|partial - F(3)|": abs(part - float(F(3))),
        "consistent": abs(part - float(F(3))) <= 7 / (2 * M * M) + 1e-13}

    with open(os.path.join(HERE, "neg_control_check.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print("mismatches:", mism[:10])
    for r in table[:8]:
        print(r)
    print("|F(s0)| =", out["|F(s0)|"], " |zeta(s0)| =", out["|zeta(s0)|"])
    print("FE residuals:", [r["|Lambda_F(s) - Lambda_F(1-s)|"] for r in fe])
    print("dirichlet series check:", out["dirichlet_series_at_3"])


if __name__ == "__main__":
    main()
