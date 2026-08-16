"""G34-MULTI: the star-of-hubs defected stuck configurations are dominated -- symbolic in the
sizes, concrete in the hub count.

The multi-hub (H >= 3) residual's archetypes are the DEPTH-2 hub trees (stars of hubs), because
blocking every merge needs a vertex cover of defected hubs and the star's cover is cheapest
(one defected top -- or every sub-hub defected).  Deeper trees need spine covers and pay more
ledger per blocked edge, and their towers decay hard (amortized_hub_bound).  This module proves
the depth-2 archetypes dominated:

  CONFIG (top-defected):  top (load cT, pT arms(5), j defects) + S sub-hubs (load cB, q arms(5)).
  CONFIG (subs-defected): top clean + each sub-hub carrying one defect.

  CLOSED FORM (exact; verified against pi_loaded):
    Psi = prod_i subOpen_i * [1 + z_top*(sigma_top + SUM_i z_i/subOpen_i)],
  the depth-2 matching sum factors over sub-hubs.

  THEOREM (certify_symbolic): for every S in 2..10, cT in 0..5, cB in {0,5}, defect type in
  {leaf, arm1, arm2} with budget-bounded counts, the config is strictly below a same-n
  single-hub comparator for ALL (pT >= 0, q >= 1) -- symbolic all-nonneg certificates in
  (pT, q) with PER-RESIDUE COMPARATOR SEARCH (the winning template varies with n mod 11,
  as in the two-hub discharge).

  Plus an exact-rational ASYMMETRIC SWEEP (unequal sub-hub sizes, sampled grids).

HONEST SCOPE: depth >= 3 hub trees, mixed defect placements, and asymmetric tails beyond the
sweep remain probe-backed ("G34-deep": towers + ledger arguments; margins grow with depth and
hub count -- worst observed ratio in ALL multi-hub probes is 1.09+, vs 1.018 for two hubs).
conjecture1_proved=False.  Self-verifying run_all().
"""
from __future__ import annotations

import functools
from fractions import Fraction as Fr

import sympy as sp

from verification.kelmans_mixed_load import F_of, z_of

z15f = z_of(1, 5)
DEFECTS = {"leaf": (0, 2), "arm1": (1, 9), "arm2": (2, 13)}   # load, budget jmax (top variant)


# ------------------------------------------------------------- exact closed forms
def pi_star_top_defected(pT, j, dload, cT, S, q, cB) -> Fr:
    zD, FD = z_of(1, dload), F_of(1, dload)
    dt = pT + j + S
    zt = z_of(dt, cT)
    zi = z_of(q + 1, cB)
    sub_open = 1 + zi * q * z15f
    psi = sub_open ** S * (1 + zt * (pT * z15f + j * zD + S * (zi / sub_open)))
    return (F_of(dt, cT) * FD ** j * F_of(1, 5) ** (pT + S * q)
            * F_of(q + 1, cB) ** S * psi)


def pi_star_subs_defected(pT, dload, cT, S, q, cB) -> Fr:
    zD, FD = z_of(1, dload), F_of(1, dload)
    dt = pT + S
    zt = z_of(dt, cT)
    zi = z_of(q + 2, cB)                       # each sub-hub: q arms + 1 defect + top edge
    sub_open = 1 + zi * (q * z15f + zD)
    psi = sub_open ** S * (1 + zt * (pT * z15f + S * (zi / sub_open)))
    return (F_of(dt, cT) * FD ** S * F_of(1, 5) ** (pT + S * q)
            * F_of(q + 2, cB) ** S * psi)


def verify_closed_forms() -> dict:
    import networkx as nx
    from verification.kelmans_mixed_load import pi_loaded
    checked = 0
    for (pT, j, dload, cT, S, q, cB) in ((3, 1, 0, 0, 2, 4, 0), (5, 2, 1, 3, 3, 6, 5),
                                         (2, 1, 2, 5, 4, 3, 0), (0, 1, 0, 0, 2, 5, 5)):
        G = nx.Graph(); load = {0: cT}; nxt = 1
        for _ in range(pT):
            G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
        for _ in range(j):
            G.add_edge(0, nxt); load[nxt] = dload; nxt += 1
        for _ in range(S):
            h = nxt; G.add_edge(0, h); load[h] = cB; nxt += 1
            for _ in range(q):
                G.add_edge(h, nxt); load[nxt] = 5; nxt += 1
        assert pi_star_top_defected(pT, j, dload, cT, S, q, cB) == pi_loaded(G, load)
        checked += 1
    for (pT, dload, cT, S, q, cB) in ((3, 0, 0, 2, 4, 0), (2, 1, 5, 3, 3, 0), (0, 2, 2, 2, 6, 5)):
        G = nx.Graph(); load = {0: cT}; nxt = 1
        for _ in range(pT):
            G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
        for _ in range(S):
            h = nxt; G.add_edge(0, h); load[h] = cB; nxt += 1
            for _ in range(q):
                G.add_edge(h, nxt); load[nxt] = 5; nxt += 1
            G.add_edge(h, nxt); load[nxt] = dload; nxt += 1
        assert pi_star_subs_defected(pT, dload, cT, S, q, cB) == pi_loaded(G, load)
        checked += 1
    return {"closed_forms_exact": checked}


# ------------------------------------------------------ the symbolic certificates
def _sym_star(variant, S, cT, cB, dload, j):
    """symbolic config/V5^(arm count) and its n-constant, in (x=pT, y=q-1)."""
    x, y = sp.symbols("x y", nonnegative=True)
    pT = x
    q = 1 + y
    V5 = sp.Rational(621, 64)
    z15 = sp.Rational(3, 23)
    zDl = sp.Rational(z_of(1, dload).numerator, z_of(1, dload).denominator)
    FDl = sp.Rational(F_of(1, dload).numerator, F_of(1, dload).denominator)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    if variant == "top":
        dt = pT + j + S
        zt = zs(dt, cT)
        zi = zs(q + 1, cB)
        sub_open = 1 + zi * q * z15
        cfg = (Fs(dt, cT) * FDl ** j * Fs(q + 1, cB) ** S
               * sub_open ** S * (1 + zt * (pT * z15 + j * zDl + S * zi / sub_open)))
        # arm count pT + S*q; n = 1 + 2cT + 11pT + j*(1+2*dload) + S*(1+2*cB) + 11*S*q
        n_lin = (11, 11 * S)                # coefficients of (pT, q) in n... q coeff = 11S
        n_const = 1 + 2 * cT + j * (1 + 2 * dload) + S * (1 + 2 * cB)
    else:
        dt = pT + S
        zt = zs(dt, cT)
        zi = zs(q + 2, cB)
        sub_open = 1 + zi * (q * z15 + zDl)
        cfg = (Fs(dt, cT) * FDl ** S * Fs(q + 2, cB) ** S
               * sub_open ** S * (1 + zt * (pT * z15 + S * zi / sub_open)))
        n_const = 1 + 2 * cT + S * (1 + 2 * cB) + S * (1 + 2 * dload)
    return x, y, pT, q, cfg, n_const


def certify_symbolic(S_range=range(2, 11)) -> dict:
    """Both variants, S concrete, symbolic in (pT >= 0, q >= 1), per-residue comparators."""
    V5 = sp.Rational(621, 64)
    W4 = sp.Rational(513, 80)
    z15 = sp.Rational(3, 23)
    z14 = sp.Rational(3, 19)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    certified = 0
    hard = []
    for variant in ("top", "subs"):
        for S in S_range:
            for cT in range(6):
                for cB in (0, 5):
                    for name, (dload, jmax) in DEFECTS.items():
                        js = ([1, jmax] if variant == "top" else [None])
                        for j in js:
                            jv = j if j is not None else S
                            x, y, pT, q, cfg, n_const = _sym_star(
                                variant, S, cT, cB, dload, j if j is not None else 0)

                            def allnn(expr):
                                num, den = sp.fraction(sp.together(expr))
                                pnum = sp.Poly(sp.expand(num), x, y)
                                pden = sp.Poly(sp.expand(den), x, y)
                                dc = pden.coeffs()
                                dsg = 1 if all(c > 0 for c in dc) else (
                                    -1 if all(c < 0 for c in dc) else 0)
                                nc = [c * dsg for c in pnum.coeffs()]
                                return dsg != 0 and all(c >= 0 for c in nc) and any(c > 0 for c in nc)

                            # comparator: K = pT + S*q + Kc arms; n-residue fixes (c0,m4,nleaf)
                            found = False
                            for c0 in range(0, 7):
                                for m4 in range(0, 11):
                                    for nleaf in (0, 1):
                                        if found:
                                            continue
                                        rem = n_const - 1 - 2 * c0 + 2 * m4 - nleaf
                                        if rem % 11:
                                            continue
                                        Kc = rem // 11
                                        K = pT + S * q + Kc
                                        dT = K + nleaf
                                        zT = sp.Integer(3) / (3 * dT + 4 * c0)
                                        sig = (K - m4) * z15 + m4 * z14 + nleaf
                                        tmpl = (Fs(dT, c0) * (W4 / V5) ** m4 * V5 ** Kc
                                                * (1 + zT * sig))
                                        # both sides normalized by V5^(pT + S*q)
                                        if allnn(tmpl - cfg):
                                            found = True
                            if found:
                                certified += 1
                            else:
                                hard.append((variant, S, cT, cB, name, j))
    return {"certified": certified, "hard_cases": hard}


def sweep_asymmetric(nmax_hint: int = 0) -> dict:
    """Exact sweep: unequal sub-hub sizes (H = 3..5), top-defected, vs searched comparator."""
    import itertools

    @functools.lru_cache(maxsize=None)
    def best_template(n):
        best = None
        for c0 in range(0, 7):
            for nleaf in (0, 1, 2):
                rem = n - 1 - 2 * c0 - nleaf
                if rem <= 0:
                    continue
                for K in range(max(1, rem // 13), rem // 9 + 2):
                    t2 = rem - K
                    if t2 < 0 or t2 % 2:
                        continue
                    tot = t2 // 2
                    if tot > 8 * K:
                        continue
                    b, r = divmod(tot, K)
                    loads = [b + 1] * r + [b] * (K - r)
                    zh = z_of(K + nleaf, c0)
                    p = F_of(K + nleaf, c0)
                    s = Fr(0)
                    for c in loads:
                        p *= F_of(1, c)
                        s += z_of(1, c)
                    s += nleaf
                    p *= (1 + zh * s)
                    if best is None or p > best:
                        best = p
        return best

    def pi_asym(pT, j, dload, cT, qs):
        zD, FD = z_of(1, dload), F_of(1, dload)
        S = len(qs)
        dt = pT + j + S
        zt = z_of(dt, cT)
        psi_extra = Fr(0)
        fprod = F_of(dt, cT) * FD ** j * F_of(1, 5) ** (pT + sum(qs))
        prod_open = Fr(1)
        for qq in qs:
            zi = z_of(qq + 1, 0)
            so = 1 + zi * qq * z15f
            prod_open *= so
            psi_extra += zi / so
            fprod *= F_of(qq + 1, 0)
        psi = prod_open * (1 + zt * (pT * z15f + j * zD + psi_extra))
        return fprod * psi

    checked = 0
    for Ssz in (2, 3, 4):
        for qs in itertools.combinations_with_replacement((1, 3, 6, 10, 16), Ssz):
            if len(set(qs)) == 1:
                continue                        # symmetric covered symbolically
            for pT in (0, 2, 6):
                for cT in (0, 5):
                    for (j, dload) in ((1, 0), (2, 0), (1, 1), (2, 2)):
                        cfg = pi_asym(pT, j, dload, cT, qs)
                        n = 1 + 2 * cT + 11 * pT + j * (1 + 2 * dload) + sum(1 + 11 * qq for qq in qs)
                        assert best_template(n) > cfg, (Ssz, qs, pT, cT, j, dload)
                        checked += 1
    return {"asymmetric_sweep_exact": True, "cases": checked}


def run_all():
    out = {}
    out["closed_forms"] = verify_closed_forms()
    out["symbolic"] = certify_symbolic()
    out["asymmetric"] = sweep_asymmetric()
    hard = out["symbolic"]["hard_cases"]
    out["status"] = {
        "star_of_hubs": f"symbolic certificates: {out['symbolic']['certified']} cases green"
                        + (f"; {len(hard)} hard cases -> sweep/named" if hard else "; NO hard cases"),
        "remaining": "G34-deep: depth >= 3 hub trees + mixed placements + asymmetric tails "
                     "(probe-backed, margins grow with depth/count)",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
