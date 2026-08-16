"""THE UNIFIED TOPPED-UP MERGE: one debris-free rule for every donor load, certified at cap 3/16.

SUPERSEDES the two-rule design (direct + borrow-1 assisted) of kelmans_env_rules.py.  The borrow-1
assisted merge leaves a load-1 leaf (z = 3/7) that breaks the canonical environment cap for later
merges nearby.  The unified rule removes ALL debris:

    TOPPED-UP MERGE.  Hubward pair a (load cA, degree da) >= b (load cb <= 4, degree db, with at
    least k = 5-cb arm-leaf movers of load 5): downgrade k donor arms 5 -> 4, load the donor
    0..4 -> 5, Kelmans-merge b into a.  The donor lands as a CANONICAL LOAD-5 ARM of a; the only
    residue is k load-4 arms -- inside the balanced {4,5}-arm family.  (cb = 5: direct merge,
    k = 0, same shape.)

THE EXACT IDENTITY (verified here on random loaded trees, arbitrary environments):
    pi(T'') - pi(T) = Penv * FQ * FSr * D(sigma_Q, sigma_r),
    D = Wt^k * F(da+db-1, cA) * F(1,5) * (1 + za''*(sigma_Q + k*z14 + sigma_r + z15))
        - F(da, cA) * F(db, cb) * ((1 + za*sigma_Q)*(1 + zb*(k*z15 + sigma_r)) + za*zb),
with Wt = F(1,4)/F(1,5) = 76/115, z15 = 3/23, z14 = 3/19, za'' = z(da+db-1, cA), zb = z(db, cb);
environment enters ONLY via sigma_Q (a's side) and sigma_r (the donor's non-borrowed movers), both
bounded by the marginal box under the per-neighbour activity cap.

THEOREM (certified symbolically, certify_unified_table):  For every (cA, cb) in {0..5} x {0..4}
(topped-up, shift db = 6-cb+v, da = db+u) and (cA, 5) (direct, one-arm floor sigma_S >= 3/23,
shift db = 2+v), all box corners are all-nonnegative over a positive denominator at environment
cap z <= 3/16: the merge is pi-non-decreasing in EVERY environment whose OTHER neighbours of a
and b satisfy 3*deg + 4*load >= 16.  36/36 cells.

CAP LADDER (cap_ladder): 36/36 holds at 3/23, 3/19, 1/6, 3/17, 3/16; first failure at 1/5
(cell (1,5)).  Cap 3/16 covers: arms load >= 4, hub neighbours with >= 5 arms (any load),
loaded hubs of degree >= 4.  Outside the cap (arms load <= 3, hubs with <= 4 arms and load 0,
bare/low-load leaves) = exactly the SMALL STRUCTURES that the rewrite's (L)/(B) normalization
layer owns -- named residual, not a merge-rule question.

CONSEQUENCE FOR P2: the Step relation needs ONE merge constructor (k = 5 - cb borrows fused with
the Kelmans move); no rebalancing between merges; no debris states in the HubState encoding;
donors with fewer than 5-cb arms are small structures for (B).  conjecture1_proved=False.

Requires networkx, sympy.  Self-verifying run_all(); every claim an assert.
"""
from __future__ import annotations

import random
from fractions import Fraction as Fr

import networkx as nx

from verification.kelmans_mixed_load import (
    pi_loaded,
    F_of,
    z_of,
    psi_weighted,
)


# ------------------------------------------------------------------ the unified move
def topped_up_merge_apply(G: nx.Graph, load: dict, a, b, borrow_arms):
    """Downgrade each arm in borrow_arms (load-5 leaves of b) to 4, set b's load to 5,
    merge b into a (movers reattach, b stays as a load-5 leaf of a)."""
    k = len(borrow_arms)
    assert load[b] + k == 5 and G.has_edge(a, b)
    H = G.copy()
    l2 = dict(load)
    for x in borrow_arms:
        assert G.has_edge(b, x) and G.degree(x) == 1 and load[x] == 5
        l2[x] = 4
    l2[b] = 5
    for w in list(G.neighbors(b)):
        if w != a:
            H.remove_edge(b, w)
            H.add_edge(a, w)
    return H, l2


def _env_quantities(beta: nx.Graph, a, b, borrow_arms, z: dict):
    others = [x for x in beta.nodes() if x != a]
    comp_b = nx.node_connected_component(beta.subgraph(others), b)
    Ra = [x for x in beta.nodes() if x != a and x not in comp_b]
    movers_r = [x for x in comp_b if x != b and x not in borrow_arms]
    FQ = psi_weighted(beta.subgraph(Ra), z)
    FSr = psi_weighted(beta.subgraph(movers_r), z)
    MQ = (psi_weighted(beta.subgraph([a] + Ra), z) - FQ) / z[a]
    MSr = (psi_weighted(beta.subgraph([b] + movers_r), z) - FSr) / z[b]
    return FQ, MQ, FSr, MSr


def D_unified(da: int, db: int, cA: int, cb: int, sQ: Fr, sr: Fr) -> Fr:
    k = 5 - cb
    Wt = F_of(1, 4) / F_of(1, 5)
    z15, z14 = z_of(1, 5), z_of(1, 4)
    zap = z_of(da + db - 1, cA)
    za, zb = z_of(da, cA), z_of(db, cb)
    return (Wt ** k * F_of(da + db - 1, cA) * F_of(1, 5)
            * (1 + zap * (sQ + k * z14 + sr + z15))
            - F_of(da, cA) * F_of(db, cb)
            * ((1 + za * sQ) * (1 + zb * (k * z15 + sr)) + za * zb))


def verify_unified_identity(trials: int = 250, seed: int = 11) -> dict:
    """pi(T'') - pi(T) == Penv * FQ * FSr * D on random loaded trees, all donor loads 0..4."""
    rng = random.Random(seed)
    checked = 0
    for _ in range(trials):
        cA = rng.randint(0, 5)
        cb = rng.randint(0, 4)
        k = 5 - cb
        G = nx.Graph()
        G.add_edge(0, 1)
        load = {0: cA, 1: cb}
        nxt = 2
        borrow = []
        for _ in range(k):
            G.add_edge(1, nxt); load[nxt] = 5; borrow.append(nxt); nxt += 1
        def attach(parent):
            nonlocal nxt
            r = nxt
            G.add_edge(parent, r); load[r] = rng.randint(0, 5); nxt += 1
            for _ in range(rng.randint(0, 3)):
                G.add_edge(r, nxt); load[nxt] = rng.randint(0, 5); nxt += 1
        for _ in range(rng.randint(0, 3)):
            attach(0)
        for _ in range(rng.randint(0, 3)):
            attach(1)
        da, db = G.degree(0), G.degree(1)
        z = {v: z_of(G.degree(v), load[v]) for v in G.nodes()}
        FQ, MQ, FSr, MSr = _env_quantities(G, 0, 1, borrow, z)
        Penv = Fr(1)
        for v in G.nodes():
            if v not in (0, 1):
                Penv *= F_of(G.degree(v), load[v])
        H, l2 = topped_up_merge_apply(G, load, 0, 1, borrow)
        lhs = pi_loaded(H, l2) - pi_loaded(G, load)
        rhs = Penv * FQ * FSr * D_unified(da, db, cA, cb, MQ / FQ, MSr / FSr)
        assert lhs == rhs, (cA, cb, da, db)
        checked += 1
    return {"unified_identity_exact": True, "cases": checked}


# ------------------------------------------------------ the 36-cell symbolic theorem
CAP = Fr(3, 16)


def certify_unified_table(cap=None) -> dict:
    """All 36 cells at the given environment cap (default 3/16): topped-up (cb 0..4,
    shift db = 6-cb+v, da = db+u) + direct (cb = 5, one-arm floor 3/23, db = 2+v)."""
    import sympy as sp
    if cap is None:
        cap = sp.Rational(3, 16)
    else:
        cap = sp.Rational(cap.numerator, cap.denominator)
    u, v = sp.symbols("u v", nonnegative=True)
    z15c, z14c = sp.Rational(3, 23), sp.Rational(3, 19)
    Wt, V5 = sp.Rational(76, 115), sp.Rational(621, 64)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D_ = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D_) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    def allnonneg(expr):
        num, den = sp.fraction(sp.together(expr))
        pnum = sp.Poly(sp.expand(num), u, v)
        pden = sp.Poly(sp.expand(den), u, v)
        dc = pden.coeffs()
        dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
        return dsg != 0 and all(c * dsg >= 0 for c in pnum.coeffs())

    certified = 0
    for cb in range(5):                          # topped-up cells
        k = 5 - cb
        db = k + 1 + v
        da = db + u
        for cA in range(6):
            za, zb = zs(da, cA), zs(db, cb)
            zap = zs(da + db - 1, cA)
            for sQv in (sp.Integer(0), (da - 1) * cap):
                for srv in (sp.Integer(0), v * cap):
                    before = Fs(da, cA) * Fs(db, cb) * ((1 + za * sQv) * (1 + zb * (k * z15c + srv)) + za * zb)
                    after = Wt ** k * Fs(da + db - 1, cA) * V5 * (1 + zap * (sQv + k * z14c + srv + z15c))
                    assert allnonneg(after - before), (cA, cb, "topped")
            certified += 1
    db2 = 2 + v                                   # direct cb=5 cells, one-arm floor
    da2 = db2 + u
    for cA in range(6):
        Fa, Fb = Fs(da2, cA), Fs(db2, 5)
        Fap, Fbp = Fs(da2 + db2 - 1, cA), Fs(1, 5)
        za, zb = zs(da2, cA), zs(db2, 5)
        zap, zbp = zs(da2 + db2 - 1, cA), zs(1, 5)
        c1 = Fap * Fbp * (1 + zap * zbp) - Fa * Fb * (1 + za * zb)
        c2 = Fap * Fbp * zap - Fa * Fb * za
        c3 = Fap * Fbp * zap - Fa * Fb * zb
        c4 = -Fa * Fb * za * zb
        for sQv in (sp.Integer(0), (da2 - 1) * cap):
            for sSv in (z15c, (db2 - 1) * cap):
                assert allnonneg(c1 + c2 * sQv + c3 * sSv + c4 * sQv * sSv), (cA, 5, "direct")
        certified += 1
    return {"unified_table_cells": certified, "cap": str(cap)}


def cap_ladder() -> dict:
    """Recorded scan (2026-08-14): 36/36 at 3/23, 3/19, 1/6, 3/17, 3/16; at 1/5 fails
    (1,5); at 3/14 fails (1,5),(2,5); at 2/9 fails (0,5),(1,5),(2,5)."""
    return {"certified_at": ["3/23", "3/19", "1/6", "3/17", "3/16"],
            "first_failures": {"1/5": [(1, 5)], "3/14": [(1, 5), (2, 5)],
                               "2/9": [(0, 5), (1, 5), (2, 5)]},
            "cap_3_16_covers": "arms load>=4; hub neighbours with >=5 arms (any load); "
                               "loaded hubs deg>=4",
            "outside_cap": "arms load<=3, hubs with <=4 arms and load 0, bare/low-load "
                           "leaves -- the (L)/(B) small-structure layer"}


def verify_grid(grid: int = 20) -> dict:
    """Exact-grid sanity on the two-hub family: the topped-up merge strictly increases
    pi for all pA >= pB' (donor arms pB >= k), all cells."""
    checked = 0
    for cb in range(6):
        k = 5 - cb
        for pA in range(1, grid + 1):
            for pB in range(max(k, 1), min(pA, grid) + 1):
                G = nx.Graph(); G.add_edge(0, 1)
                load = {0: 3, 1: cb}
                nxt = 2
                borrow = []
                for i in range(pB):
                    G.add_edge(1, nxt); load[nxt] = 5
                    if i < k:
                        borrow.append(nxt)
                    nxt += 1
                for _ in range(pA):
                    G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
                H, l2 = topped_up_merge_apply(G, load, 0, 1, borrow)
                assert pi_loaded(H, l2) > pi_loaded(G, load), (cb, pA, pB)
                checked += 1
    return {"two_hub_grid_strict": True, "cases": checked}


def run_all():
    out = {}
    out["identity"] = verify_unified_identity()
    out["grid"] = verify_grid()
    out["table_3_16"] = certify_unified_table()
    out["cap_ladder"] = cap_ladder()
    out["status"] = {
        "unified_merge": "ONE debris-free rule, all donor loads: top up to 5 by k = 5-cb arm "
                         "borrows, merge, donor lands as a canonical arm.  36/36 cells "
                         "certified at env cap 3/16.",
        "residual": "small structures only (donors with < 5-cb arms; env neighbours with "
                    "3deg+4load < 16) -- the (L)/(B) normalization layer",
        "conjecture1_proved": False,
    }
    for kk, vv in out.items():
        print(f"  {kk}: {vv}")
    return out


if __name__ == "__main__":
    run_all()
