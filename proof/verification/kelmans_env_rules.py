"""ENVIRONMENT versions of the merge rules: the assisted merge in an arbitrary loaded-backbone
environment, and the settlement of the residual direct-merge cells.

CONTEXT.  kelmans_mixed_load.py gave the DIRECT hubward merge its environment theorem (box corners:
25/30 loaded-donor cells, any environment with per-neighbour 3*deg+4*load >= 23).  kelmans_vertex_budget.py
proved the ASSISTED merge (borrow one cherry from a donor arm, then merge) on the exact two-hub family,
dissolving stuck configurations there.  This module lifts the assisted merge to ARBITRARY environments
and probes the 5 residual direct-merge cells in the donor shape the box actually fears.

THE COMPOSED EXACT IDENTITY (verified here on assorted loaded trees).  Let a (load cA, degree da) be
adjacent to the de-loaded donor b (load 0, degree db >= 2) whose movers are one explicit ARM-LEAF
arm0 (load 5) plus a forest S_rest (db-2 subtrees); let Q be a's environment forest.  The assisted
merge (arm0 5->4, b 0->1, then all movers to a, b left as a load-1 leaf on a) satisfies

    pi(T'') - pi(T) = Penv * FQ * FSr * D(sigma_Q, sigma_r),

    D = Wt * F(da+db-1, cA) * F(1,1) * (1 + za''*(sigma_Q + sigma_r + z14 + z11))
        - F(da, cA) * ((1 + za*sigma_Q)*(1 + zb*(sigma_r + z15)) + za*zb),

with Wt = F(1,4)/F(1,5) = 76/115, za'' = z(da+db-1, cA), za = z(da, cA), zb = 1/db,
z15 = 3/23, z14 = 3/19, z11 = 3/7, Penv = prod of untouched F's, and the environment entering ONLY
through sigma_Q = MQ/FQ and sigma_r = MSr/FSr.  D is BILINEAR in (sigma_Q, sigma_r), so its minimum
over the marginal box  sigma_Q in [0, (da-1)*z1], sigma_r in [0, (db-2)*z1]  (z1 = 3/23; valid when
every Q-root and S_rest-root has 3*deg + 4*load >= 23 and cavity ratio <= 1, psi_close piece (2))
is attained at a corner.

THEOREM (ASSISTED MERGE IN ENVIRONMENT, certified here symbolically).  For hubward da >= db >= 2,
receiver load cA in {0..5}, de-loaded donor with at least one arm-leaf mover, and every OTHER
neighbour of a and b satisfying 3*deg + 4*load >= 23: all four corners of D are >= 0 after the shift
da = db + u, db = 2 + v -- so the assisted merge is pi-non-decreasing in EVERY such environment.

THEOREM (RESIDUAL CELLS CLOSED -- the ONE-ARM FLOOR).  The 5 direct-merge cells the plain box
could not certify ({(0,5),(1,4),(1,5),(2,5),(3,5)}) fail only at the sigma_S = 0 corner -- which is
UNREALIZABLE when the donor carries at least one arm-leaf mover (that arm alone contributes
z(1,5)*1 = 3/23 to sigma_S, exactly).  Over the floored box sigma_S in [3/23, (db-1)*3/23] all four
corners certify all-nonneg for all hubward (da, db) (certify_residual_one_arm_floor).  [This also
explains the earlier sub-box failure: a (db-2)*z1 floor DEGENERATES to 0 at db = 2, resurrecting
the bad corner; the constant one-arm floor does not.]  So with the same natural hypothesis as the
assisted merge -- donor has >= 1 arm -- the direct merge is certified on ALL 30 loaded-donor cells.

THE COMPLETE IN-ENVIRONMENT MERGE TABLE (canonical environments, z-cap 3/23):
    hubward da >= db >= 2, every other neighbour of a and b with 3*deg + 4*load >= 23,
    donor carrying >= 1 arm-leaf mover:
      donor load 1..5  ->  DIRECT merge,   pi-non-decreasing   (30/30 cells)
      donor load 0     ->  ASSISTED merge, pi-non-decreasing   (all 6 receiver cells)
    anti-hubward -> reverse the roles.
CAP ROBUSTNESS (cap_robustness_report): the table is EXACT at the canonical cap 3/23 (all-load-5-arm
environments); at 3/19 (load-4 arms present) direct survives 29/30 (only (5,1) fails) but the
assisted certificate is tight to 3/23 -- so the rewrite should REBALANCE to canonical arms between
merges, or the assisted certificate needs sharpening (more explicit movers) for wider caps.
STILL OPEN: environments with a low-z neighbour (bare leaves, load-1 leaves z=3/7, hubs with
3*deg+4*load < 23 adjacent to the pair) and arm-less de-loaded connector donors.

conjecture1_proved=False.  Requires networkx, sympy.  Self-verifying run_all().
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction as Fr

import networkx as nx

from verification.kelmans_mixed_load import (
    pi_loaded,
    F_of,
    z_of,
    psi_weighted,
)


# ------------------------------------------------------------------ the composed move
def assisted_merge_apply(G: nx.Graph, load: dict, a, b, arm0):
    """Apply the assisted merge: arm0 (load-5 leaf of b) downgraded to 4, b's load 0 -> 1,
    all of b's movers reattached to a, b left as a leaf on a.  Returns (G'', load'')."""
    assert G.has_edge(a, b) and G.has_edge(b, arm0)
    assert load[b] == 0 and load[arm0] == 5 and G.degree(arm0) == 1
    H = G.copy()
    l2 = dict(load)
    l2[arm0] = 4
    l2[b] = 1
    for w in list(G.neighbors(b)):
        if w != a:
            H.remove_edge(b, w)
            H.add_edge(a, w)
    return H, l2


def _env_quantities(beta: nx.Graph, a, b, arm0, z: dict):
    """(FQ, MQ, FSr, MSr): Q = a's side without a; S_rest = b's movers minus arm0."""
    others = [x for x in beta.nodes() if x != a]
    comp_b = nx.node_connected_component(beta.subgraph(others), b)
    Ra = [x for x in beta.nodes() if x != a and x not in comp_b]
    movers_r = [x for x in comp_b if x not in (b, arm0)]
    FQ = psi_weighted(beta.subgraph(Ra), z)
    FSr = psi_weighted(beta.subgraph(movers_r), z)
    MQ = (psi_weighted(beta.subgraph([a] + Ra), z) - FQ) / z[a]
    MSr = (psi_weighted(beta.subgraph([b] + movers_r), z) - FSr) / z[b]
    return FQ, MQ, FSr, MSr


def D_form(da: int, db: int, cA: int, sQ: Fr, sr: Fr) -> Fr:
    Wt = F_of(1, 4) / F_of(1, 5)                     # 76/115
    z15, z14, z11 = z_of(1, 5), z_of(1, 4), z_of(1, 1)
    zap = z_of(da + db - 1, cA)
    za, zb = z_of(da, cA), z_of(db, 0)
    return (Wt * F_of(da + db - 1, cA) * F_of(1, 1) * (1 + zap * (sQ + sr + z14 + z11))
            - F_of(da, cA) * ((1 + za * sQ) * (1 + zb * (sr + z15)) + za * zb))


def verify_composed_identity(trials: int = 200, seed: int = 7) -> dict:
    """pi(T'') - pi(T) == Penv * FQ * FSr * D(sigma_Q, sigma_r) on random loaded trees."""
    rng = random.Random(seed)
    checked = 0
    for _ in range(trials):
        # build: a (load cA) -- b (load 0); a gets qn extra neighbours, b gets arm0 + rn movers
        cA = rng.randint(0, 5)
        G = nx.Graph()
        G.add_edge(0, 1)                     # a=0, b=1
        load = {0: cA, 1: 0}
        nxt = 2
        arm0 = nxt
        G.add_edge(1, arm0); load[arm0] = 5; nxt += 1
        def attach_subtree(root_parent):
            nonlocal nxt
            kind = rng.random()
            r = nxt
            G.add_edge(root_parent, r); load[r] = rng.randint(0, 5); nxt += 1
            if kind < 0.5:                   # leaf mover
                return
            for _ in range(rng.randint(1, 3)):   # small subtree
                G.add_edge(r, nxt); load[nxt] = rng.randint(0, 5); nxt += 1
        for _ in range(rng.randint(0, 3)):
            attach_subtree(0)
        for _ in range(rng.randint(0, 3)):
            attach_subtree(1)
        da, db = G.degree(0), G.degree(1)
        z = {v: z_of(G.degree(v), load[v]) for v in G.nodes()}
        FQ, MQ, FSr, MSr = _env_quantities(G, 0, 1, arm0, z)
        sQ, sr = MQ / FQ, MSr / FSr
        Penv = Fr(1)
        for v in G.nodes():
            if v not in (0, 1):
                Penv *= F_of(G.degree(v), load[v])
        H, l2 = assisted_merge_apply(G, load, 0, 1, arm0)
        lhs = pi_loaded(H, l2) - pi_loaded(G, load)
        rhs = Penv * FQ * FSr * D_form(da, db, cA, sQ, sr)
        assert lhs == rhs, (cA, da, db)
        checked += 1
    return {"composed_identity_exact": True, "cases": checked}


# ------------------------------------------- THE ENVIRONMENT ASSISTED-MERGE THEOREM
def certify_assisted_env() -> dict:
    """All four corners of D >= 0 over sigma_Q in [0,(da-1)z1], sigma_r in [0,(db-2)z1],
    symbolically for all hubward da >= db >= 2 (shift da = db+u, db = 2+v), per cA."""
    import sympy as sp
    u, v = sp.symbols("u v", nonnegative=True)
    db = 2 + v
    da = db + u
    z1 = sp.Rational(3, 23)
    Wt = sp.Rational(76, 115)
    F11 = sp.Rational(7, 4)
    z15, z14, z11 = sp.Rational(3, 23), sp.Rational(3, 19), sp.Rational(3, 7)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D_ = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D_) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    certified = 0
    for cA in range(6):
        zap = zs(da + db - 1, cA)
        za, zb = zs(da, cA), zs(db, 0)
        Qhi = (da - 1) * z1
        Shi = (db - 2) * z1
        ok = True
        for sQ in (sp.Integer(0), Qhi):
            for sr in (sp.Integer(0), Shi):
                Dexpr = (Wt * Fs(da + db - 1, cA) * F11 * (1 + zap * (sQ + sr + z14 + z11))
                         - Fs(da, cA) * ((1 + za * sQ) * (1 + zb * (sr + z15)) + za * zb))
                num, den = sp.fraction(sp.together(Dexpr))
                pnum = sp.Poly(sp.expand(num), u, v)
                pden = sp.Poly(sp.expand(den), u, v)
                dc = pden.coeffs()
                dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
                if dsg == 0 or not all(c * dsg >= 0 for c in pnum.coeffs()):
                    ok = False
        assert ok, cA
        certified += 1
    return {"assisted_env_theorem_cells": certified}


# ---------------------- residual direct-merge cells: the one-arm-floor certificate
def certify_residual_one_arm_floor() -> dict:
    """THEOREM: the 5 plain-box-resistant loaded-donor cells certify over the floored
    box sigma_S in [3/23, (db-1)*3/23] (donor has >= 1 arm-leaf mover), sigma_Q in
    [0, (da-1)*3/23], for all hubward da >= db >= 2 -- all four corners all-nonneg."""
    import sympy as sp
    u, v = sp.symbols("u v", nonnegative=True)
    db = 2 + v
    da = db + u
    z1 = sp.Rational(3, 23)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D_ = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D_) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    certified = 0
    for (ca, cb) in [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]:
        Fa, Fb = Fs(da, ca), Fs(db, cb)
        Fap, Fbp = Fs(da + db - 1, ca), Fs(1, cb)
        za, zb = zs(da, ca), zs(db, cb)
        zap, zbp = zs(da + db - 1, ca), zs(1, cb)
        c1 = Fap * Fbp * (1 + zap * zbp) - Fa * Fb * (1 + za * zb)
        c2 = Fap * Fbp * zap - Fa * Fb * za
        c3 = Fap * Fbp * zap - Fa * Fb * zb
        c4 = -Fa * Fb * za * zb
        for sQ in (sp.Integer(0), (da - 1) * z1):
            for sS in (z1, (db - 1) * z1):
                Phi = c1 + c2 * sQ + c3 * sS + c4 * sQ * sS
                num, den = sp.fraction(sp.together(Phi))
                pnum = sp.Poly(sp.expand(num), u, v)
                pden = sp.Poly(sp.expand(den), u, v)
                dc = pden.coeffs()
                dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
                assert dsg != 0 and all(c * dsg >= 0 for c in pnum.coeffs()), (ca, cb)
        certified += 1
    return {"residual_one_arm_floor_cells": certified}


def cap_robustness_report() -> dict:
    """Where the certificates hold as the environment z-cap widens (report, not assert):
    3/23 = load-5 arms (canonical): direct 30/30, assisted 6/6.
    3/19 = load-4 arms present:      direct 29/30 (fails (5,1)), assisted 0/6 (tight).
    See module docstring; recorded from the scan of 2026-08-14."""
    return {"cap_3_23": {"direct": "30/30", "assisted": "6/6"},
            "cap_3_19": {"direct": "29/30 fails [(5,1)]", "assisted": "0/6 (certificate tight)"},
            "consequence": "rebalance to canonical load-5 arms between merges, or sharpen the "
                           "assisted certificate for wider caps"}


# --------------------------------------- residual direct-merge cells: reality probe
def residual_cells_probe() -> dict:
    """The box's worst fear for {(0,5),(1,4),(1,5),(2,5),(3,5)}: donor with ONE arm and
    many HIGH-DEGREE hub-children (sigma_S pinned near 3/23), receiver with all-arm
    environment (sigma_Q at its max).  Exact pi difference for the direct hubward merge."""
    from verification.kelmans_mixed_load import kelmans_step
    decreases = []
    checked = 0
    for (ca, cb) in [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]:
        for pa in (6, 12, 24):                 # receiver arms (sigma_Q high)
            for nhub in (2, 4):                # donor hub-children count
                for hub_arms in (6, 12):       # each hub-child's own arms (high degree)
                    G = nx.Graph()
                    load = {0: ca, 1: cb}
                    G.add_edge(0, 1)
                    nxt = 2
                    for _ in range(pa):
                        G.add_edge(0, nxt); load[nxt] = 5; nxt += 1
                    G.add_edge(1, nxt); load[nxt] = 5; nxt += 1      # the single donor arm
                    for _ in range(nhub):
                        h = nxt
                        G.add_edge(1, h); load[h] = 0; nxt += 1
                        for _ in range(hub_arms):
                            G.add_edge(h, nxt); load[nxt] = 5; nxt += 1
                    if G.degree(0) < G.degree(1):
                        continue               # keep hubward
                    Gp = kelmans_step(G, 0, 1)
                    d = pi_loaded(Gp, load) - pi_loaded(G, load)
                    checked += 1
                    if d < 0:
                        decreases.append((ca, cb, pa, nhub, hub_arms, float(d)))
    return {"residual_probe_cases": checked, "decreases": decreases}


def run_all():
    out = {}
    out["composed_identity"] = verify_composed_identity()
    out["assisted_env_theorem"] = certify_assisted_env()
    out["residual_one_arm_floor"] = certify_residual_one_arm_floor()
    out["residual_probe"] = residual_cells_probe()
    out["cap_robustness"] = cap_robustness_report()
    out["env_merge_table"] = {
        "direct_merge": "hubward, donor load 1..5 with >=1 arm-leaf mover, env 3deg+4load>=23: "
                        "ALL 30 cells, any environment (25 plain box [kelmans_mixed_load] + "
                        "5 via the one-arm floor [this module])",
        "assisted_merge": "hubward, de-loaded donor with >=1 arm-leaf mover, same env "
                          "condition: ALL 6 receiver cells, any environment (this module)",
        "still_open": "low-z neighbours (bare/load-1 leaves, hubs with 3deg+4load<23) "
                      "adjacent to the pair; arm-less de-loaded connector donors; "
                      "assisted certificate beyond the canonical 3/23 cap",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
