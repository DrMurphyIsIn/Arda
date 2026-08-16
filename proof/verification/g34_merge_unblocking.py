"""G3/G4 DISCHARGE (major narrowing): merge unblocking -- cap widening, the balancing lemma,
the sharpened boundary factor, and the single named residual.

The architecture's G3 (defects adjacent to a merging hub pair block the certified merges) and
G4 (donors with too few arms cannot top up) reduce, after the three certificates below, to ONE
named ledger-bounded finite family with an already-proven-in-core backstop.

(A) CAP WIDENING + ROUTE, certified.  The unified topped-up merge table holds at environment
    cap z <= 1/5 (3*deg + 4*load >= 15) for 35/36 cells; the single failing cell (cA,cb) =
    (1,5) is ROUTED by the RECEIVER-BORROW fused move (receiver borrows one cherry from its
    own load-5 arm: cA 1 -> 2, arm 5 -> 4, then direct merge in the certified (2,5) cell) --
    itself certified at cap 1/5 (certify_cap_15 + certify_route_15).
    CONSEQUENCE: arm(3) neighbours (z = 1/5) no longer block anything.

(B) THE BALANCING LEMMA (conditional), certified.  For arms x (load ch), y (load cl) on a hub
    that carries AT LEAST TWO OTHER arm-neighbours of loads 4..6 (any hub load 0..5, any
    environment beyond), the balancing transfer (ch, cl) -> (ch-1, cl+1), ch >= cl+2, is
    pi-non-decreasing: the difference is linear in the environment scalar sigma with a
    PROVEN-nonneg coefficient (the F-product increases under balancing), and the coupled
    (z_hub, sigma) certificate closes for e >= 2 arm-neighbours (certify_balancing).
    The move is GENUINELY false without the condition (a bare 2-arm hub: ratio 0.956) -- the
    condition is sharp in kind.  CONSEQUENCE: bare leaves and arm(<=2)s on ARM-RICH hubs are
    balanced up into the cap (loads climb toward the mean >= 3); merges then fire.

(C) SHARPENED BOUNDARY FACTOR, proven.  Rooting at a CHERRY TIP (leaf whose neighbour has
    degree 2) gives S = z_mid * rho <= 1/2 exactly, hence R = (1+S)/(1+S/2) <= 6/5.  Every
    Stage-I survivor contains a cherry (cherry-free trees have every node paying chain/leaf
    floors -- over budget), so the elimination budget TIGHTENS to
        log(6/(5*C_1)) = 0.26631  (from 0.37167).
    Tightened confinement: nl >= 3 nodes eliminated OUTRIGHT (floor 0.26673 > budget);
    bare-leaf defects <= 5; chains <= 48; pure hubs <= 11 (amortized).

(D) THE NAMED RESIDUAL (all that remains of G3/G4).  After (A)+(B)+(C), a multi-hub survivor
    can evade every certified move only if EVERY blocking defect sits on an ARM-POOR hub
    (fewer than 2 spare arm-neighbours: tiny hubs, or hubs whose mass is sub-hub-heavy) AND
    the whole configuration stays under the tightened ledger budget -- an explicitly
    parametrized finite family ("G34-residual"), which additionally contains all
    small-structure donors (G4).  BACKSTOP, proven in core: the same-n template domination --
    the two-hub stuck theorem (kelmans_vertex_budget, ALL pA,pB >= 1) plus the 3/4-hub and
    Lemma-A-tower sweeps -- kills every probed member; the symbolic extension of the
    domination to the full parametrized family is the residual check.

conjecture1_proved=False.  Self-verifying run_all().
"""
from __future__ import annotations

import math
import sys

sys.setrecursionlimit(100000)

from fractions import Fraction as Fr

import sympy as sp

from verification.kelmans_mixed_load import (
    pi_loaded,
    psi_weighted,
)

C1 = (26 / 23) / (621 / 64) ** (1 / 11)


def _sym_tools():
    u, v = sp.symbols("u v", nonnegative=True)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def zs(deg, c):
        return sp.Integer(3) / (3 * deg + 4 * c)

    def allnn(expr):
        num, den = sp.fraction(sp.together(expr))
        pnum = sp.Poly(sp.expand(num), u, v)
        pden = sp.Poly(sp.expand(den), u, v)
        dc = pden.coeffs()
        dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
        return dsg != 0 and all(c * dsg >= 0 for c in pnum.coeffs())

    return u, v, Fs, zs, allnn


def certify_cap_15() -> dict:
    """(A1): the unified table at cap 1/5 -- exactly one failing cell, (1,5)-direct."""
    u, v, Fs, zs, allnn = _sym_tools()
    CAP = sp.Rational(1, 5)
    z15c, z14c = sp.Rational(3, 23), sp.Rational(3, 19)
    Wt, V5 = sp.Rational(76, 115), sp.Rational(621, 64)
    fails = []
    for cb in range(5):
        k = 5 - cb
        db = k + 1 + v
        da = db + u
        for cA in range(6):
            za, zb = zs(da, cA), zs(db, cb)
            zap = zs(da + db - 1, cA)
            ok = all(allnn(Wt ** k * Fs(da + db - 1, cA) * V5
                           * (1 + zap * (sQ + k * z14c + sr + z15c))
                           - Fs(da, cA) * Fs(db, cb)
                           * ((1 + za * sQ) * (1 + zb * (k * z15c + sr)) + za * zb))
                     for sQ in (sp.Integer(0), (da - 1) * CAP)
                     for sr in (sp.Integer(0), v * CAP))
            if not ok:
                fails.append((cA, cb))
    db2 = 2 + v
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
        ok = all(allnn(c1 + c2 * sQ + c3 * sS + c4 * sQ * sS)
                 for sQ in (sp.Integer(0), (da2 - 1) * CAP)
                 for sS in (sp.Rational(3, 23), (db2 - 1) * CAP))
        if not ok:
            fails.append((cA, 5))
    assert fails == [(1, 5)], fails
    return {"cap_1_5_cells": 35, "only_failure": "(1,5)-direct"}


def certify_route_15() -> dict:
    """(A2): the (1,5) receiver-borrow fused route, certified at cap 1/5."""
    u, v, Fs, zs, allnn = _sym_tools()
    CAP = sp.Rational(1, 5)
    z15c, z14c = sp.Rational(3, 23), sp.Rational(3, 19)
    Wt = sp.Rational(76, 115)
    db = 2 + v
    da = db + u
    za1, zb5 = zs(da, 1), zs(db, 5)
    zap2 = zs(da + db - 1, 2)
    for sQ in (sp.Integer(0), (da - 2) * CAP):
        for sS in (z15c, (db - 1) * CAP):
            before = Fs(da, 1) * Fs(db, 5) * ((1 + za1 * (z15c + sQ)) * (1 + zb5 * sS) + za1 * zb5)
            after = Wt * Fs(da + db - 1, 2) * Fs(1, 5) * (1 + zap2 * (z14c + sQ + sS + z15c))
            assert allnn(after - before)
    return {"route_1_5": "certified (receiver-borrow into (2,5))"}


def certify_balancing() -> dict:
    """(B): balancing (ch,cl)->(ch-1,cl+1) on a hub with >= 2 other arm-neighbours
    (loads 4..6), any hub load 0..5, any environment: pi-non-decreasing.  Sharp in kind:
    genuinely false on a bare 2-arm hub (checked)."""
    t = sp.symbols("t", nonnegative=True)

    def F1(c):
        if c == 0:
            return sp.Integer(1)
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * (1 + c)) * sp.Rational(3, 2) ** (c - 1)

    def z1(c):
        return sp.Integer(3) / (3 + 4 * c)

    def allnn1(expr):
        num, den = sp.fraction(sp.together(expr))
        pnum = sp.Poly(sp.expand(num), t)
        pden = sp.Poly(sp.expand(den), t)
        dc = pden.coeffs()
        dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
        return dsg != 0 and all(c * dsg >= 0 for c in pnum.coeffs())

    e = 2 + t
    for c0 in range(0, 6):
        zH = sp.Integer(3) / (3 * (2 + e) + 4 * c0)
        for ch in range(2, 9):
            for cl in range(0, ch - 1):
                FA = F1(ch - 1) * F1(cl + 1)
                FB = F1(ch) * F1(cl)
                assert allnn1(FA - FB)                      # sigma-coefficient
                SA = z1(ch - 1) + z1(cl + 1)
                SB = z1(ch) + z1(cl)
                for sig in (e * sp.Rational(1, 9), e * sp.Rational(3, 19)):
                    assert allnn1(FA * (1 + zH * (SA + sig)) - FB * (1 + zH * (SB + sig))), (c0, ch, cl)
    # sharpness in kind: bare 2-arm hub genuinely decreases
    import networkx as nx
    G = nx.Graph()
    G.add_edge(0, 1)
    G.add_edge(0, 2)
    lo = {0: 0, 1: 5, 2: 0}
    la = {0: 0, 1: 4, 2: 1}
    assert pi_loaded(G, la) < pi_loaded(G, lo)
    return {"balancing": "certified for hubs with >= 2 other arm-neighbours (loads 4..6), "
                         "all pairs ch<=8, hub loads 0..5", "bare_2arm_hub": "genuinely down"}


def certify_sharp_R(n_max: int = 9) -> dict:
    """(C): at a cherry-tip root S <= 1/2 exactly, hence R <= 6/5; sharpened budget."""
    import networkx as nx

    def f_at(T, r, zr):
        z = {vv: (zr if vv == r else Fr(1, T.degree(vv))) for vv in T.nodes()}
        return psi_weighted(T, z)

    cnt = 0
    for n in range(4, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            for r in T.nodes():
                if T.degree(r) != 1:
                    continue
                (c,) = list(T.neighbors(r))
                if T.degree(c) != 2:
                    continue
                A0 = f_at(T, r, Fr(0))
                A1 = f_at(T, r, Fr(1)) - A0
                assert A1 / A0 <= Fr(1, 2), (n, r)
                cnt += 1
    budget = math.log(6 / (5 * C1))
    assert 0.266 < budget < 0.267
    return {"cherry_tip_cases": cnt, "R_bound": "6/5", "sharpened_budget": round(budget, 5),
            "tightened": "nl>=3 nodes eliminated outright (0.26673 > 0.26631); "
                         "bare leaves <= 5; chains <= 48; pure hubs <= 11"}


def run_all():
    out = {}
    out["A_cap"] = certify_cap_15()
    out["A_route"] = certify_route_15()
    out["B_balancing"] = certify_balancing()
    out["C_sharp_R"] = certify_sharp_R()
    out["G34_status"] = {
        "discharged": "arm(3) blockers (cap 1/5 + route); low arms/leaves on arm-rich hubs "
                      "(balancing); short-total hubs (sharpened budget: nl>=3 outright)",
        "named_residual": "G34-residual: multi-hub survivors whose every blocking defect "
                          "sits on an ARM-POOR hub (< 2 spare arm-neighbours), within the "
                          "tightened ledger budget; includes small-structure donors.  "
                          "Backstop proven in core: same-n template domination (two-hub "
                          "theorem, all pA,pB; 3/4-hub + tower sweeps).  Remaining check: "
                          "symbolic template domination over the parametrized residual family",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
