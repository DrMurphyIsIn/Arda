"""The rem:tie constant-order tiebreak, RESOLVED at the surface-constant level.

Remark (paper): at matched vertex count a single-hub star and a double star both attain the growth rate
rho_B=(621/64)^{1/11}, differing only at constant order -- so "the backbone is a star" hides a
constant-order tiebreak (single hub vs two hubs vs ...).  This module resolves it exactly.

DE-LOADED CHERRY-BUNDLE CONFIGURATIONS.  Fix the rate-optimal building block: an arm-center of degree 6
carrying five length-2 cherries, which contributes EXACTLY rho_B^{11}=621/64 (spanning 11 vertices).  An
m-hub configuration is m cherry-less "hubs" (a backbone on m vertices) with k arm-centers distributed among
them.  Then n=m+11k and, since each hub carries no cherries (F(hub)=1) and each arm-center contributes
621/64,
    pi = (621/64)^{k} * Psi_m  =  rho_B^{n-m} * Psi_m ,
where Psi_m = sum over matchings of the m-hub backbone of prod z_v (activities z_v=3/(3 deg_v) at a
de-loaded hub, z=3/23 at an arm-center).  So the SURFACE CONSTANT is
    C_m := pi / rho_B^{n} = Psi_m / rho_B^{m}.

EXACT CLOSED FORMS (verified against the permanent):
    single hub:  pi = (26/23)(621/64)^{k},         Psi_1 = 26/23,      so C_1 = (26/23)/rho_B.
    double hub:  pi = (621/64)^{k_a+k_b} * Psi_D,   Psi_D = 1 + k_a z_A z + k_b z_B z + z_A z_B
                                                            + k_a k_b z_A z_B z^2,  z=3/23,
                 z_A=1/(k_a+1), z_B=1/(k_b+1); Psi_D -> (26/23)^2 as k_a,k_b -> inf.
More generally, each hub with K -> inf arms contributes a factor (1 + K z_hub * 3/23) -> 26/23 while the
inter-hub backbone activities z_v z_w -> 0, so Psi_m -> (26/23)^m and
    C_m  ->  (26/23)^m / rho_B^m  =  C_1^m .

THE TIEBREAK, EXACTLY.  C_1 = (26/23)/rho_B < 1 is the EXACT RATIONAL INEQUALITY
    (26/23)^{11} < 621/64            (i.e. 26/23 < rho_B),
which holds with room (3.85 < 9.70).  Since 0 < C_1 < 1, the surface constants strictly decrease in the
hub count, C_1 > C_1^2 > C_1^3 > ...: FEWER HUBS STRICTLY WIN, and the SINGLE HUB (m=1) is the unique
maximizer.  Hence for all large n the single-hub cherry-bundle star strictly exceeds every multi-hub
configuration at matched vertex count -- the constant-order margin is a fixed factor
1/C_1 = rho_B*23/26 = 1.0876..., which dominates the O(1/k) finite-size corrections.  This resolves the
rem:tie tiebreak (and, beyond a single double star, every m-hub competitor).

SCOPE (honest).  This settles the constant-order tiebreak AMONG de-loaded cherry-bundle configurations --
i.e. once one knows the maximizer is such a configuration, its backbone is a single hub.  It does NOT by
itself prove Conjecture 1: that still needs Phi<=1 (the certified candidate) to force cherry-arm branches,
and the global structural reduction that the maximizer is a cherry-bundle configuration at all.  The
single-hub-vs-multi-hub question, however, is now closed exactly, with the same 23-adic crux
((26/23)^11 < 621/64) as the rest of the program.

Requires numpy, networkx.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import networkx as nx
import numpy as np

from verification.permanent import laplacian_ratio

RHO11 = Fr(621, 64)
LOG_RHO = math.log(621 / 64) / 11


def _single_hub(k):
    G = nx.Graph()
    G.add_node(0)
    nxt = 1
    for _ in range(k):
        ac = nxt
        nxt += 1
        G.add_edge(0, ac)
        for _ in range(5):
            y, z = nxt, nxt + 1
            nxt += 2
            G.add_edge(ac, y)
            G.add_edge(y, z)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def _double_hub(ka, kb):
    G = nx.Graph()
    G.add_edge(0, 1)
    nxt = 2
    for h, K in ((0, ka), (1, kb)):
        for _ in range(K):
            ac = nxt
            nxt += 1
            G.add_edge(h, ac)
            for _ in range(5):
                y, z = nxt, nxt + 1
                nxt += 2
                G.add_edge(ac, y)
                G.add_edge(y, z)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def _path_hub(hub_arms):
    m = len(hub_arms)
    G = nx.Graph()
    for h in range(m):
        G.add_node(h)
    for h in range(m - 1):
        G.add_edge(h, h + 1)
    nxt = m
    for h, K in enumerate(hub_arms):
        for _ in range(K):
            ac = nxt
            nxt += 1
            G.add_edge(h, ac)
            for _ in range(5):
                y, z = nxt, nxt + 1
                nxt += 2
                G.add_edge(ac, y)
                G.add_edge(y, z)
    return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)


def _PsiD(ka, kb):
    zA, zB, z = Fr(1, ka + 1), Fr(1, kb + 1), Fr(3, 23)
    return 1 + ka * zA * z + kb * zB * z + zA * zB + ka * kb * zA * zB * z * z


def _logpi_root_n(A):
    p = laplacian_ratio(A)
    n = A.shape[0]
    return (math.log(p.numerator) - math.log(p.denominator)) / n


def certify():
    # (1) exact closed forms
    single_ok = all(laplacian_ratio(_single_hub(k)) == Fr(26, 23) * RHO11 ** k for k in (1, 2, 3, 5, 8))
    double_ok = all(laplacian_ratio(_double_hub(ka, kb)) == RHO11 ** (ka + kb) * _PsiD(ka, kb)
                    for (ka, kb) in ((2, 2), (3, 2), (4, 4), (6, 3)))
    # (2) the exact crux C_1 < 1
    crux = Fr(26, 23) ** 11 < RHO11
    C1 = (26 / 23) / (621 / 64) ** (1 / 11)
    # (3) m-hub surface constant -> C_1^m  (log-space; K arms per hub)
    K = 60
    surf = []
    for m in (1, 2, 3, 4):
        A = _path_hub([K] * m)
        n = A.shape[0]
        C_emp = math.exp(_logpi_root_n(A) * n - n * LOG_RHO)   # pi / rho_B^n
        surf.append((m, C_emp, C1 ** m))
    surf_ok = all(abs(ce - c1m) / c1m < 0.03 for _, ce, c1m in surf)   # approaches C1^m (finite-K, ~1/K)
    strictly_decreasing = all(surf[i][1] > surf[i + 1][1] for i in range(len(surf) - 1))
    # (4) Psi_D -> (26/23)^2
    psiD_lim = _PsiD(10 ** 8, 10 ** 8)
    return {
        "single_hub_closed_form_exact": single_ok,     # pi=(26/23)(621/64)^k
        "double_hub_closed_form_exact": double_ok,      # pi=(621/64)^K Psi_D
        "C1_lt_1_exact_rational": crux,                 # (26/23)^11 < 621/64
        "C1": C1,
        "surface_constant_is_C1_pow_m": surf_ok,        # C_m ~ C1^m
        "surface_constants_strictly_decrease_in_hubs": strictly_decreasing,  # single hub wins
        "PsiD_limit_eq_26_23_sq": abs(float(psiD_lim) - float(Fr(26, 23) ** 2)) < 1e-6,
        "constant_order_margin_1_over_C1": 1 / C1,      # 1.0876: single-hub advantage factor
        "rem_tie_resolved_constant_order": bool(single_ok and double_ok and crux and strictly_decreasing),
        "note": "resolves single- vs multi-hub tiebreak among de-loaded cherry-bundle configs; Conjecture 1 "
                "still needs Phi<=1 (candidate) + the global structural reduction.",
        "conjecture1_proved": False,
    }


if __name__ == "__main__":
    v = certify()
    for k, val in v.items():
        print(f"  {k}: {val}")
