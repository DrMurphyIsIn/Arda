"""Tests for the explicit N0 (growth_n0.py) and the cherry-distribution step (distribution.py)."""
import random
from fractions import Fraction as Fr

import trees
import permanent
import growth_n0 as g0
import distribution as dist


# ---- N0 / spider upper bound ----

def test_C_upper_certificate():
    assert g0.certify_C_upper()

def test_c_prime_lower_bound():
    assert g0.certify_c_prime()

def test_N0_crude_subsequence():
    assert g0.certify_N0_crude()

def test_N0_tight_all_residues():
    # branch beats every spider (via C rho_S^n envelope) for all n >= 412, fails at 411
    assert g0.certify_N0_tight(dist.best_branch_pi)

def test_spider_upper_bound_holds_on_sample():
    import math
    rhoS = math.sqrt(377 / 250); C = float(g0.C_UPPER)
    random.seed(0)
    worst = 0.0
    cfgs = [[random.randint(0, 12) for _ in range(random.randint(1, 8))] for _ in range(200)]
    cfgs += [[a] for a in range(1, 30)] + [[a, a] for a in range(1, 20)]
    for cfg in cfgs:
        if sum(cfg) == 0:
            continue
        A = trees.spider(cfg); n = A.shape[0]
        if n < 2:
            continue
        try:
            pi = float(permanent.laplacian_ratio(A))
        except ZeroDivisionError:
            continue
        worst = max(worst, pi / rhoS ** n)
    assert worst <= C


# ---- distribution / non-uniform star ----

def test_nonuniform_star_closed_form_matches_permanent():
    import networkx as nx
    def build(c0, arms):
        G = nx.Graph(); k = len(arms); G.add_nodes_from(range(k + 1))
        for a in range(1, k + 1):
            G.add_edge(0, a)
        nxt = k + 1
        for ctr, cc in enumerate([c0] + list(arms)):
            for _ in range(cc):
                y, z = nxt, nxt + 1; nxt += 2
                G.add_edge(ctr, y); G.add_edge(y, z)
        return nx.to_numpy_array(G, nodelist=range(nxt), dtype=int)
    random.seed(2)
    for _ in range(30):
        k = random.randint(1, 5); c0 = random.randint(3, 8)
        arms = [random.randint(3, 8) for _ in range(k)]
        assert permanent.laplacian_ratio(build(c0, arms)) == dist.pi_star(c0, arms)

def test_g_log_concave():
    assert dist.certify_g_log_concave()

def test_arm_balancing_certificate():
    assert dist.certify_arm_balancing()

def test_arm_balancing_matches_brute_force():
    # at fixed hub and total arm cherries, balanced arms maximise pi
    def brute(c0, k, arm_total):
        best = None
        def comps(total, n, cmin=3):
            if n == 1:
                if total >= cmin:
                    yield (total,)
                return
            for x in range(cmin, total - cmin * (n - 1) + 1):
                for rest in comps(total - x, n - 1, cmin):
                    yield (x,) + rest
        for arms in comps(arm_total, k):
            v = dist.pi_star(c0, list(arms))
            if best is None or v > best[0]:
                best = (v, tuple(sorted(arms)))
        return best[1]
    for k in (2, 3, 4):
        for arm_total in range(3 * k, 3 * k + 6):
            arms = brute(4, k, arm_total)
            assert max(arms) - min(arms) <= 1  # balanced

def test_hub_sinks_to_floor_at_large_n():
    # asymptotically the maximizing star has hub at the floor c0=3
    _, k, c0, arms = dist.best_star_at_n(341)
    assert c0 == 3 and min(arms) >= 4


def test_arm_balancing_symbolic_proof():
    res = dist.certify_arm_balancing_symbolic()
    assert res["proven"] and res["den_nonneg"]
    assert res["num_min_coeff"] >= 0

def test_A_single_exact():
    assert dist.A_SINGLE == Fr(468, 529)

def test_single_star_beats_near_star_competitors():
    assert dist.certify_single_beats_double(p=60)
