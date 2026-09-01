"""Tests for the tie-regime campaign: the uniform-hub potential + the arithmetic cherry-worst reduction.

Verifies: uniform_hub_ell(k, cherry) == branch ell(B(k)); the envelope tops are brooms; the cherry-worst
rational ratio > 1 (slack) in the tie regime; ell(hub of k cherries) has its max = 0 at k=5.
conjecture1_proved = False.
"""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.branch_potential import branch_ell, broom_edges  # noqa: E402
from telperion.tie_regime import (  # noqa: E402
    CHERRY,
    TieCherryWorstCertificate,
    binding_j,
    broom_child,
    cherry_vs_broom_ratio,
    uniform_hub_ell,
)


def test_uniform_cherry_hub_is_broom():
    """ell(hub of k cherries) == branch ell(B(k)) (the broom), to float precision."""
    for k in range(1, 9):
        ell_uniform = uniform_hub_ell(k, CHERRY)
        ell_broom, _ = branch_ell(*broom_edges(k))
        assert abs(ell_uniform - ell_broom) < 1e-9, f"k={k}"


def test_broom_hub_max_at_5():
    """max_k ell(hub of k cherries) = 0 at k=5 (the tie); strictly negative elsewhere -- the broom optimum (B)."""
    vals = {k: uniform_hub_ell(k, CHERRY) for k in range(1, 12)}
    assert max(vals, key=vals.get) == 5
    assert abs(vals[5]) < 1e-9
    for k in range(1, 5):
        assert vals[k] < -1e-9
    for k in range(6, 12):
        assert vals[k] < -1e-9


def test_cherry_worst_rational_and_slack():
    """cherry-worst: exp(11*(ell(k,cherry)-ell(k,B(j)))) is EXACT rational and > 1 (slack, >= 2) in the tie
    regime -- so the cherry is the worst uniform child with margin (only the broom step is tie-tight)."""
    for k in range(2, 8):
        for j in range(2, 8):
            r = cherry_vs_broom_ratio(k, j)
            assert isinstance(r, Fr)
            assert r > 1, f"cherry not worst at k={k}, j={j}"
            assert r > Fr(3, 2), f"expected slack (>1.5) at k={k}, j={j}, got {float(r)}"  # min ~1.95 at (2,2)


def test_cherry_beats_broom_children_ell():
    """Directly: ell(hub of k cherries) >= ell(hub of k B(j)) for tie-regime k (cherry is the worst child)."""
    for k in range(1, 9):
        ec = uniform_hub_ell(k, CHERRY)
        for j in range(2, 10):
            assert ec >= uniform_hub_ell(k, broom_child(j)) - 1e-12, f"k={k}, j={j}"


def test_ratio_unimodal_in_j_and_binding():
    """cherry_vs_broom_ratio(k, .) is unimodal in j (min at binding_j(k)); ratio(k, j*) > 1 covers all j."""
    for k in range(2, 21):
        js = binding_j(k)
        vals = {j: cherry_vs_broom_ratio(k, j) for j in range(1, 25)}
        assert min(vals, key=vals.get) == js
        assert all(vals[j] > vals[j + 1] for j in range(1, js))       # decreasing to j*
        assert all(vals[j] < vals[j + 1] for j in range(js, 24))      # increasing after j*
        assert vals[js] > 1                                            # binding case still cherry-worst


def test_tie_cherry_worst_certificate_k20():
    """The k<=20 certificate holds exactly and emits a well-formed norm_num module (19 atoms)."""
    cert = TieCherryWorstCertificate(k_max=20)
    assert cert.check() is True
    assert len(cert.atoms()) == 19
    mod = cert.lean_module()
    assert "import Mathlib" in mod and "namespace BGTieCherryWorst" in mod
    assert mod.count("by norm_num") == 19
    # k=21 is outside the tie regime -- the certificate must NOT claim it
    assert cherry_vs_broom_ratio(21, 4) < 1


def _hub(children):
    """Build a hub (root 0) from a list of child specs and return its exact ell."""
    from telperion.branch_potential import branch_ell
    E = []
    nid = 1
    for spec in children:
        if spec == ("leaf",):
            E.append((0, nid)); nid += 1
        elif spec == ("cherry",):
            E.append((0, nid)); E.append((nid, nid + 1)); nid += 2
        elif spec[0] == "broom":
            hub = nid; E.append((0, hub)); nid += 1
            for _ in range(spec[1]):
                E.append((hub, nid)); E.append((nid, nid + 1)); nid += 2
    ell, _ = branch_ell(nid, tuple(E), 0)
    return ell


def test_mixed_le_uniform_k_le_15():
    """mixed <= B(k) for k in {2..15} ONLY -- it FAILS at k >= 20 (a hub of (k-1) cherries + one B(5)-child
    beats B(k); mixed - B(20) = +0.00035). The mixed reduction is used only for k <= 15; the slack bound covers
    k >= 16 (`slack_g(k) <= F*`). So no gap. (Corrects the earlier false 'k <= 20' claim -- caught by the
    child->cherry exchange analysis.)"""
    import random
    from telperion.branch_potential import branch_ell, broom_edges
    pool = [("leaf",), ("cherry",), ("broom", 2), ("broom", 4), ("broom", 5), ("broom", 6)]
    rng = random.Random(7)
    for k in range(2, 16):                                     # k <= 15 (mixed<=B(k) holds; slack covers k>=16)
        ell_bk, _ = branch_ell(*broom_edges(k))
        for _ in range(300):
            ch = [rng.choice(pool) for _ in range(k)]
            assert _hub(ch) <= ell_bk + 1e-12, f"mixed hub beats B({k})"
        for a in range(k + 1):
            assert _hub([("leaf",)] * a + [("cherry",)] * (k - a)) <= ell_bk + 1e-12
    # the failure at k=20 is REAL and must be recorded (not asserted away):
    mix20 = _hub([("cherry",)] * 19 + [("broom", 5)])
    ell_b20, _ = branch_ell(*broom_edges(20))
    assert mix20 > ell_b20                                     # mixed BEATS B(20) -- reduction fails here
    assert mix20 < 0                                           # but the BOUND ell <= 0 still holds


def test_slack_regime_bound():
    """Slack regime k>=21: ell(hub) <= slack_hub_bound(k) <= 0 (tie-free soft bound); sup at k=21."""
    from telperion.tie_regime import slack_hub_bound, slack_g
    for k in [21, 22, 25, 30, 50, 100, 500]:
        assert slack_hub_bound(k) < 0, f"slack bound not < 0 at k={k}"
        assert slack_g(k) < 0.207, f"g(k) not < F* at k={k}"
    # tightest at the boundary k=21, with margin ~0.05
    assert -0.06 < slack_hub_bound(21) < -0.04


def test_slack_certificate():
    """TieSlackCertificate: the slack bound slack_g(k)<=F* (k>=16) via frozen log-enclosures -- checks exactly
    and emits a well-formed norm_num module (phi16 + deriv16 + F*>3/23 atoms)."""
    from telperion.tie_regime import TieSlackCertificate
    cert = TieSlackCertificate()
    assert cert.check() is True
    names = [a[0] for a in cert.atoms()]
    assert sum("phi16" in n for n in names) == 8                # slack_g(16)<F* per envelope child
    assert sum("deriv16" in n for n in names) == 7              # monotone (non-B(5))
    assert "tie_slack_Fstar_gt_3_23" in names                   # B(5) bound
    mod = cert.lean_module()
    assert "import Mathlib" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_mixed_kkt_reduction_concavity():
    """The concavity tangent bound is EXACT (never violated): for arbitrary mixed hubs,
    ell(hub) - ell(B(k)) <= sum_i (V(c_i) - V(cherry)), V(c)=ell(c)+lambda(k) x_c, lambda(k)=3(k+1)/(4k+3).
    This is the rigorous log-concavity step that decouples the mixed-hub bound into per-child inequalities."""
    import random
    from telperion.branch_potential import branch_ell, broom_edges
    from telperion.tie_regime import mixed_lambda, child_value, CHERRY, broom_child
    from fractions import Fraction as Fr

    # lambda(k) = 3(k+1)/(4k+3) exact (derivative of log(1+.) at the all-cherry point)
    assert mixed_lambda(5) == Fr(18, 23)

    specs = {("cherry",): CHERRY, ("broom", 2): broom_child(2), ("broom", 4): broom_child(4),
             ("broom", 5): broom_child(5), ("broom", 6): broom_child(6)}
    rng = random.Random(11)
    for k in range(2, 16):
        ell_bk, _ = branch_ell(*broom_edges(k))
        vch = child_value(CHERRY, k)
        for _ in range(200):
            ch = [rng.choice(list(specs)) for _ in range(k)]
            ell_hub = _hub(ch)
            rhs = sum(child_value(specs[c], k) - vch for c in ch)          # sum (V(c_i) - V(cherry))
            assert ell_hub - ell_bk <= rhs + 1e-12                          # concavity tangent (rigorous)
            assert rhs <= 1e-9                                              # per-child KKT => sum <= 0


def test_mixed_hub_kkt_certificate():
    """MixedHubKKTCertificate: per-child V(c) < V(cherry) for every broom child and k in [2,15], via frozen
    log-enclosures -- proving (with concavity) mixed <= B(k) for k <= 15. Checks exact + emits norm_num."""
    from telperion.tie_regime import MixedHubKKTCertificate, cherry_is_kkt_argmax
    cert = MixedHubKKTCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 14 * 7                                      # k=2..15 x B(2..8)
    # KKT (cherry = argmax V over the broom envelope) holds across the whole tie regime k<=15 ...
    assert all(cherry_is_kkt_argmax(k) for k in range(2, 16))
    # ... and must FAIL for large k (else it would contradict mixed<=B(k) itself failing at k>=20)
    assert not cherry_is_kkt_argmax(20)
    mod = cert.lean_module()
    assert "import Mathlib" in mod and "namespace BGMixedHubKKT" in mod
    assert mod.count("by norm_num") == len(cert.atoms())


def test_slack_bound_proof_structure():
    """Rigorous proof of slack_g(k) <= F* for k>=16: (1) slack_g monotone-decreasing so <= slack_g(16);
    (2) slack_g(16) < F*; (3) per-child, every non-B(5) envelope child phi_c is decreasing for k>=16
    (deriv = ell(c) + (h/d)/(k+1)^2 < 0, and deriv <= deriv@16), and B(5) is bounded by 3/23 < F*."""
    import math
    from telperion.tie_regime import slack_g, broom_child
    from telperion.branch_potential import F_STAR
    g16 = slack_g(16)
    assert all(slack_g(k) <= g16 + 1e-12 for k in range(16, 400))   # (1) monotone-decreasing sup
    assert g16 < F_STAR                                             # (2) binding value < F*
    # (3) per-child derivative at k=16 (the largest, since (k+1)^2 grows): < 0 for non-B(5), B(5) bounded
    for j in list(range(2, 9)):
        c = broom_child(j)
        tot, sz = c["total"], c["size"]
        el = (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR
        deriv16 = el + (float(c["h"]) / c["d"]) / 17 ** 2
        if j == 5:
            assert 3 / 23 < F_STAR                                 # B(5): phi -> 3/23 < F*
        else:
            assert deriv16 < 0                                     # decreasing for all k >= 16
