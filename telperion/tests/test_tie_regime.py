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
