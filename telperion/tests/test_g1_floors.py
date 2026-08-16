"""The G1 floor family: structure and spot checks (full regen runs in verify)."""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "examples" / "g1_floors"))

import family as G1  # noqa: E402

from telperion import certify  # noqa: E402
from telperion.certify import restrict_instances  # noqa: E402


def test_claim_inventory_matches_origin_structure():
    cs = G1.claims()
    kinds = {k: sum(1 for c in cs if c[0] == k) for k in ("leaf", "m0", "collapse")}
    assert kinds["collapse"] == 6 + 10 + 7          # mixed + bare-leaf + nl2
    assert kinds["m0"] >= 9 + 7 + 3                 # bare-leaf + nl2 + ladder (deduped)
    assert kinds["leaf"] > 300                      # the bisection refinement
    assert len({G1._name(c) for c in cs}) == len(cs)  # names unique


def test_worst_corner_floors_hold_exactly():
    # every claim clears its floor at (L_LO, G_HI) — the origin's own criterion
    for c in G1.claims()[::25]:
        t = G1._target(c)
        val = t.subs({G1.L: sp.Rational(G1.L_LO), G1.G: sp.Rational(G1.G_HI)})
        assert val >= 0, c


def test_spot_certification_of_cells():
    fam = G1.family()
    cf = certify(fam)  # full certification is cheap (~1 s): linear 2-bracket cells
    assert len(cf.instances) == len(G1.claims())
    assert all(len(i.corners) == 4 for i in cf.instances)


def test_anchor_facts_verified_at_minimal_K():
    facts = G1.anchor_facts()
    assert len(facts) > 100
    for name, u0, q, K in facts[::20]:
        assert G1.exp_lower(q, K) >= 1 + u0
        if K > 1:
            assert G1.exp_lower(q, K - 1) < 1 + u0   # K is minimal
