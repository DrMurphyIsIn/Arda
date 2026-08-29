"""The collective-cancellation obstruction, kernel-gated: two per-vertex factors exceed 1."""
import importlib.util
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.collective_cancellation import per_vertex_factor, hub_factor, near_star_balance  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_cc_gen", ROOT / "examples" / "bg_collective_cancellation" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_two_factors_exceed_one_but_product_is_one():
    leaf, mid, hub = gen._facts()
    assert leaf < 1 < hub and mid > 1          # two of three per-vertex factors > 1
    assert leaf ** 5 * mid ** 5 * hub == 1      # yet the full 11-vertex product = 1
    assert near_star_balance(5) == 1           # = the tie's Phi^11


def test_no_all_sub_unit_decomposition():
    # the obstruction: since a per-vertex factor exceeds 1, no all-<=1 per-vertex
    # decomposition (no sum of non-positive local terms) can bound Phi^11.
    leaf, mid, hub = gen._facts()
    assert any(f > 1 for f in (leaf, mid, hub))


def test_emitted_shape_and_scope():
    src = gen.build()
    assert "namespace BGCollectiveCancellation" in src
    assert src.rstrip().endswith("end BGCollectiveCancellation")
    assert "conjecture1_proved = False" in src and "does NOT prove the crux" in src
    for name in ("pvf_leaf_sub_unit", "pvf_hub_excess", "pvf_armmid_excess", "tie_collective_balance"):
        assert name in src
    assert src.count("by norm_num") == 4


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_collective_cancellation" / "frozen" / "BGCollectiveCancellation.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
