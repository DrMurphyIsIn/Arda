"""Kernel-gated 23-gate-strictness anchor: the emitted Lean regenerates the deficit facts."""
import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.gate_strictness import deficit_23_valuation, deficit_integer  # noqa: E402
from telperion.frustration_free import tie_recursive_edges  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_gate_gen", ROOT / "examples" / "bg_gate_strictness" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_deficit_integers_positive_and_23_linear_growth():
    # the facts the Lean gates: M_k > 0 (non-tie strict) and v_23(M_k) = 11(k-1)
    for k in gen.KS:
        n, e = tie_recursive_edges(k)
        M, _ = deficit_integer(n, e, 0)
        assert M > 0
        assert deficit_23_valuation(n, e, 0) == 11 * (k - 1)


def test_emitted_facts_match_python():
    # every big-integer literal in the emitted Lean is exactly the Python deficit integer
    for k, n, M, v, lo_div, hi_div in gen._facts():
        assert lo_div == 23 ** v and hi_div == 23 ** (v + 1)
        assert M % lo_div == 0 and M % hi_div != 0  # v_23(M) = v, exactly
        assert f"deficit_pos_k{k} : (0 : ℤ) < {M}" in gen.build()
        assert f"(({lo_div} : ℤ) ∣ {M})" in gen.build()


def test_emitted_lean_shape_and_scope():
    src = gen.build()
    assert "namespace BGGateStrictness" in src and src.rstrip().endswith("end BGGateStrictness")
    assert "does NOT prove the open <= half" in src
    assert src.count("by norm_num") == 2 * len(gen.KS)  # pos + v23 per level


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_gate_strictness" / "frozen" / "BGGateStrictness.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
