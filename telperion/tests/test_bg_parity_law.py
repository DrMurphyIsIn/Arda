"""The per-n extremality parity law, kernel-gated: exact extremal Phi^11 values (n<=14)."""
import importlib.util
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.multi_hub_extremality import phi_maximizer, is_near_star  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_parity_gen", ROOT / "examples" / "bg_parity_law" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_parity_law_structure_and_bound():
    # near-star wins iff n odd; max <= 1 with equality only at n=11
    for n in gen.NS:
        phi, edges = phi_maximizer(n)
        assert is_near_star(n, edges) == (n % 2 == 1)
        assert phi <= 1
        assert (phi == 1) == (n == 11)


def test_emitted_facts_match_python():
    src = gen.build()  # one full sweep; reused across all n
    for n, phi, ns in gen._facts():
        P, Q = phi.numerator, phi.denominator
        if n == 11:
            assert f"bg_extremum_n11 : (({P} : ℚ) / {Q}) = 1" in src
        else:
            assert f"bg_extremum_n{n} : (({P} : ℚ) / {Q}) < 1" in src


def test_emitted_shape_and_scope():
    src = gen.build()
    assert "namespace BGParityLaw" in src and src.rstrip().endswith("end BGParityLaw")
    assert "exhaustive" in src.lower() and "conjecture1_proved = False" in src
    # exactly one tie (=1) and the rest strict (<1)
    assert src.count(") = 1 := by norm_num") == 1
    assert src.count(") < 1 := by norm_num") == len(list(gen.NS)) - 1


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_parity_law" / "frozen" / "BGParityLaw.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
