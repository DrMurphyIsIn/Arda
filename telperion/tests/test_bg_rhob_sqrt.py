"""sqrt_bracket wired into BG: regenerates the sqrt 2 bracket of e2_two_rhoB_gt."""
import importlib.util
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

_spec = importlib.util.spec_from_file_location(
    "bg_rhob_sqrt_gen", ROOT / "examples" / "bg_rhob_sqrt" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_coarse_cert_is_bgs_exact_bound():
    # BG hand-writes `Real.sqrt 2 < 17/12`; the cert regenerates 1 <= sqrt2 <= 17/12.
    c = gen._cert_coarse()
    assert c.check()
    assert (c.lo, c.hi) == (Fr(1), Fr(17, 12))
    assert c.hi ** 2 == Fr(289, 144) > 2  # (17/12)^2 clears 2, so sqrt2 <= 17/12


def test_bracket_composes_to_e2_crux():
    # The <= bracket composes with rhoB > 29/24 (strict) to give BG's strict 1+sqrt2 < 2 rhoB:
    #   1 + sqrt2 <= 1 + 17/12 = 29/12 = 2*(29/24) < 2*rhoB.
    hi = gen._cert_coarse().hi
    assert 1 + hi == Fr(29, 12) == 2 * Fr(29, 24)


def test_tight_cert_valid():
    assert gen._cert_tight().check()


def test_emitted_lean_shape():
    src = gen.build()
    assert "namespace BGRhoBSqrt" in src and src.rstrip().endswith("end BGRhoBSqrt")
    assert "theorem bg_rhob_e2_sqrt2 :" in src
    assert "Real.sqrt ((2 : ℝ) / 1) ≤ (17 : ℝ) / 12" in src
    # kernel-discharge tactics BG's own proof also uses
    assert "Real.sqrt_sq" in src and "Real.sqrt_le_sqrt" in src


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_rhob_sqrt" / "frozen" / "BGRhoBSqrt.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
