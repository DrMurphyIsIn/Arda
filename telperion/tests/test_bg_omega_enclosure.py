"""Taylor-log + d9 wired into BG: regenerates R3Cert/Sweep.lean's omega_enclosure."""
import importlib.util
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.taylor_log import TaylorLogNear1Certificate  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_omega_gen", ROOT / "examples" / "bg_omega_enclosure" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_taylor_bracket_contains_log_23_24():
    c = TaylorLogNear1Certificate(name="t", k=24, degree=4)
    assert c.check()
    assert c.remainder() == Fr(1, 7630848)  # matches BG's omega proof
    lo, hi = c.bracket()
    v = math.log(1 - 1 / 24)
    assert float(lo) <= v <= float(hi)
    assert float(hi) - float(lo) < 1e-6  # degree-4 remainder is ~1.3e-7


def test_omega_window_matches_bg():
    # BG's Sweep.lean: -78/10000 < omega < -77/10000
    tay = TaylorLogNear1Certificate(name="t", k=24, degree=4)
    lo, hi = gen._window(tay)
    assert (lo, hi) == (Fr(-78, 10000), Fr(-77, 10000))


def test_emitted_omega_shape():
    src = gen.build()
    assert "namespace BGOmegaEnclosure" in src and src.rstrip().endswith("end BGOmegaEnclosure")
    assert "(-78 : ℝ) / 10000 <" in src and "< (-77 : ℝ) / 10000" in src
    # uses the same Mathlib machinery as BG's omega proof
    for lem in ("Real.log_two_gt_d9", "Real.abs_log_sub_add_sum_range_le", "abs_le", "nlinarith"):
        assert lem in src


def test_rejects_bad_params():
    for k, deg in [(1, 4), (24, 0)]:
        try:
            TaylorLogNear1Certificate(name="t", k=k, degree=deg).lean()
            assert False, f"should reject k={k} deg={deg}"
        except ValueError:
            pass


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_omega_enclosure" / "frozen" / "BGOmegaEnclosure.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
