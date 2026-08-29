"""TightLogCertificate wired into BG: regenerates R3Cert/Sweep.lean's log enclosures."""
import importlib.util
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from telperion.tight_log import TightLogCertificate  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "bg_log_gen", ROOT / "examples" / "bg_log_enclosures" / "generate.py"
)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def test_reproduces_bg_windows_exactly():
    # BG's Sweep.lean: 405/1000 < log(3/2) < 406/1000 and 287/1000 < log(4/3) < 288/1000
    for nm, n, d, (blo, bhi) in [
        ("log_three_half_enclosure", 3, 2, (405, 406)),
        ("log_four_third_enclosure", 4, 3, (287, 288)),
    ]:
        src = TightLogCertificate(name=nm, n=n, d=d).lean()
        assert f"({blo} : ℝ) / 1000 < Real.log (({n} : ℝ) / {d})" in src
        assert f"Real.log (({n} : ℝ) / {d}) < ({bhi} : ℝ) / 1000" in src


def test_coarse_cannot_but_tight_can():
    # the coarse LogBoundCertificate bracket [1-d/n, n/d-1] for 3/2 is [1/3, 1/2] --
    # far wider than BG's [0.405, 0.406]; the tight cert contains the true value tightly.
    c = TightLogCertificate(name="x", n=3, d=2)
    lo, hi = c.bracket()
    v = math.log(3 / 2)
    assert float(lo) < v < float(hi)
    assert float(hi) - float(lo) <= 0.001 + 1e-12  # /1000 grid, vs coarse ~0.167


def test_rejects_non_23_basis():
    import pytest  # noqa
    for n, d in [(5, 1), (7, 2), (1, 5)]:
        try:
            TightLogCertificate(name="x", n=n, d=d).lean()
            assert False, f"should reject {n}/{d}"
        except ValueError:
            pass


def test_emitted_lean_shape():
    src = gen.build()
    assert "namespace BGLogEnclosures" in src and src.rstrip().endswith("end BGLogEnclosures")
    # uses the same Mathlib decimal constants + tactics BG's sweep proof uses
    for lem in ("Real.log_two_gt_d9", "Real.log_three_lt_d9", "Real.log_div", "nlinarith"):
        assert lem in src


def test_frozen_matches_generated():
    frozen = ROOT / "examples" / "bg_log_enclosures" / "frozen" / "BGLogEnclosures.lean"
    assert frozen.exists(), "run generate.py to freeze"
    assert frozen.read_text() == gen.build(), "frozen drift; re-run generate.py"
