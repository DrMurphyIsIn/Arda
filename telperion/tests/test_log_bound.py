"""Transcendental log-bound certificate: 1 - d/n <= log(n/d) <= n/d - 1."""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import LogBoundCertificate  # noqa: E402


def test_bracket_contains_log_across_a_range():
    for n, d in [(3, 2), (5, 1), (7, 4), (100, 99), (1, 2), (22, 7), (271, 100)]:
        c = LogBoundCertificate(name=f"log_{n}_{d}", n=n, d=d)
        assert c.check()
        lo, hi = c.bracket()
        assert float(lo) <= math.log(n / d) <= float(hi)
        assert lo <= hi


def test_bracket_is_exact_convex_bounds():
    c = LogBoundCertificate(name="log_5_1", n=5, d=1)
    lo, hi = c.bracket()
    assert lo == 1 - Fr(1, 5)          # 1 - d/n
    assert hi == Fr(5, 1) - 1          # n/d - 1


def test_tight_at_one_loose_far_away():
    near = LogBoundCertificate(name="n", n=101, d=100)
    far = LogBoundCertificate(name="f", n=10, d=1)
    nlo, nhi = near.bracket(); flo, fhi = far.bracket()
    assert float(nhi - nlo) < 0.001            # coarse bound is tight near q=1
    assert float(fhi - flo) > 5                 # ... and loose far away (honest)


def test_lean_shape():
    c = LogBoundCertificate(name="log_bound_demo", n=22, d=7)
    lean = c.lean()
    assert "theorem log_bound_demo" in lean
    assert "Real.log" in lean
    assert "Real.log_le_sub_one_of_pos" in lean    # the Mathlib lemma it rests on
    assert "Real.log_inv" in lean


def test_bad_inputs_refused():
    with pytest.raises(ValueError, match="refusing to emit"):
        LogBoundCertificate(name="bad", n=-3, d=2).lean()
