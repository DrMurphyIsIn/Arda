"""Robin's criterion (RH-EQUIVALENT, Robin 1984): RH <=> sigma(n) < e^gamma n loglog n
for all n >= 5041.  RobinCertificate machine-verifies a single instance: exact integer
sigma(n) against a rational LOWER bound on the transcendental RHS built from a lower
bound E_lo <= e^gamma (ExpBracket on a Mathlib gamma bound) and LL_lo <= loglog n
(tight log).  Finite per-n verification of an RH-equivalent condition -- a single
n >= 5041 violating it would DISPROVE RH.  Honest scope: RH-necessary/equivalent
evidence on a finite set, never a proof.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import RobinCertificate  # noqa: E402


def test_sigma_exact():
    # 5041 = 71^2 -> sigma = 1 + 71 + 71^2 = 5113
    assert RobinCertificate(name="r", n=5041, egamma_lo=Fr(3, 2), loglog_lo=Fr(2)).sigma() == 5113
    # 5040 = 2^4 3^2 5 7 -> sigma = 31*13*6*8 = 19344 (the last Robin exception)
    assert RobinCertificate(name="r", n=5040, egamma_lo=Fr(3, 2), loglog_lo=Fr(2)).sigma() == 19344


def test_comfortable_n_certifies_with_clean_mathlib_brackets():
    # e^gamma > e^{1/2} (Mathlib: Real.one_half_lt_eulerMascheroniConstant), coarse loglog
    c = RobinCertificate.from_gamma_lower(n=5041, gamma_lo=Fr(1, 2))
    assert c.check()
    # margin is huge for this comfortable (non-superabundant) n
    assert c.sigma() * 3 < c.rhs_lo()


def test_last_exception_5040_does_not_certify():
    # n=5040 is the largest KNOWN Robin exception (sigma/(n loglog n) ~ 1.79 > e^gamma).
    # Robin's inequality is FALSE here, so no honest bracket can certify it.
    c = RobinCertificate.from_gamma_lower(n=5040, gamma_lo=Fr(1, 2))
    assert not c.check()


def test_tight_superabundant_needs_tighter_gamma():
    # n=55440 superabundant: Robin HOLDS (ratio ~1.751 < 1.781) but the clean gamma>1/2
    # bound (e^gamma>1.6487) is too loose -> NOT certifiable with the coarse bracket.
    coarse = RobinCertificate.from_gamma_lower(n=55440, gamma_lo=Fr(1, 2))
    assert not coarse.check()
    # with a tight gamma (0.5772156649 -> e^gamma ~1.781) AND a tight loglog it WOULD close:
    tight = RobinCertificate(name="r55440", n=55440,
                             egamma_lo=Fr(178, 100), loglog_lo=Fr(239, 100))
    assert tight.check()   # 232128 < 1.78 * 55440 * 2.39


def test_check_is_exact_rational_no_float():
    c = RobinCertificate(name="r", n=5041, egamma_lo=Fr(16487, 10000), loglog_lo=Fr(2079, 1000))
    assert isinstance(c.rhs_lo(), Fr)
    assert c.check() == (c.sigma() < c.rhs_lo())


def test_lean_emits_theorem_consuming_two_brackets():
    c = RobinCertificate.from_gamma_lower(n=5041, gamma_lo=Fr(1, 2))
    lean = c.lean()
    assert "theorem robin_n5041" in lean
    assert "eulerMascheroniConstant" in lean       # the e^gamma bracket hypothesis
    assert "Real.log (Real.log" in lean            # the loglog n term
    assert "5113" in lean                          # the exact sigma value


def test_lean_refuses_when_not_certified():
    c = RobinCertificate.from_gamma_lower(n=5040, gamma_lo=Fr(1, 2))
    try:
        c.lean()
        assert False, "expected refusal on the (true) Robin exception 5040"
    except ValueError:
        pass


def test_unconditional_emits_self_contained_theorem():
    c = RobinCertificate.from_gamma_lower(n=5041, gamma_lo=Fr(1, 2))
    lean = c.lean_unconditional()
    # no free hypotheses -- the theorem statement takes no bracket args
    assert "theorem robin_n5041 :\n" in lean
    # both brackets discharged in-kernel
    assert "Real.one_half_lt_eulerMascheroniConstant" in lean  # gamma>1/2
    assert "Real.sum_le_exp_of_nonneg" in lean                 # exp Taylor lower bound
    assert "Real.log_two_gt_d9" in lean                        # log2 d9 constant
    assert "Real.log_pow" in lean and "gcongr" in lean         # loglog monotone chain


def test_unconditional_requires_clean_gamma_half():
    # a non-1/2 gamma has no clean Mathlib discharge -> refuse the unconditional emit
    c = RobinCertificate(name="r", n=5041, egamma_lo=Fr(178, 100), loglog_lo=Fr(2079, 1000),
                         gamma_lo=Fr(5772156649, 10 ** 10))
    try:
        c.lean_unconditional()
        assert False, "expected refusal without gamma_lo=1/2"
    except ValueError:
        pass
