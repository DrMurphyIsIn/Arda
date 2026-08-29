"""TightRobinCertificate: Robin's inequality at the RH-tight superabundant regime."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import TightRobinCertificate  # noqa: E402

SA = [10080, 15120, 25200, 27720, 55440, 110880, 166320,
      277200, 332640, 554400, 665280, 720720, 1441440]


def test_all_13_superabundant_in_range_certify():
    # every superabundant number in (5040, 2e6] closes the tight arithmetic
    for n in SA:
        c = TightRobinCertificate.for_superabundant(n)
        assert c.check(), n
        assert c.sigma() < c.egamma_lo * n * c.loglog_lo


def test_recipe_is_a_valid_lower_bracket():
    import math
    c = TightRobinCertificate.for_superabundant(10080)
    # egamma_lo is a genuine lower bound on e^gamma; loglog_lo on log log n
    assert float(c.egamma_lo) <= math.exp(0.5772156649) + 1e-9
    assert float(c.loglog_lo) <= math.log(math.log(10080)) + 1e-9


def test_n25200_matches_named_builder():
    a = TightRobinCertificate.for_n25200()
    b = TightRobinCertificate.for_superabundant(25200, name="robin_tight_n25200")
    assert a.lean() == b.lean()


def test_lean_emits_unconditional_theorem():
    lean = TightRobinCertificate.for_superabundant(166320).lean()  # b2=2 recipe shape
    assert "theorem robin_tight_n166320" in lean
    assert "eulerMascheroniSeq" in lean and "abs_log_sub_add_sum_range_le" in lean
    # no free hypotheses (unconditional)
    assert "theorem robin_tight_n166320 :\n" in lean
