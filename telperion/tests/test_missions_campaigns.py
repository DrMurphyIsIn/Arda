"""The real campaigns' invariants run in CI: a hand-edited status cannot pass.

The design's central promise is that the registry never claims more than CI
can re-check (spec section 7). The fixture-only tests cover the machinery;
these cover the DATA.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.missions.verify import verify_campaign  # noqa: E402

MISSIONS = Path(__file__).resolve().parents[1] / "missions"


def test_bg_campaign_invariants_hold():
    report = verify_campaign(MISSIONS / "bg")
    assert report.ok, f"errors={report.errors} warnings={report.warnings}"


def test_rh_campaign_invariants_hold():
    report = verify_campaign(MISSIONS / "rh")
    assert report.ok, f"errors={report.errors} warnings={report.warnings}"
