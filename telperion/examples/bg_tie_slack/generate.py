"""Generate the BG slack-regime bound certificate (upper-bound campaign, kernel-gated).

    python examples/bg_tie_slack/generate.py [--check]

The branch-induction upper bound is `ell(hub) <= 0` for all `k`.  For `k >= 16` (the SLACK regime, covering
MIXED hubs) this follows from `slack_g(k) <= F*` (via `log(1+Sum x) <= Sum x`).  See
`docs/BG_TIE_REGIME_CAMPAIGN_20260831.md`.  `TieSlackCertificate` emits the rational atoms (frozen log-enclosures,
concavity/turan trust model) proving `slack_g(k) <= F*` for `k >= 16`:
  (A) `slack_g(16) < F*` -- per envelope child, `176 L(total)+11(h/d)(16/17) < (16|c|+1) L(621/64)`;
  (B) `dphi_c/dk|_16 < 0` (non-B(5)) -- so `slack_g(k) <= slack_g(16)` for `k >= 16`;
  (C) `F* > 3/23` -- the `B(5)` limit.
NOT the full bound (`mixed <= B(k)` for `k <= 15` + the envelope-dominance reduction remain, all tie-free).
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import TieSlackCertificate  # noqa: E402

_CERT = TieSlackCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGTieSlack.lean"


def build() -> str:
    assert _CERT.check(), "slack certificate does not hold"
    head = (
        "/- BG slack-regime bound (upper-bound campaign, kernel-gated).\n"
        "   For k>=16 (slack regime, covers MIXED hubs) ell(hub)<=slack_g(k)-F*<=0. slack_g(k)<=F* via frozen\n"
        "   log-enclosures: (A) slack_g(16)<F* per envelope child; (B) dphi_c/dk|_16<0 (non-B(5)) => slack_g(k)\n"
        "   <=slack_g(16); (C) F*>3/23 (B(5) limit). NOT the full bound (mixed<=B(k), k<=15, + envelope-dominance\n"
        "   remain, tie-free). conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGTieSlack")


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true"); a = ap.parse_args()
    src = build()
    if a.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        print("ok: matches" if cur == src else "DRIFT: re-run generate.py")
        return 0 if cur == src else 1
    _OUT.parent.mkdir(parents=True, exist_ok=True); _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}"); return 0


if __name__ == "__main__":
    sys.exit(main())
