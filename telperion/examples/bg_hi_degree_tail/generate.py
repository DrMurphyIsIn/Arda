"""Generate the BG high-degree envelope-tail certificate (upper-bound campaign, kernel-gated).

    python examples/bg_hi_degree_tail/generate.py [--check]

The mixed-hub reduction (`bg_mixed_kkt`) leaves the per-child envelope tail `V(c) <= V(cherry)` for ALL branches,
`V(c) = ell(c) + lambda(k) x_c`.  HIGH-degree branches close cleanly using only the ceiling `ell(c) <= 0` and
`h_c <= 1`: for `d_c >= 7`, `V(c) <= lambda(k)/(7(k+1)) < V(cherry)`, i.e. the rational-cleared inequality
`-44/(7(4k+3)) < 11 ell(cherry) = 11 log(3/2) - 2 log(621/64)`.  So the OPEN part of the tail shrinks to
small-degree (`d_c <= 6`) branches (brooms `B(2..5)` gated by `bg_mixed_kkt`; residual = small-degree non-broom).
See `docs/BG_MIXED_KKT_20260831.md`.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import HighDegreeTailCertificate  # noqa: E402

_CERT = HighDegreeTailCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGHighDegreeTail.lean"


def build() -> str:
    assert _CERT.check(), "high-degree tail certificate does not hold"
    head = (
        "/- BG high-degree envelope-tail (upper-bound campaign, kernel-gated).\n"
        "   Per-child envelope V(c)=ell(c)+lambda(k) x_c <= V(cherry). For d_c>=7, using only ell(c)<=0 and\n"
        "   h_c<=1, V(c) <= lambda(k)/(7(k+1)) < V(cherry), i.e. -44/(7(4k+3)) < 11 ell(cherry) =\n"
        "   11 log(3/2)-2 log(621/64) (RHS lower-bounded by frozen log-enclosures). Shrinks the open envelope\n"
        "   tail to small-degree d_c<=6 branches. conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGHighDegreeTail")


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
