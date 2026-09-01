"""Generate the BG smooth no-go / integrality-gap certificate (kernel-gated).

    python examples/bg_smooth_nogo/generate.py [--check]

The broom per-vertex free energy `f(c) = log(total(c))/(2c+1)` is maximised over INTEGER `c` at `c=5`
(`f(5) = F* = log(621/64)/11`), but its CONTINUOUS relaxation overshoots: `f(24/5) > F*`.  Hence any certificate
that relaxes the integer arm-count (convex / SOS / moment / tangent / spectral -- everything smooth) is bounded
below by `f(c*) > F*` and CANNOT prove the BG upper bound `F(T) <= F*`.  `SmoothNoGoCertificate` emits the single
rational-log atom (frozen log-enclosures) proving `f(24/5) > F*`.  See `docs/BG_INTEGRALITY_GAP_20260831.md`.
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.spider_broom import SmoothNoGoCertificate  # noqa: E402

_CERT = SmoothNoGoCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGSmoothNoGo.lean"


def build() -> str:
    assert _CERT.check(), "smooth no-go certificate does not hold"
    head = (
        "/- BG smooth no-go / integrality gap (kernel-gated).\n"
        "   The continuous broom free energy f(c)=log(total(c))/(2c+1) overshoots the INTEGER optimum F* at\n"
        "   c0=24/5: 209 L(3/2)+55 L(111/5)-55 L(2)-55 L(29/5) > 53 L(621/64) (cleared f(24/5)>F*, frozen\n"
        "   log-enclosures). So NO smooth (relaxation-based) certificate can prove F(T)<=F* -- the BG optimum is\n"
        "   an integer-program optimum (rational 621/64, prime 4*5+3=23) with a positive integrality gap; the\n"
        "   closing argument must be arithmetic. conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGSmoothNoGo")


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
