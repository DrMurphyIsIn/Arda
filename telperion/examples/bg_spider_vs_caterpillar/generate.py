"""Generate the BG spider-beats-caterpillar certificate (kernel-gated).

    python examples/bg_spider_vs_caterpillar/generate.py [--check]

Part (ii) of the broom-dominance reduction (see `docs/BG_ARITHMETIC_VS_COMBINATORIAL_20260831.md`): the exchange
analysis shows every rich-exchange local maximum of `rho` is the broom (spider) or a length-2 caterpillar, so
broom dominance reduces to the spider beating every caterpillar.  Asymptotically that is `F* > F(a)`, `F* =
log(621/64)/11` (spider), `F(a) = log(lam(a))/(2a+1)` (uniform caterpillar, `lam(a)` the transfer-matrix Perron
surd).  `SpiderBeatsCaterpillarCertificate` clears the logs to `(621/64)^(2a+1) > lam(a)^11 = A + B sqrt(D)` and
emits the surd-cleared rational atoms `L>A`, `B>0`, `(L-A)^2 > B^2 D` (exactly equivalent to `L > lam^11`) for
`a=1..12`, covering the caterpillar sup `a=7`.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.transfer_caterpillar import SpiderBeatsCaterpillarCertificate  # noqa: E402

_CERT = SpiderBeatsCaterpillarCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGSpiderBeatsCaterpillar.lean"


def build() -> str:
    assert _CERT.check(), "spider-beats-caterpillar certificate does not hold"
    head = (
        "/- BG spider beats caterpillar (kernel-gated) -- part (ii) of the broom-dominance reduction.\n"
        "   F* > F(a) (spider free energy beats every uniform caterpillar), F*=log(621/64)/11,\n"
        "   F(a)=log(lam(a))/(2a+1), lam(a)=(t+sqrt(D))/2 the transfer Perron surd. Cleared to\n"
        "   (621/64)^(2a+1) > lam^11 = A+B sqrt(D) via the rational atoms L>A, B>0, (L-A)^2>B^2 D\n"
        "   (together <=> L>lam^11), a=1..12 (sup at a=7; F(a) decreases to log(3/2)/2<F*).\n"
        "   conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGSpiderBeatsCaterpillar")


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
