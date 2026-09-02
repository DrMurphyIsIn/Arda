"""Generate the BG broom-vs-cherry-on-I certificate (extremality assembly leg #4, kernel-gated).

    python examples/bg_broom_vs_cherry/generate.py [--check]

The single-child lemma's joint induction needs the reference broom to beat the cherry in V_mu UNIFORMLY on the
invariant price interval I=[456/3703,3/7]: V_mu(B(j)) <= V_mu(cherry) for every broom child of degree <= 6
(j=1..5; degree>=7 is bg_high_degree_tail). Linear in mu, so both endpoints A,B suffice. Cleared (x11,
11 F*=log(621/64)) with the exact-rational mu-term: 11 L(total B(j))-11 L(3/2)-(2j-1) L(621/64) < 11 mu(1/3-y_Bj),
LHS by frozen log-enclosures. See docs/BG_EXTREMALITY_ASSEMBLY_20260902.md. conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import BroomVsCherryOnICertificate  # noqa: E402

_CERT = BroomVsCherryOnICertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGBroomVsCherry.lean"


def build() -> str:
    assert _CERT.check(), "broom-vs-cherry-on-I certificate does not hold"
    head = (
        "/- BG extremality assembly leg #4: broom-vs-cherry on the invariant price interval I=[456/3703,3/7].\n"
        "   V_mu(B(j)) <= V_mu(cherry) for broom children of degree <= 6 (j=1..5) and all mu in I (linear in mu,\n"
        "   so both endpoints A,B). Atoms (frozen log-enclosures): 11 L(total B(j))-11 L(3/2)-(2j-1) L(621/64)\n"
        "   < 11 mu (1/3 - y_Bj). Reference-broom leg of the single-child induction. conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGBroomVsCherry")


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
