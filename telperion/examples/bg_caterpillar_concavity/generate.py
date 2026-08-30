"""Generate the BG caterpillar density concavity + strict-max certificate (route-b piece 2, kernel-gated).

    python examples/bg_caterpillar_concavity/generate.py           # write lean/BGCaterpillarConcavity.lean
    python examples/bg_caterpillar_concavity/generate.py --check    # drift check (no write)

F(a) = the infinite length-2-arm caterpillar cavity (Bethe) free-energy density with a arms per hub -- the
k=0 "phonon" direction of the structural Hessian (the arm-count knife-edge).  rho* = exp(max_a F(a)), and the
maximizer is the ~7-arm caterpillar.  This example kernel-gates two facts about F(a):

  (max)      a=7 STRICTLY maximizes F over integer arm-counts:  F(7) > F(6),  F(7) > F(8);
  (concave)  F is concave at the max:  F(a-1) + F(a+1) < 2 F(a)  for a = 6,7,8.

Combined with monomer-dimer STRONG SPATIAL MIXING (Bayati-Gamarnik-Katz-Nagaraj-Tetali, STOC 2007 -- uniform
correlation decay), which gaps every non-k=0 phonon mode BELOW this one, these certify the caterpillar as a
strict LOCAL max of the free-energy density in every structural direction (route-b W15-W20 fusion).  NOT the
full BG proof -- the global step (no distant competitor max) remains.  conjecture1_proved = False.

The F(a) values are transcendental (logs of quadratic surds from the exact cavity fixed point); the certificate
CONSUMES rigorous rational enclosures F(a) in [lo_a, hi_a] (derived offline by 80-digit interval numerics --
the transcendental import, exactly the turan/jensen/hankel trust model) and kernel-gates the rational
inequalities between them by `norm_num`.  Enclosure half-width ~1e-15; the concavity margins are ~1e-5.
"""
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMESPACE = "BGCaterpillarConcavity"
_OUT = Path(__file__).resolve().parent / "lean" / "BGCaterpillarConcavity.lean"

# FROZEN rigorous rational enclosures  F(a) in [LO[a], HI[a]]  (80-digit interval numerics; denom 1e18)
LO = {
    5: Fr(204904997586507802, 10**18), 6: Fr(205060572941684843, 10**18),
    7: Fr(205098366921379213, 10**18), 8: Fr(205075579671531362, 10**18),
    9: Fr(205021655854407260, 10**18),
}
HI = {
    5: Fr(204904997586507805, 10**18), 6: Fr(205060572941684846, 10**18),
    7: Fr(205098366921379216, 10**18), 8: Fr(205075579671531365, 10**18),
    9: Fr(205021655854407263, 10**18),
}


def _rat(f: Fr) -> str:
    return f"(({f.numerator} : ℚ)/{f.denominator})"


def atoms():
    """List of (name, lhs, rhs) with the certified strict inequality lhs < rhs."""
    out = [("bg_cat_max_a7_gt_a6", HI[6], LO[7]),        # F(6) < F(7)
           ("bg_cat_max_a7_gt_a8", HI[8], LO[7])]        # F(8) < F(7)
    for a in (6, 7, 8):                                   # concavity: F(a-1)+F(a+1) < 2 F(a)
        out.append((f"bg_cat_concave_a{a}", HI[a - 1] + HI[a + 1], 2 * LO[a]))
    return out


def build() -> str:
    for nm, lhs, rhs in atoms():
        assert lhs < rhs, f"{nm}: enclosure inequality fails ({lhs} < {rhs})"
    head = (
        "/- BG caterpillar density concavity + strict max at a=7 (route-b piece 2, kernel-gated).\n"
        "   F(a) = infinite length-2-arm caterpillar cavity free-energy density (a arms/hub); the k=0 phonon\n"
        "   knife-edge. rho* = exp(max_a F(a)), maximizer ~7-arm caterpillar. Enclosures from rigorous 80-digit\n"
        "   interval numerics (transcendental import, turan/jensen model). Atoms: a=7 strictly maximizes F over\n"
        "   integer arm-counts, and F is concave (a=6,7,8). With monomer-dimer strong spatial mixing (BGKNT 2007)\n"
        "   gapping every non-k=0 mode, these certify a strict LOCAL max in every structural direction.\n"
        "   NOT a proof of Brualdi-Goldwasser (the global no-competitor step remains). conjecture1_proved = False. -/\n"
        "import Mathlib\n\n"
        f"namespace {NAMESPACE}\n\n"
    )
    body = "\n".join(f"theorem {nm} : {_rat(lhs)} < {_rat(rhs)} := by norm_num" for nm, lhs, rhs in atoms())
    return head + body + f"\n\nend {NAMESPACE}\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        if cur != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py"); return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches"); return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
