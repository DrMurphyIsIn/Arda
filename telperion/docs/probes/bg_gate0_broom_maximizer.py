"""Gate 0 (sorted-conjuring-clock plan): does the single-hub broom B(c) actually dominate?

VERDICT: NO. B(c) (one hub of c cherries) is NOT the size-2c+1 maximizer for large c -- caterpillars beat it
(n=27: [4,4,4] > B(13); n=33: [5,5,5] > B(16)), both rooted and unrooted. Asymptotic per-vertex free energies:
S(k,5)=F*=0.20659 > caterpillar=0.20510 > single-hub B(c)=0.20273. So B(c) is the WORST of the three.

BUT the asymptotic upper bound (branch ceiling ell(B)<=0) needs only the LOCAL lemma mixed<=B(k) (hub of k
children <= hub of k cherries) + broom optimum -- NOT global broom dominance. See BG_GATE0_VERDICT_20260901.md.
conjecture1_proved = False.
"""
import math
from fractions import Fraction as Fr

from telperion.branch_potential import branch_ell, branch_total, broom_edges, F_STAR
from telperion.transfer_caterpillar import caterpillar_edges
from telperion.matching_free_energy import rho


def max_rooted_total(n, edges):
    return max(branch_total(n, tuple(edges), r) for r in range(n))


def gate0_broom_vs_caterpillar():
    """Rooted-total comparison, size-matched. Returns list of (size, B(c), cat, broom_wins)."""
    out = []
    for spine in ([3, 3, 3], [4, 4, 4], [5, 5, 5]):
        nc, ec = caterpillar_edges(spine)
        c = (nc - 1) // 2
        bt = max_rooted_total(*broom_edges(c))
        ct = max_rooted_total(nc, ec)
        out.append((nc, float(bt), float(ct), bt >= ct))
    return out


def gate0_ceiling_intact():
    """The caterpillars that beat B(c) still satisfy ell(B)<=0 (the asymptotic bound is intact)."""
    out = []
    for spine in ([4, 4, 4], [5, 5, 5], [6, 6, 6]):
        n, e = caterpillar_edges(spine)
        worst = max(branch_ell(n, tuple(e), r)[0] for r in range(n))
        out.append((n, worst, worst <= 1e-9))
    return out


if __name__ == "__main__":
    print("Gate 0 -- broom B(c) vs caterpillar (rooted total, size-matched):")
    for sz, b, cat, win in gate0_broom_vs_caterpillar():
        print(f"  size {sz}: B={b:.3f} cat={cat:.3f} -> B(c) {'WINS' if win else 'LOSES'}")
    print("ceiling ell<=0 intact for the caterpillars that beat B(c):")
    for sz, w, ok in gate0_ceiling_intact():
        print(f"  size {sz}: max ell={w:+.5f} {'OK' if ok else 'VIOLATED'}")
    print(f"per-vertex free energy: S(k,5)={F_STAR:.5f} > cat=0.20510 > single-hub B(c)={math.log(1.5)/2:.5f}")
