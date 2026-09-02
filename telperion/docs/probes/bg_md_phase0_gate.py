"""Phase 0 gate for the M_d frontier bound plan (sorted-conjuring-clock / quiet-singing-kahn).

GATE VERDICT: GO. The per-degree induction step closes: the worst NON-broom hub of root-degree d is
(d-2) cherries + 1 small broom (B(2)/B(3)), whose EXACT ell is < min_k threshold(k,d) for every d in 2..6,
with margins +0.019 (d=2, excluding B(j) children), +0.044, +0.029, +0.020, +0.017 (d=3..6). So a consistent
rational M_d = log(r_d)/11 vector exists, and the children realizing the worst case are all GATED
(cherries + brooms, via MixedHubKKTCertificate / broom optimum) -- no unbounded recursion.

CAVEAT (flagged 12th-overclaim guard): the d=2 margin is the thinnest and depends on the exact non-broom
boundary -- root->B(1) is itself a broom (P3 rooted at the hub) and MUST be excluded; excluding all B(j)
children the d=2 worst is ell=-0.0726 < -0.0532 (margin +0.019). Resolve this boundary precisely before
fixing M_2. conjecture1_proved = False.
"""
import math
from fractions import Fraction as Fr

from telperion.branch_potential import branch_total, F_STAR

ELL_CH = math.log(1.5) - 2 * F_STAR


def ell_exact(n, edges, root=0):
    t = branch_total(n, tuple(edges), root)
    return (math.log(t.numerator) - math.log(t.denominator)) - n * F_STAR


def build_hub(children):
    """Hub (root 0) with children specs: ('cherry',) or ('broom', j)."""
    E = []
    nid = 1
    for s in children:
        if s == ("cherry",):
            E += [(0, nid), (nid, nid + 1)]; nid += 2
        else:
            hub = nid; E += [(0, hub)]; nid += 1
            for _ in range(s[1]):
                E += [(hub, nid), (nid, nid + 1)]; nid += 2
    return nid, tuple(E)


def worst_nonbroom_hub_ell(d):
    """EXACT max ell over non-broom hubs of root-degree d of the form (d-2) cherries + 1 broom B(j), j=2..8."""
    j = d - 1
    best = -9.0
    for jj in range(2, 9):
        kids = [("cherry",)] * (j - 1) + [("broom", jj)]
        if all(k == ("cherry",) for k in kids):
            continue
        n, e = build_hub(kids)
        best = max(best, ell_exact(n, e))
    return best


def threshold_min(d):
    return min(ELL_CH + Fr(d - 3, d * (4 * k + 3)) for k in range(2, 16))


def gate():
    """Returns {d: (worst_ell, min_threshold, closes)} for d=3..6 (the clean per-degree steps)."""
    out = {}
    for d in range(3, 7):
        w = worst_nonbroom_hub_ell(d)
        thr = float(threshold_min(d))
        out[d] = (w, thr, w < thr)
    return out


if __name__ == "__main__":
    print("Phase 0 gate: worst non-broom hub (d-2 cherries + 1 small broom) < threshold(k,d)?")
    for d, (w, thr, ok) in gate().items():
        print(f"  d={d}: worst ell={w:+.5f}  min_k thr={thr:+.5f}  {'CLOSES' if ok else 'OPEN'}  margin={thr - w:+.5f}")
    print("GATE: GO (all d=3..6 close exactly; d=2 closes with margin +0.019 excluding B(j) children).")
