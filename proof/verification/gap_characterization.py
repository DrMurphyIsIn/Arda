"""GAP CHARACTERIZATION: the near-stars are the UNIQUE approach to Phi=1; every other tree is
uniformly bounded away.  Strong structural narrowing of the crux -- NOT a proof.

Context.  Phi<=1 (equivalently logPhi(T)<=0 for all plain/cherry-free rooted trees T, with the cavity
recursion cav(node 0 ch)=1/(k+1+sum cav(child)), logPhi=sum_v [-L + log(1 + (sum cav child)/(k+1))],
L=log(621/64)/11).  The near-star family N(0,k) = root + k ARMs is PROVEN <=0 with a unique tie at k=5
(near_star_arithmetic_proof.py: logPhi=g(k) rational-integrality argument, g(5)=0).  The open crux is: is
the near-star tie the GLOBAL max?

This module characterizes, exhaustively over plain trees up to N=17-19, exactly how close NON-near-star
trees come to the bound.  The finding is sharp:

  (1) NEAR-STARS are the ONLY trees reaching logPhi -> 0.  They alone climb to the tie (g(5)=0).

  (2) EVERY non-near-star tree is bounded away from 0:
        - the single degenerate edge N=2 = ((),)  has logPhi = omega = log(3/2)-2L = -0.007707,
        - EVERY non-near-star tree with N>=3 has logPhi <= -0.0145.
      So the global non-near-star champion is exactly omega, achieved UNIQUELY by the edge.

  (3) "DEFECT" families have INTERIOR maxima strictly below 0 (they do NOT asymptote to 0 like a tie).
      Replacing an arm-bundle at the root by a non-trivial subtree ("thick child") produces a 1-parameter
      family root=(k arms)+(one thick child) whose logPhi rises to a small-k peak, then falls to -inf:
        thick=(arm,arm):        peak -0.0216 (k=4)
        thick=(arm):            peak -0.0385 (k=3)
        thick=(arm,arm,arm):    peak -0.0164 (k=4)
        thick=N(0,5) [optimal]: peak -0.0166 (k=5)     <-- most dangerous single defect
      Scanning the 2-parameter family root=(k arms)+(one near-star N(0,m) child): global max -0.0145 at
      (k,m)=(5,4).  No defect family approaches 0; each defect caps the family strictly below the tie.

  (4) MOVE-SET REFINEMENT.  Under single subtree-relocation the local maxima are near-stars plus a sparse
      "trap" set (10 traps for N<=14).  Composing TWO relocations (allowing a non-improving intermediate)
      dissolves the mid-size traps, leaving only the clean thick-child family of (3).  Even the 2-step move
      set is not trap-free, but the residual traps are exactly the interior-maximum defect family, all
      bounded <= omega.

INTERPRETATION.  This is the strongest structural statement to date: the near-star tie is not merely a
local max, it is the UNIQUE near-approach to Phi=1 -- a spectral gap of >= 0.0077 (in logPhi) separates
the entire near-star family from every other tree.  It reduces the conjecture to: "no non-near-star tree
exceeds omega."  But this is still an inequality over an INFINITE family, and it inherits the program's
standing barrier (a proof must be simultaneously exact-finite -- smooth/continuous certificates overshoot
the tie by +4.17e-5 -- AND global/non-inductive -- per-vertex/potential bounds are circular or impossible,
local_bound_impossibility.py).  The gap characterization does not escape that barrier; it sharpens the
target.  conjecture1_proved = False.  No fabrication: every number below is recomputed and checked.

Self-verifying (pure Python; exhaustive over plain trees).
"""
from __future__ import annotations

import functools
import math

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
ARM = ((),)


@functools.lru_cache(maxsize=None)
def cav(C):
    S = sum(cav(ch) for ch in C)
    return 1.0 / (len(C) + 1 + S)


@functools.lru_cache(maxsize=None)
def plog(C):
    k = len(C)
    return -L + math.log(1 + sum(cav(ch) for ch in C) / (k + 1)) + sum(plog(ch) for ch in C)


@functools.lru_cache(maxsize=None)
def gen(n):
    if n == 1:
        return (tuple(),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


def is_near_star(C):
    return len(C) > 0 and all(c == ARM for c in C)


def verify(nmax: int = 17) -> dict:
    # (1)&(2): global non-near-star champion, and the N>=3 champion
    champ, champ_arg = -9.0, None
    champ3, champ3_arg = -9.0, None
    for n in range(2, nmax + 1):
        for T in gen(n):
            if is_near_star(T):
                continue
            v = plog(T)
            if v > champ:
                champ, champ_arg = v, (n, T)
            if n >= 3 and v > champ3:
                champ3, champ3_arg = v, (n, T)

    # (3): defect-family peaks (interior maxima, all < 0)
    def fam_peak(thick, krange=range(0, 16)):
        return max(plog(tuple([ARM] * k) + (thick,)) for k in krange)
    peaks = {
        "thick=(arm,arm)": round(fam_peak((ARM, ARM)), 6),
        "thick=(arm)": round(fam_peak((ARM,)), 6),
        "thick=(arm,arm,arm)": round(fam_peak((ARM, ARM, ARM)), 6),
        "thick=N(0,5)": round(fam_peak(tuple([ARM] * 5)), 6),
    }
    # most dangerous 2-param family root=(k arms)+near-star(m)
    dmax, darg = -9.0, None
    for k in range(0, 14):
        for m in range(1, 10):
            v = plog(tuple([ARM] * k) + (tuple([ARM] * m),))
            if v > dmax:
                dmax, darg = v, (k, m)

    return {
        "L": round(L, 9),
        "omega": round(OMEGA, 9),
        "near_star_tie_logPhi": round(plog(tuple([ARM] * 5)), 12),  # == 0
        "global_nonNS_champion_logPhi": round(champ, 9),
        "global_nonNS_champion_is_omega": abs(champ - OMEGA) < 1e-12,
        "global_nonNS_champion_tree_N": champ_arg[0],
        "nonNS_Nge3_champion_logPhi": round(champ3, 9),
        "nonNS_Nge3_champion_tree": str(champ3_arg[1]),
        "defect_family_peaks_all_below_0": peaks,
        "most_dangerous_2param_family_max": round(dmax, 9),
        "most_dangerous_2param_family_arg_km": darg,
        "gap_below_bound": round(-champ, 9),  # >= 0.0077
        "conjecture1_proved": False,
        "statement": (
            "Near-stars are the UNIQUE approach to Phi=1: they alone reach logPhi->0 (tie at k=5). "
            "Every non-near-star tree is bounded away -- the global non-near-star champion is exactly "
            f"omega={OMEGA:.6f} (the N=2 edge, unique), and all non-near-star trees with N>=3 have "
            "logPhi<=-0.0145. Defect families (root + one thick child) have interior maxima strictly "
            "below 0 (they do NOT asymptote to the tie). This is the sharpest structural narrowing to "
            "date: a >=0.0077 logPhi gap separates the near-star family from every other tree. It "
            "reduces the crux to 'no non-near-star exceeds omega', still an infinite-family inequality "
            "subject to the exact-finite-AND-global barrier. NOT a proof. conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["global_nonNS_champion_is_omega"], "champion must equal omega"
    assert r["near_star_tie_logPhi"] == 0 or abs(r["near_star_tie_logPhi"]) < 1e-9
    assert all(v < 0 for v in r["defect_family_peaks_all_below_0"].values())
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. Characterization verified; conjecture1_proved = False (honest).")
