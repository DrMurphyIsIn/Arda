"""
Exact analytic decomposition of the Aobj change under a LEAF RELOCATION -- the analytic handle for the
`hwh` monotonicity nut (the tree->cherry-backbone straightening).

Setup: tree T, leaf l with neighbor p (deg a), relocate l to a non-adjacent w (deg b). T' has deg(p)=a-1,
deg(w)=b+1. Let G = T - l. Classify matchings of G by (p matched?, w matched?), with the p- and w-degree
factors FACTORED OUT of the edge weights 1/(deg u . deg v):
    P00 = both unmatched,  P10 = p matched w unmatched,  P01 = p unmatched w matched,  P11 = both matched.

EXACT identities (verified below, 0 mismatches):
    Aobj(T)  = P00*(a+1)/a + P10/a + P01*(a+1)/(a b) + P11/(a b)
    Aobj(T') = P00*(b+2)/(b+1) + P10*(b+2)/((a-1)(b+1)) + P01/(b+1) + P11/((a-1)(b+1))
  =>  (Aobj(T') - Aobj(T)) * a(b+1) = (a+b+1)*B1 + (a-b-1)*B2
     with  B1 = P10/(a-1) - P01/b ,  B2 = P00 - P11/(b(a-1)).

Empirical facts (exact Fraction, exhaustive small n):
  * The decomposition is EXACT (0 mismatches, n<=11, p,w non-adjacent).
  * B2 >= 0 is a CLEAN universal lemma in the regime b <= a-1 (0 counterexamples, n<=11).  [provable]
  * A defect-reducing leaf move with b <= a-1 EXISTS for every defective tree except the n=13 triple-3-star.
  * B1 >= 0 is NOT a degree-only fact (fails for e.g. leaf-onto-leaf a=2,b=1), but holds for the
    MIN-receiving-degree defect-reducing selection.  This coupling (B1 >= 0 under the min-degree
    defect-reducing move) is the remaining open core of the leaf case.  Since B2 >= 0 and (for the move)
    a-b-1 >= 0, monotonicity ΔAobj >= 0 follows from (a+b+1)*B1 + (a-b-1)*B2 >= 0.

conjecture1_proved = False.  This file is an analytic de-risk, not a proof.
"""
import itertools
from fractions import Fraction as Fr
import networkx as nx
import phase0_straightprogress_sized as P


def Psums(G, p, w, degT):
    edges = list(G.edges())
    P00 = P10 = P01 = P11 = Fr(0)
    for r in range(len(edges) + 1):
        for M in itertools.combinations(edges, r):
            vs = [x for e in M for x in e]
            if len(set(vs)) != len(vs):
                continue
            rw = Fr(1); pm = wm = False
            for (u, v) in M:
                fu = 1 if u in (p, w) else degT[u]
                fv = 1 if v in (p, w) else degT[v]
                rw *= Fr(1, fu * fv)
                if u == p or v == p: pm = True
                if u == w or v == w: wm = True
            if pm and wm: P11 += rw
            elif pm: P10 += rw
            elif wm: P01 += rw
            else: P00 += rw
    return P00, P10, P01, P11


def verify_decomposition(n_max=11):
    bad = tested = 0
    b2bad = 0
    for n in range(6, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            degT = {v: dg for v, dg in T.degree()}
            for l in [x for x in T.nodes() if T.degree(x) == 1]:
                p = next(iter(T.neighbors(l))); a = degT[p]
                if a < 2:
                    continue
                G = T.copy(); G.remove_node(l)
                for w in T.nodes():
                    if w in (l, p) or T.has_edge(p, w):
                        continue
                    b = degT[w]
                    P00, P10, P01, P11 = Psums(G, p, w, degT)
                    aT = P00 * Fr(a + 1, a) + P10 * Fr(1, a) + P01 * Fr(a + 1, a * b) + P11 * Fr(1, a * b)
                    Tp = T.copy(); Tp.remove_edge(l, p); Tp.add_edge(l, w)
                    aTp = (P00 * Fr(b + 2, b + 1) + P10 * Fr(b + 2, (a - 1) * (b + 1))
                           + P01 * Fr(1, b + 1) + P11 * Fr(1, (a - 1) * (b + 1)))
                    tested += 1
                    if aT != P.Aobj(T) or aTp != P.Aobj(Tp):
                        bad += 1
                    if b <= a - 1 and (P00 - Fr(P11, b * (a - 1))) < 0:
                        b2bad += 1
    return tested, bad, b2bad


if __name__ == "__main__":
    tested, bad, b2bad = verify_decomposition(11)
    print(f"decomposition verified on {tested} leaf-moves (p,w non-adjacent); mismatches = {bad}")
    print(f"B2 = P00 - P11/(b(a-1)) >= 0  in regime b<=a-1: counterexamples = {b2bad}  (clean lemma)")
    print("Remaining open core of the leaf case: B1 = P10/(a-1) - P01/b >= 0 under the min-degree "
          "defect-reducing selection (coupled to the defect structure, not a degree-only fact).")
