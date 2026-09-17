"""
Verify the ADJACENT-p,w leaf-relocation decomposition (the p ~ w case of the leaf decomposition).

When p and w are adjacent, G = T - leaf contains the edge p-w. Over the matching sums P00,P10,P01,P11 of G
restricted to matchings NOT using the p-w edge (P11 = p,w matched to distinct non-partners):

  (Aobj(T') - Aobj(T)) * a(b+1) = (a+b+1)*B1 + (a-b-1)*B2adj,
     B1 = P10/(a-1) - P01/b,   B2adj = P00 - (P00+P11)/(b*(a-1)).

B2adj >= 0 holds (adjacent counting: q!=w, r!=p give P11 <= (a-2)(b-1)P00, so P00+P11 <= (a-1)b P00).
Verified exact (0 mismatches, 0 B2adj counterexamples). Formalized in R3Cert/R47HwhAdjDecomp.lean.
"""
import itertools
from fractions import Fraction as Fr
import networkx as nx
import phase0_straightprogress_sized as P


def Psums_adj(G, p, w, degT):
    edges = list(G.edges()); P00 = P10 = P01 = P11 = Fr(0)
    for r in range(len(edges) + 1):
        for M in itertools.combinations(edges, r):
            vs = [x for e in M for x in e]
            if len(set(vs)) != len(vs):
                continue
            if (p, w) in M or (w, p) in M:
                continue  # exclude p-w matched (that term = Q = P00)
            rw = Fr(1); pm = wm = False
            for (u, v) in M:
                fu = 1 if u in (p, w) else degT[u]; fv = 1 if v in (p, w) else degT[v]
                rw *= Fr(1, fu * fv)
                if u == p or v == p: pm = True
                if u == w or v == w: wm = True
            if pm and wm: P11 += rw
            elif pm: P10 += rw
            elif wm: P01 += rw
            else: P00 += rw
    return P00, P10, P01, P11


def verify(n_max=11):
    bad = b2bad = tested = 0
    for n in range(6, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            degT = {v: dg for v, dg in T.degree()}
            for l in [x for x in T.nodes() if T.degree(x) == 1]:
                p = next(iter(T.neighbors(l))); a = degT[p]
                if a < 2:
                    continue
                G = T.copy(); G.remove_node(l)
                for w in T.nodes():
                    if w in (l, p) or not T.has_edge(p, w):
                        continue
                    b = degT[w]
                    P00, P10, P01, P11 = Psums_adj(G, p, w, degT)
                    B1 = Fr(P10, a - 1) - Fr(P01, b)
                    B2adj = P00 - Fr(P00 + P11, b * (a - 1))
                    rhs = (a + b + 1) * B1 + (a - b - 1) * B2adj
                    Tp = T.copy(); Tp.remove_edge(l, p); Tp.add_edge(l, w)
                    lhs = (P.Aobj(Tp) - P.Aobj(T)) * a * (b + 1)
                    tested += 1
                    bad += (lhs != rhs)
                    b2bad += (B2adj < 0)
    return tested, bad, b2bad


if __name__ == "__main__":
    tested, bad, b2bad = verify(11)
    print(f"adjacent p~w leaf moves: tested={tested}  decomposition mismatches={bad}  B2adj<0 count={b2bad}")
