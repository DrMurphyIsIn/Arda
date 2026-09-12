"""
Verify the GENERAL piece-relocation Aobj decomposition (extends the leaf case to cherry/arm/sub-star).

Relocate a rigid piece K (anchor c, tree-degree dc) from a degree-a vertex p to a non-adjacent degree-b
vertex w. With G = T - K and its matching sums P00/P10/P01/P11 (p,w match-status, degree factors removed),
and the piece's cavity scalars  Z = Ztot(dtSub K)  (total matching value of K),  rho = phi/dc  (phi =
matchings of K with anchor c unmatched):

  (Aobj(T') - Aobj(T)) * a(b+1)
     = rho*(a-b-1)*P00 + (Z*(b+1)+rho*a)/(a-1)*P10 - (Z*a+rho*(b+1))/b*P01 - Z*(a-b-1)/(b*(a-1))*P11.

Leaf: Z=1, rho=1 (recovers R47HwhLeafDecomp).  Cherry: Z=3/2, rho=1/2.  Arm-j: Z=(3/2)^j(1+j/(3(j+1))),
rho=(3/2)^j/(j+1).  Verified exact (0 mismatches) below. Exact fractions.Fraction throughout.
"""
import itertools
from fractions import Fraction as Fr
import networkx as nx
import phase0_straightprogress_sized as P


def matchsum(G, degT, c=None, cstate=None):
    edges = list(G.edges()); tot = Fr(0)
    for r in range(len(edges) + 1):
        for M in itertools.combinations(edges, r):
            vs = [x for e in M for x in e]
            if len(set(vs)) != len(vs):
                continue
            if c is not None:
                cm = any(c in e for e in M)
                if cstate == 'unmatched' and cm: continue
                if cstate == 'matched' and not cm: continue
            wt = Fr(1)
            for (u, v) in M:
                wt *= Fr(1, degT[u] * degT[v])
            tot += wt
    return tot


def Psums(G, p, w, degT):
    edges = list(G.edges()); P00 = P10 = P01 = P11 = Fr(0)
    for r in range(len(edges) + 1):
        for M in itertools.combinations(edges, r):
            vs = [x for e in M for x in e]
            if len(set(vs)) != len(vs):
                continue
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


def check_piece(kind, ncher=0):
    # base path 0-1-2-3-4; p=2, w=0; attach piece at p via anchor c=10
    G = nx.Graph(); G.add_edges_from([(0, 1), (1, 2), (2, 3), (3, 4)])
    p, w, c = 2, 0, 10
    G.add_edge(p, c); verts = [c]
    if kind == 'leaf':
        pass
    elif kind == 'cherry':
        G.add_edge(c, 11); verts += [11]
    elif kind == 'arm':
        nid = 11
        for _ in range(ncher):
            G.add_edge(c, nid); G.add_edge(nid, nid + 1); verts += [nid, nid + 1]; nid += 2
    degT = {v: d for v, d in G.degree()}
    a, b, dc = degT[p], degT[w], degT[c]
    K = G.subgraph(verts).copy()
    Z = matchsum(K, degT)
    phi = matchsum(K, degT, c=c, cstate='unmatched')
    rho = Fr(phi, dc)
    G0 = G.copy(); G0.remove_nodes_from(verts)
    P00, P10, P01, P11 = Psums(G0, p, w, degT)
    Gp = G.copy(); Gp.remove_edge(p, c); Gp.add_edge(w, c)
    lhs = (P.Aobj(Gp) - P.Aobj(G)) * a * (b + 1)
    rhs = (rho * (a - b - 1) * P00 + Fr(Z * (b + 1) + rho * a, a - 1) * P10
           - Fr(Z * a + rho * (b + 1), b) * P01 - Fr(Z * (a - b - 1), b * (a - 1)) * P11)
    return kind, Z, rho, (lhs == rhs)


if __name__ == "__main__":
    bad = 0
    for kind, nch in [('leaf', 0), ('cherry', 0), ('arm', 1), ('arm', 2), ('arm', 3)]:
        k, Z, rho, ok = check_piece(kind, nch)
        label = f"{k}{('-' + str(nch)) if k == 'arm' else ''}"
        print(f"{label:8s}  Z={Z}  rho={rho}  formula exact: {ok}")
        bad += (not ok)
    print(f"general piece decomposition: {bad} mismatches")
