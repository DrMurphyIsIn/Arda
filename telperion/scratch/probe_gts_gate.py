"""
GATE G-R3-gts : does the Csikvari Generalized Tree Shift (GTS) move keep the
VDB-weighted matching coefficients Z_k coefficientwise NON-DECREASING toward the path?

M(T,t) = sum_k Z_k t^k,  Z_k = sum over size-k matchings M of  prod_{(u,v) in M} 1/(d_u d_v).

GTS(T, x, y) [Csikvari 2010, "On a poset of trees"]:
  Let x,y be two vertices, and let z be the neighbor of x on the x->y path.
  Detach every neighbor w of x with w != z, and reattach w to y.
  (This slides the branches at x over to y; iterating drives T toward the path P_n,
   the unique maximum of the poset.)

We enumerate all trees n<=CAP, apply EVERY GTS step (all ordered pairs x,y that produce
a genuinely different tree), and test Z_k(GTS(T)) >= Z_k(T) coefficientwise.
A single violation REFUTES the gate.

EXACT fractions.Fraction only.
"""
from fractions import Fraction as Fr
import networkx as nx


# --------------------------------------------------------------------- VDB matching poly
def vdb_matching_coeffs(n, edges):
    """Return dict k -> Z_k (Fraction), the size-graded VDB-weighted matching sum.
    Z_k = sum over matchings of size k of prod 1/(d_u d_v).  Z_0 = 1.
    Computed by exact tree DP graded by matching size (polynomials in t)."""
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    deg = {v: len(adj[v]) for v in range(n)}
    if n == 1:
        return {0: Fr(1)}
    root = 0
    parent = {root: -1}
    order = []
    stack = [root]; seen = {root}
    while stack:
        u = stack.pop(); order.append(u)
        for w in adj[u]:
            if w not in seen:
                seen.add(w); parent[w] = u; stack.append(w)

    # For each vertex store two polynomials (as dict deg->Fr):
    #   unm[v] : gen. poly of matchings of subtree(v) with v UNMATCHED
    #   mat[v] : gen. poly of matchings of subtree(v) with v MATCHED (to a child)
    # graded by matching SIZE (power of t).
    def polymul(p, q):
        r = {}
        for a, ca in p.items():
            for b, cb in q.items():
                r[a + b] = r.get(a + b, Fr(0)) + ca * cb
        return r
    def polyadd(p, q):
        r = dict(p)
        for b, cb in q.items():
            r[b] = r.get(b, Fr(0)) + cb
        return r
    def polyscale(p, s):
        return {a: c * s for a, c in p.items()}

    unm = {}; mat = {}
    for v in reversed(order):
        kids = [c for c in adj[v] if c != parent[v]]
        # tot[c] = unm[c] + mat[c]
        tots = {c: polyadd(unm[c], mat[c]) for c in kids}
        # unm[v] = prod_c tot[c]
        pu = {0: Fr(1)}
        for c in kids:
            pu = polymul(pu, tots[c])
        # mat[v] = sum_i (edge weight * t) * unm[child_i] * prod_{j!=i} tot[child_j]
        pm = {0: Fr(0)}
        # prefix/suffix products of tots for leave-one-out
        m = {0: Fr(0)}
        for i, c in enumerate(kids):
            w = Fr(1, deg[v] * deg[c])
            rest = {0: Fr(1)}
            for j, c2 in enumerate(kids):
                if j != i:
                    rest = polymul(rest, tots[c2])
            # matched edge (v,c): weight w, contributes t^1, child c must be UNMATCHED
            contrib = polyscale(polymul({1: w}, polymul(unm[c], rest)), Fr(1))
            m = polyadd(m, contrib)
        unm[v] = pu; mat[v] = m
    full = polyadd(unm[root], mat[root])
    return full


# --------------------------------------------------------------------- GTS move
# Csikvari (Combinatorica 2010, "On a poset of trees"):
#   x,y vertices s.t. all INTERIOR vertices of path P_{x,y} have degree 2.
#   z = neighbor of y on P_{x,y}.  T2 = move ALL neighbors of y except z onto x.
#   This is the UP move: STAR is the top (max), PATH is the bottom (min).
# "Toward the path" (the direction in the question) is the INVERSE / DOWN move.

def _path(adj, x, y):
    par = {x: None}; dq = [x]
    while dq:
        u = dq.pop(0)
        if u == y:
            break
        for w in adj[u]:
            if w not in par:
                par[w] = u; dq.append(w)
    if y not in par:
        return None
    seq = [y]
    while par[seq[-1]] is not None:
        seq.append(par[seq[-1]])
    seq.reverse()               # x ... y
    return seq

def gts_up(adj, x, y):
    """Csikvari GTS UP step (toward the star). Returns new adj or None if degenerate/illegal."""
    if x == y:
        return None
    P = _path(adj, x, y)
    if P is None or len(P) < 2:
        return None
    # interior vertices must have degree 2
    for v in P[1:-1]:
        if len(adj[v]) != 2:
            return None
    z = P[-2]                                   # neighbor of y on path
    movers = [w for w in adj[y] if w != z]
    if not movers:
        return None
    new = {v: set(s) for v, s in adj.items()}
    changed = False
    for w in movers:
        if w == x:
            continue
        new[y].discard(w); new[w].discard(y)
        new[x].add(w); new[w].add(x)
        changed = True
    if not changed:
        return None
    return new


def adj_to_edges(adj):
    E = set()
    for u, s in adj.items():
        for v in s:
            E.add((min(u, v), max(u, v)))
    return sorted(E)


def canon(n, edges):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    return nx.weisfeiler_lehman_graph_hash(G, iterations=n)


# --------------------------------------------------------------------- probe driver
def coeffs_ge(after, before):
    """Return list of k where Z_k(after) < Z_k(before) (violations)."""
    ks = set(after) | set(before)
    bad = []
    for k in ks:
        a = after.get(k, Fr(0)); b = before.get(k, Fr(0))
        if a < b:
            bad.append((k, b, a))
    return bad


def run(CAP=13):
    """For every GTS covering pair (T_lo --UP--> T_hi), where T_hi = gts_up(T_lo) is
    the tree one step TOWARD THE STAR and T_lo is one step TOWARD THE PATH, test the
    'non-decreasing toward the path' claim:  Z_k(T_lo) >= Z_k(T_hi) for all k.
    A violation (some k with Z_k(T_lo) < Z_k(T_hi)) REFUTES the gate."""
    total_trees = 0
    total_moves = 0
    violations = []
    for n in range(2, CAP + 1):
        for T in nx.nonisomorphic_trees(n):
            total_trees += 1
            edges0 = list(T.edges())
            adj0 = {i: set() for i in range(n)}
            for a, b in edges0:
                adj0[a].add(b); adj0[b].add(a)
            Z_lo = vdb_matching_coeffs(n, edges0)   # T_lo (toward the path)
            h0 = canon(n, edges0)
            for x in range(n):
                for y in range(n):
                    if x == y:
                        continue
                    up = gts_up(adj0, x, y)          # T_hi (toward the star)
                    if up is None:
                        continue
                    e1 = adj_to_edges(up)
                    if len(e1) != n - 1 or not nx.is_connected(nx.Graph(e1)):
                        continue
                    if canon(n, e1) == h0:
                        continue                    # no structural change
                    total_moves += 1
                    Z_hi = vdb_matching_coeffs(n, e1)
                    # "non-decreasing toward the path": Z_lo >= Z_hi coefficientwise.
                    # violation = some k with Z_lo < Z_hi  ==  coeffs_ge(after=Z_lo, before=Z_hi).
                    bad = coeffs_ge(Z_lo, Z_hi)      # returns k where Z_lo < Z_hi
                    if bad:
                        violations.append({
                            "n": n, "x": x, "y": y,
                            "T_path": edges0, "T_star": e1,
                            "bad_k": bad,
                        })
    print(f"[GTS gate] CAP n<= {CAP}")
    print(f"  trees enumerated       : {total_trees}")
    print(f"  GTS covering steps      : {total_moves}")
    print(f"  coefficientwise violations of 'Z_k non-decreasing toward the path': {len(violations)}")
    if violations:
        v = violations[0]
        print("  FIRST COUNTEREXAMPLE:")
        print(f"    n={v['n']}  GTS(x={v['x']}, y={v['y']}) moves UP toward star")
        print(f"    T_path (toward path, lo) edges = {v['T_path']}")
        print(f"    T_star (toward star, hi) edges = {v['T_star']}")
        Zlo = vdb_matching_coeffs(v['n'], v['T_path'])
        Zhi = vdb_matching_coeffs(v['n'], v['T_star'])
        allk = sorted(set(Zlo) | set(Zhi))
        for (k, hi, lo) in v["bad_k"]:   # coeffs_ge returned (k, before=Z_hi, after=Z_lo)
            print(f"    Z_{k}: toward-path={lo}  toward-star={hi}   (path < star -> 'non-decreasing toward path' FAILS)")
        print("    Z_k(T_path):", {k: str(Zlo.get(k, Fr(0))) for k in allk})
        print("    Z_k(T_star):", {k: str(Zhi.get(k, Fr(0))) for k in allk})
    else:
        print("  VERDICT: no violation -- Z_k are coefficientwise non-decreasing toward the path on all trees n<=CAP")
    return violations, total_trees, total_moves


if __name__ == "__main__":
    import sys
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    run(cap)
