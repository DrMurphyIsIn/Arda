"""
Characterize the TRUE per-size maximizer of Aobj = per(L)/prod(deg) over n-vertex trees,
to assess whether conjecture1 is salvageable with a corrected (multi-hub-caterpillar) tie family.

Exact fractions.Fraction throughout. Aobj computed as the monomer-dimer partition function
Z = sum over matchings M of prod_{(u,v) in M} 1/(deg u * deg v)  [= per(L)/prod(deg) for a tree],
via a linear rooted tree-DP. Validated against networkx-independent brute enumeration on small n.

- n <= NEXH: exhaustive over all non-isomorphic trees (networkx).
- larger aligned n: multi-start SPR hill-climb from structured seeds (caterpillars, spiders, near-stars,
  Pant T-families, and the broadened hub).
Classifies each maximizer: hub set (deg>=3), hub-degree multiset, whether caterpillar, pendant/cherry loads.
"""
import sys, os, itertools
from fractions import Fraction as F
import networkx as nx

# ---------- Aobj engine: monomer-dimer Z via tree DP (exact) ----------
def aobj(G):
    """Aobj(T) = per(L)/prod(deg) = sum_matchings prod 1/(deg u deg v). Exact Fraction. Root anywhere."""
    deg = dict(G.degree())
    root = next(iter(G.nodes()))
    # iterative post-order to avoid recursion limits
    parent = {root: None}
    order = []
    stack = [root]
    seen = {root}
    while stack:
        v = stack.pop()
        order.append(v)
        for w in G.neighbors(v):
            if w not in seen:
                seen.add(w); parent[w] = v; stack.append(w)
    m0 = {}; m1 = {}
    for v in reversed(order):
        prod = F(1)
        children = [w for w in G.neighbors(v) if parent.get(w) == v]
        for c in children:
            prod *= (m0[c] + m1[c])
        m0[v] = prod
        s = F(0)
        for c in children:
            w_e = F(1, deg[v] * deg[c])
            rest = prod / (m0[c] + m1[c]) if (m0[c] + m1[c]) != 0 else F(0)
            s += w_e * m0[c] * rest
        m1[v] = s
    return m0[root] + m1[root]

# ---------- structural classification ----------
def classify(G):
    deg = dict(G.degree())
    hubs = sorted([v for v in G.nodes() if deg[v] >= 3], key=lambda v: -deg[v])
    hub_degs = sorted([deg[v] for v in hubs], reverse=True)
    # caterpillar test: removing all leaves yields a path
    H = G.copy()
    leaves = [v for v in H.nodes() if H.degree(v) == 1]
    H.remove_nodes_from(leaves)
    is_cat = (H.number_of_nodes() == 0) or nx.is_connected(H) and all(H.degree(v) <= 2 for v in H.nodes())
    # pendant-path (cherry) counts per hub: count length-2 pendant paths and bare leaves at each hub
    return {"n_hubs": len(hubs), "hub_degs": hub_degs, "is_caterpillar": bool(is_cat)}

# ---------- tree builders (return networkx graph) ----------
def path_graph(k): return nx.path_graph(k)

def caterpillar(spine_len, legs):
    """spine of spine_len core vertices (a path); legs[i] = list of pendant-path lengths at core i."""
    G = nx.Graph(); nid = 0
    spine = list(range(spine_len)); nid = spine_len
    G.add_nodes_from(spine)
    for i in range(spine_len - 1): G.add_edge(spine[i], spine[i+1])
    for i in range(spine_len):
        for L in legs[i]:
            prev = spine[i]
            for _ in range(L):
                G.add_edge(prev, nid); prev = nid; nid += 1
    return G

def pant_uniform(m, t, leglen=2):
    """T(t,...,t) with m core vertices, each carrying t pendant paths of length leglen."""
    return caterpillar(m, [[leglen]*t for _ in range(m)])

def near_star(K):
    """single hub with K load-5 arms (armU 5 = vertex with 5 cherries)."""
    return caterpillar(1, [[2]*0]) if False else broadened_hub(K, 0, 0)

def broadened_hub(a, b, c):
    """single hub: a load-5 arms + b load-4 arms + c cherries. armU(j)=hub->arm->(j cherries)."""
    G = nx.Graph(); hub = 0; nid = 1; G.add_node(hub)
    def add_arm(load):
        nonlocal nid
        arm = nid; nid += 1; G.add_edge(hub, arm)
        for _ in range(load):
            ch = nid; nid += 1; leaf = nid; nid += 1
            G.add_edge(arm, ch); G.add_edge(ch, leaf)
    for _ in range(a): add_arm(5)
    for _ in range(b): add_arm(4)
    for _ in range(c):  # cherry directly on hub
        ch = nid; nid += 1; leaf = nid; nid += 1
        G.add_edge(hub, ch); G.add_edge(ch, leaf)
    return G

# ---------- SPR neighborhood ----------
def spr_neighbors(G):
    """all trees from pruning one edge and regrafting the smaller component onto any node of the other."""
    nodes = list(G.nodes())
    for (u, v) in list(G.edges()):
        H = G.copy(); H.remove_edge(u, v)
        comps = list(nx.connected_components(H))
        cu = comps[0] if u in comps[0] else comps[1]
        cv = comps[1] if u in comps[0] else comps[0]
        # regraft: connect u's component (via u) to any node in v's component, and vice versa
        for target in cv:
            if target == v: continue
            H2 = H.copy(); H2.add_edge(u, target); yield H2
        for target in cu:
            if target == u: continue
            H2 = H.copy(); H2.add_edge(v, target); yield H2

def spr_hillclimb(seed, iters=400):
    best = seed; bestval = aobj(seed)
    improved = True; steps = 0
    while improved and steps < iters:
        improved = False; steps += 1
        for nb in spr_neighbors(best):
            v = aobj(nb)
            if v > bestval:
                best = nb; bestval = v; improved = True; break
    return best, bestval

def seeds_for(n):
    out = []
    # path
    out.append(nx.path_graph(n))
    # uniform Pant families with m cores
    for m in (2, 3, 4, 5, 6, 7):
        for t in range(1, n):
            G = pant_uniform(m, t)
            if G.number_of_nodes() == n: out.append(G)
    # broadened single hubs (a,b,c) of size n
    for a in range(0, n // 11 + 2):
        for b in range(0, n // 9 + 2):
            for c in range(0, 8):
                if 1 + 11*a + 9*b + 2*c == n and a + b >= 1:
                    out.append(broadened_hub(a, b, c))
    # cherry-spider: single hub with k cherries
    for k in range(1, (n - 1)//2 + 1):
        if 1 + 2*k == n: out.append(broadened_hub(0, 0, k))
    return out

def best_over_seeds(n):
    best = None; bestval = None
    for s in seeds_for(n):
        if s.number_of_nodes() != n: continue
        cand, val = spr_hillclimb(s)
        if bestval is None or val > bestval:
            best, bestval = cand, val
    return best, bestval

# ---------- exhaustive (small n) ----------
def exhaustive_max(n):
    best = None; bestval = None
    for T in nx.nonisomorphic_trees(n):
        v = aobj(T)
        if bestval is None or v > bestval: best, bestval = T, v
    return best, bestval

def selfcheck():
    # validate aobj vs brute matching enumeration on a few small trees
    def brute(G):
        deg = dict(G.degree()); edges = list(G.edges()); tot = F(0)
        for r in range(len(edges)+1):
            for M in itertools.combinations(edges, r):
                vs = [x for e in M for x in e]
                if len(set(vs)) == len(vs):
                    p = F(1)
                    for (u, v) in M: p *= F(1, deg[u]*deg[v])
                    tot += p
        return tot
    for G in [nx.path_graph(5), broadened_hub(1,1,1), pant_uniform(3,2), pant_uniform(2,3)]:
        assert aobj(G) == brute(G), (aobj(G), brute(G))
    print("selfcheck: aobj == brute matching enumeration  OK")

if __name__ == "__main__":
    selfcheck()
    NEXH = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    print(f"\n=== EXHAUSTIVE maximizer, n = 7..{NEXH} ===")
    for n in range(7, NEXH+1):
        T, v = exhaustive_max(n)
        c = classify(T)
        print(f"n={n:3d}  Aobj~={float(v):12.4f}  hubs={c['n_hubs']} degs={c['hub_degs']} caterpillar={c['is_caterpillar']}")
    print(f"\n=== SPR-best maximizer, selected larger n ===")
    for n in [23, 34, 45, 46, 52, 55, 56, 58, 67, 68, 78, 84, 90]:
        T, v = best_over_seeds(n)
        c = classify(T)
        print(f"n={n:3d}  Aobj~={float(v):12.4f}  hubs={c['n_hubs']} degs={c['hub_degs']} caterpillar={c['is_caterpillar']}")
