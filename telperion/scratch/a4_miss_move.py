"""
A4b: characterize the WINNING move on the leaf-path-extension MISSES (the symmetric multi-hub trees).

For every genuine tree that leaf-path-extension canNOT straighten (from a4_pathext_covers), enumerate
ALL SPR relocations, keep those that are root-fixed strDefect-DOWN and Aobj-UP, and tabulate the
geometry: moved-subtree size, source degree, target degree, and whether the moved thing is a PIECE
(arm/cherry) vs a bare leaf.  Goal: identify the SECOND move family that closes RealObligationA's tail.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF, isPiece
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
import networkx as nx

def leaves_of(G): return [i for i in G.nodes() if G.degree(i) == 1]

def pathext_can_straighten(t):
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    d0 = strDefect(t); a0 = Aobj_node(t); lv = leaves_of(G)
    for w in lv:
        u = next(iter(G.neighbors(w)))
        for v in lv:
            if v == w or v == u: continue
            H = G.copy(); H.remove_edge(u, w); H.add_edge(v, w)
            if H.number_of_edges() != n - 1 or not nx.is_connected(H): continue
            adj = {i: list(H.neighbors(i)) for i in range(n)}
            tp = rooted_from(adj, 0, -1)
            if strDefect(tp) < d0 and Aobj_node(tp) >= a0:
                return True
    return False

def all_relocations_meta(t):
    """Yield (tp, movedsize, deg_src, deg_tgt, moved_is_piece) for each SPR reparent, re-rooted at 0."""
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    deg = {i: G.degree(i) for i in range(n)}
    for (x, y) in list(edges):
        for (src, w) in [(x, y), (y, x)]:
            H = G.copy(); H.remove_edge(src, w)
            keep = nx.node_connected_component(H, src)
            movedsize = n - len(keep)
            # the moved subtree rooted at w (in H, component of w)
            movedcomp = nx.node_connected_component(H, w)
            adjw = {i: list(H.neighbors(i)) for i in movedcomp}
            moved_rooted = rooted_from(adjw, w, -1)
            for tgt in keep:
                if tgt == src: continue
                Gp = H.copy(); Gp.add_edge(tgt, w)
                if Gp.number_of_edges() != n - 1 or not nx.is_connected(Gp): continue
                adj = {i: list(Gp.neighbors(i)) for i in range(n)}
                tp = rooted_from(adj, 0, -1)
                yield tp, movedsize, deg[src], deg[tgt], isPiece(moved_rooted)

def run(maxn=11):
    geom = {}; movedkind = {'piece': 0, 'nonpiece': 0}; sizes = {}
    misses = 0; miss_covered = 0
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0: continue
            if pathext_can_straighten(t): continue
            misses += 1
            a0 = Aobj_node(t)
            wins = [(sz, ds, dt, pc) for (tp, sz, ds, dt, pc) in all_relocations_meta(t)
                    if strDefect(tp) < d0 and Aobj_node(tp) >= a0]
            if wins: miss_covered += 1
            for (sz, ds, dt, pc) in wins:
                key = 'src>tgt' if ds > dt else ('eq' if ds == dt else 'src<tgt')
                geom[key] = geom.get(key, 0) + 1
                movedkind['piece' if pc else 'nonpiece'] += 1
                sizes[sz] = sizes.get(sz, 0) + 1
    print(f"leaf-path-ext MISSES, n<={maxn}: {misses}")
    print(f"  of those, some SPR move straightens (well-posed): {miss_covered}")
    print(f"  winning-move geometry (deg_src vs deg_tgt): {geom}")
    print(f"  moved thing: {movedkind}")
    print(f"  moved-subtree sizes: {dict(sorted(sizes.items()))}")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
