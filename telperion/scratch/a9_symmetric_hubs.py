"""
A9 (honest Type-W run): the symmetric two-equal-hub subfamily node[H, H].

These are the cleanest Type-W trees (deepest defect = root, two equal clean hubs H, npCount 2).  If a
STRUCTURED move with a closed-form Aobj increment exists HERE, it is the base case of an inductive existence
argument for the general Type-W lemma.  For each hub H (a clean hub: node of pieces, strDefect 0), we:
  - build T = node[H, H], confirm it is Type-W (strDefect>0, no leaf move straightens),
  - find every strDefect-down SPR move and its Aobj increment,
  - characterize the WINNER (moved subtree, target degree/kind) and whether a single structural rule holds.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, isPiece, LEAF
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
import networkx as nx

def clean_hubs(maxsize):
    """Hubs H = node[pieces], strDefect 0, up to `maxsize` vertices, with >=2 children (so node[H,H] is Type-W-ish)."""
    seen = set(); out = []
    for n in range(3, maxsize + 1):
        for t in gen_trees(n):
            if strDefect(t) == 0 and len(t) >= 2 and all(isPiece(c) for c in t):
                if t not in seen:
                    seen.add(t); out.append(t)
    return out

def all_moves(t):
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    deg = {i: G.degree(i) for i in range(n)}
    for (x, y) in list(edges):
        for (src, w) in [(x, y), (y, x)]:
            H = G.copy(); H.remove_edge(src, w)
            keep = nx.node_connected_component(H, src)
            movedsize = n - len(keep)
            for tgt in keep:
                if tgt == src: continue
                Gp = H.copy(); Gp.add_edge(tgt, w)
                if Gp.number_of_edges() != n - 1 or not nx.is_connected(Gp): continue
                tp = rooted_from({i: list(Gp.neighbors(i)) for i in range(n)}, 0, -1)
                yield tp, movedsize, deg[src], deg[tgt]

def run(maxhub=7):
    hubs = clean_hubs(maxhub)
    print(f"clean hubs H (strDefect 0, >=2 children) up to {maxhub} verts: {len(hubs)}")
    all_winner_moves_hub = 0; all_winner_tgt_leaf = 0; typeW = 0; dstr = {}
    for H in hubs:
        T = tuple([H, H])
        d0 = strDefect(T)
        a0 = Aobj_node(T)
        # ALL strDefect-down moves and whether any size-1 (leaf) move straightens with Aobj-nondown:
        down = [(tp, sz, ds, dt) for (tp, sz, ds, dt) in all_moves(T) if strDefect(tp) < d0]
        wins = [(tp, sz, ds, dt) for (tp, sz, ds, dt) in down if Aobj_node(tp) >= a0]
        leaf_straightens = any(sz == 1 and Aobj_node(tp) >= a0 for (tp, sz, ds, dt) in down)
        genuine_typeW = bool(wins) and not leaf_straightens
        if not genuine_typeW:
            continue
        typeW += 1
        best = max(wins, key=lambda r: Aobj_node(r[0]))
        binc = Aobj_node(best[0]) - a0
        dstr[str(binc)] = dstr.get(str(binc), 0) + 1
        hubsz = to_edges(H)[0]
        if best[1] == hubsz: all_winner_moves_hub += 1
        if best[3] == 1: all_winner_tgt_leaf += 1
        if typeW <= 8:
            print(f"  H={H} |H|={hubsz}: strDefect {d0}, best-move size={best[1]} tgtdeg={best[3]} dAobj={binc}")
    print(f"\n  GENUINE Type-W symmetric node[H,H] (no leaf move straightens): {typeW}")
    print(f"    best-move dAobj distribution: {dstr}")
    print(f"    best move relocates a WHOLE hub-child (size |H|): {all_winner_moves_hub}/{typeW}")
    print(f"    best move target is a LEAF (deg 1):               {all_winner_tgt_leaf}/{typeW}")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
