"""
A7: taxonomy of the LOCAL straightening move at a deepest defective node u — the sweep spec.

Given locality (a6: a subtree(u)-confined strDefect-down + Aobj-nondecreasing move always exists), classify
WHICH move-type each defective tree needs, so we know exactly which certificates to emit:

  Type L  : a LEAF move (relocate a single pendant, size 1) within subtree(u) straightens.
            -> already covered by the F2 leaf-path-extension certificate  P*(n^2+nQ+4Q)/(...) >= 0.
  Type W  : NO leaf move works; needs a WHOLE non-piece child relocation (moved size >= 2).
            -> the new certificate to derive/emit.

For the Type-W cases we also test a CANONICAL local target: relocate a non-piece child of u onto the
LOWEST-degree vertex inside subtree(u) (excluding the child's own subtree). If canonical-W is Aobj-nondown
for all Type-W trees, the Type-W move is pinned (no search) and its increment can be given a closed form.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, isPiece
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
from a6_locality import build, deepest_defective, _parent_of, subtree
import networkx as nx

def local_moves_sized(t):
    """(tp, moved_size, deg_tgt) for SPR relocations confined to subtree(u), u = deepest defect."""
    n, G, children, adj = build(t)
    u = deepest_defective(adj, children, n)
    if u is None: return
    par = _parent_of(children, u)
    sub = nx.node_connected_component(nx.restricted_view(G, [], [(u, par)] if par >= 0 else []), u)
    deg = {i: G.degree(i) for i in range(n)}
    for (x, y) in list(G.edges()):
        if x not in sub or y not in sub: continue
        for (src, w) in [(x, y), (y, x)]:
            H = G.copy(); H.remove_edge(src, w)
            keep = nx.node_connected_component(H, src)
            movedsize = n - len(keep)
            for tgt in keep:
                if tgt == src or tgt not in sub: continue
                Gp = H.copy(); Gp.add_edge(tgt, w)
                if Gp.number_of_edges() != n - 1 or not nx.is_connected(Gp): continue
                yield rooted_from({i: list(Gp.neighbors(i)) for i in range(n)}, 0, -1), movedsize, deg[tgt]

def canonical_W(t):
    """Relocate a non-piece child of u onto the LOWEST-degree vertex in subtree(u) outside that child."""
    n, G, children, adj = build(t)
    u = deepest_defective(adj, children, n)
    if u is None: return None
    par = _parent_of(children, u)
    sub = nx.node_connected_component(nx.restricted_view(G, [], [(u, par)] if par >= 0 else []), u)
    deg = {i: G.degree(i) for i in range(n)}
    best = None
    for c in children[u]:
        if isPiece(subtree(adj, c, u)): continue
        comp_c = nx.node_connected_component(nx.restricted_view(G, [], [(u, c)]), c)
        targets = [v for v in sub if v != u and v not in comp_c]
        if not targets: continue
        v = min(targets, key=lambda z: deg[z])       # lowest-degree local target
        H = G.copy(); H.remove_edge(u, c); H.add_edge(v, c)
        if H.number_of_edges() == n - 1 and nx.is_connected(H):
            tp = rooted_from({i: list(H.neighbors(i)) for i in range(n)}, 0, -1)
            best = tp   # first non-piece child; deterministic
            break
    return best

def run(maxn=12):
    genuine = 0; L_cov = 0; W_needed = 0; canonW_ok = 0; canonW_applies = 0
    wsizes = {}
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0: continue
            genuine += 1
            a0 = Aobj_node(t)
            good = [(tp, sz) for (tp, sz, dt) in local_moves_sized(t)
                    if strDefect(tp) < d0 and Aobj_node(tp) >= a0]
            if not good:
                continue  # (cannot happen; a6 = 100%)
            minsz = min(sz for _, sz in good)
            if minsz == 1:
                L_cov += 1
            else:
                W_needed += 1
                wsizes[minsz] = wsizes.get(minsz, 0) + 1
                cw = canonical_W(t)
                if cw is not None:
                    canonW_applies += 1
                    if strDefect(cw) < d0 and Aobj_node(cw) >= a0:
                        canonW_ok += 1
    print(f"genuine defective trees n<={maxn}: {genuine}")
    print(f"  Type L (a LEAF local move straightens; F2-certified)     : {L_cov}/{genuine}")
    print(f"  Type W (needs whole-child move, min size>=2)             : {W_needed}/{genuine}")
    print(f"    W min-moved-size histogram: {dict(sorted(wsizes.items()))}")
    print(f"  canonical-W (child -> lowest-degree local target):")
    print(f"    applies to W-needed: {canonW_applies}/{W_needed}")
    print(f"    Aobj-nondown among applies: {canonW_ok}/{canonW_applies}")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
