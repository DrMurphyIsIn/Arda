"""
A6: is the coupled well-posedness move LOCAL to a deepest defective node?

RealObligationA's existence leg = "every defective tree has a strDefect-down + Aobj-nondown SPR move".
If that move can ALWAYS be taken by relocating a NON-PIECE CHILD of a DEEPEST defective node u
(npCount(u) ≥ 2, no deeper node has npCount ≥ 2) — target anywhere outside that child's subtree —
then the strDefect-reduction is LOCAL (the excess non-piece child count at u drops by 1) and only the
target choice is global (handled by argmax-Aobj).  That makes the lemma a FINITE local case analysis on
u's child-degree profile — emittable / kernel-certifiable.  This probe measures that coverage exactly.

Comparison classes per defective tree:
  ALL      : any SPR relocation (the full well-posedness, = 100% baseline).
  CHILD@u  : relocate a non-piece child of a DEEPEST defective node u, target anywhere outside it.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, isPiece
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
import networkx as nx

def build(t):
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    children = {j: [] for j in range(n)}
    for (p, c) in edges:
        children[p].append(c)          # edges are (parent, child) in DFS order, root = 0
    adj = {i: list(G.neighbors(i)) for i in range(n)}
    return n, G, children, adj

def subtree(adj, node, parent):
    return rooted_from(adj, node, parent)

def npcount_at(adj, u, parent, children):
    return sum(0 if isPiece(subtree(adj, c, u)) else 1 for c in children[u])

def depth_map(children, root=0):
    d = {root: 0}; stack = [root]
    while stack:
        x = stack.pop()
        for c in children[x]:
            d[c] = d[x] + 1; stack.append(c)
    return d

def deepest_defective(adj, children, n):
    """A node u with npCount(u) ≥ 2 of MAX depth (ties: lowest id). None if strDefect concentrated
    in a single-non-piece chain with no ≥2 branching (cannot happen when strDefect>0)."""
    dep = depth_map(children)
    best = None
    for u in range(n):
        # parent of u:
        if npcount_at(adj, u, _parent_of(children, u), children) >= 2:
            if best is None or dep[u] > dep[best]:
                best = u
    return best

def _parent_of(children, u):
    for p, cs in children.items():
        if u in cs: return p
    return -1

def child_at_u_moves(t):
    """Relocations of a NON-PIECE child of a deepest defective node u, target anywhere outside it."""
    n, G, children, adj = build(t)
    u = deepest_defective(adj, children, n)
    if u is None: return
    for c in children[u]:
        if isPiece(subtree(adj, c, u)):
            continue
        comp_c = nx.node_connected_component(nx.restricted_view(G, [], [(u, c)]), c)  # c's subtree
        for v in range(n):
            if v == u or v in comp_c:
                continue
            H = G.copy(); H.remove_edge(u, c); H.add_edge(v, c)
            if H.number_of_edges() != n - 1 or not nx.is_connected(H):
                continue
            yield rooted_from({i: list(H.neighbors(i)) for i in range(n)}, 0, -1)

def local_moves(t):
    """All SPR relocations CONFINED to the subtree of a deepest defective node u — the removed edge
    AND the target all lie in subtree(u).  Captures whole-child relocations AND leaf-path-extensions
    inside a child (which turn a nested-defect child into a piece).  Re-rooted at global 0."""
    n, G, children, adj = build(t)
    u = deepest_defective(adj, children, n)
    if u is None: return
    par = _parent_of(children, u)
    sub = nx.node_connected_component(nx.restricted_view(G, [], [(u, par)] if par >= 0 else []), u)
    for (x, y) in list(G.edges()):
        if x not in sub or y not in sub:
            continue
        for (src, w) in [(x, y), (y, x)]:
            H = G.copy(); H.remove_edge(src, w)
            keep = nx.node_connected_component(H, src)
            for tgt in keep:
                if tgt == src or tgt not in sub: continue
                Gp = H.copy(); Gp.add_edge(tgt, w)
                if Gp.number_of_edges() != n - 1 or not nx.is_connected(Gp): continue
                yield rooted_from({i: list(Gp.neighbors(i)) for i in range(n)}, 0, -1)

def all_moves(t):
    n, G, children, adj = build(t)
    for (x, y) in list(G.edges()):
        for (src, w) in [(x, y), (y, x)]:
            H = G.copy(); H.remove_edge(src, w)
            keep = nx.node_connected_component(H, src)
            for tgt in keep:
                if tgt == src: continue
                Gp = H.copy(); Gp.add_edge(tgt, w)
                if Gp.number_of_edges() != n - 1 or not nx.is_connected(Gp): continue
                yield rooted_from({i: list(Gp.neighbors(i)) for i in range(n)}, 0, -1)

def run(maxn=12):
    genuine = 0; all_ok = 0; child_ok = 0; local_ok = 0; child_miss = []
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0: continue
            genuine += 1
            a0 = Aobj_node(t)
            if any(strDefect(tp) < d0 and Aobj_node(tp) >= a0 for tp in all_moves(t)):
                all_ok += 1
            if any(strDefect(tp) < d0 and Aobj_node(tp) >= a0 for tp in child_at_u_moves(t)):
                child_ok += 1
            if any(strDefect(tp) < d0 and Aobj_node(tp) >= a0 for tp in local_moves(t)):
                local_ok += 1
            else:
                child_miss.append((n, t, d0))
    print(f"genuine defective trees n<={maxn}: {genuine}")
    print(f"  ALL relocations well-posed (baseline)                : {all_ok}/{genuine}")
    print(f"  CHILD@deepest-defect (whole-child relocation)        : {child_ok}/{genuine}")
    print(f"  LOCAL@deepest-defect (any move in subtree(u))        : {local_ok}/{genuine}")
    print(f"  LOCAL misses: {len(child_miss)}")
    for m in child_miss[:10]:
        print("    LOCAL-MISS:", m)

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
