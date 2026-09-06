"""
A8: pin the Type-W local target — the 8% whole-hub residual of RealObligationA.

Type-W trees (a7): no leaf move straightens; a non-piece child of the deepest defect u must be relocated.
Canonical "lowest-degree local target" was Aobj-nondown only 60%.  Test structurally-motivated targets that
build a CATERPILLAR spine (the Aobj-maximizing direction), over exactly the Type-W trees, for a rule that is
(a) strDefect-down and (b) Aobj-nondecreasing — i.e. a deterministic Type-W witness with a hope of a closed form:

  W_sib_leaf   : relocate the first non-piece child c of u onto a LEAF-child of a sibling non-piece child c'.
  W_sib_direct : relocate c onto a sibling non-piece child c' directly (c becomes a child of c').
  W_deep_leaf  : relocate c onto the DEEPEST leaf in subtree(u).
  W_argmax     : (reference) among strDefect-down subtree(u) moves, the argmax-Aobj one (=100% by a6).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, isPiece
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
from a6_locality import build, deepest_defective, _parent_of, subtree, depth_map
from a7_taxonomy import local_moves_sized
import networkx as nx

def is_typeW(t, d0, a0):
    good = [(tp, sz) for (tp, sz, dt) in local_moves_sized(t)
            if strDefect(tp) < d0 and Aobj_node(tp) >= a0]
    return bool(good) and min(sz for _, sz in good) >= 2

def relocate(G, n, u, c, v):
    H = G.copy(); H.remove_edge(u, c); H.add_edge(v, c)
    if H.number_of_edges() != n - 1 or not nx.is_connected(H): return None
    return rooted_from({i: list(H.neighbors(i)) for i in range(n)}, 0, -1)

def apply_rule(name, t):
    n, G, children, adj = build(t)
    u = deepest_defective(adj, children, n)
    if u is None: return None
    par = _parent_of(children, u)
    sub = nx.node_connected_component(nx.restricted_view(G, [], [(u, par)] if par >= 0 else []), u)
    dep = depth_map(children)
    nonpiece = [c for c in children[u] if not isPiece(subtree(adj, c, u))]
    if not nonpiece: return None
    c = nonpiece[0]
    comp_c = nx.node_connected_component(nx.restricted_view(G, [], [(u, c)]), c)
    sibs = [s for s in nonpiece if s != c]
    if name == "W_sib_leaf":
        for c2 in sibs:
            leaves = [x for x in children[c2] if G.degree(x) == 1]
            if leaves: return relocate(G, n, u, c, leaves[0])
        return None
    if name == "W_sib_direct":
        return relocate(G, n, u, c, sibs[0]) if sibs else None
    if name == "W_deep_leaf":
        cand = [v for v in sub if v not in comp_c and v != u and G.degree(v) == 1]
        if not cand: return None
        v = max(cand, key=lambda z: dep[z]); return relocate(G, n, u, c, v)
    if name == "W_argmax":
        a0 = Aobj_node(t); d0 = strDefect(t)
        good = [tp for (tp, sz, dt) in local_moves_sized(t) if strDefect(tp) < d0 and Aobj_node(tp) >= a0]
        return max(good, key=Aobj_node) if good else None
    raise ValueError(name)

RULES = ["W_sib_leaf", "W_sib_direct", "W_deep_leaf", "W_argmax"]

STRUCT = ["W_deep_leaf", "W_sib_leaf", "W_sib_direct"]   # fixed, closed-form-able rules (no search)

def run(maxn=12):
    W = 0
    ok = {r: 0 for r in RULES}; applies = {r: 0 for r in RULES}
    union_ok = 0; union_miss = []
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0: continue
            a0 = Aobj_node(t)
            if not is_typeW(t, d0, a0): continue
            W += 1
            hit_union = False
            for r in RULES:
                tp = apply_rule(r, t)
                if tp is None: continue
                applies[r] += 1
                good = strDefect(tp) < d0 and Aobj_node(tp) >= a0
                if good: ok[r] += 1
                if good and r in STRUCT: hit_union = True
            if hit_union: union_ok += 1
            else: union_miss.append((n, t))
    print(f"Type-W trees n<={maxn}: {W}")
    for r in RULES:
        print(f"  {r:14s}: Aobj-nondown+strDefect-down {ok[r]}/{W}   (applies {applies[r]})")
    print(f"  UNION of {STRUCT}: {union_ok}/{W}   (misses {len(union_miss)})")
    for m in union_miss[:8]:
        print("    UNION-MISS:", m)

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
