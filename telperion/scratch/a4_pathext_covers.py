"""
A4 (picking up a3): the PIVOTAL RealObligationA question.

a3 established:
  (i)  well-posedness: every genuine rooted tree (root-fixed strDefect>0) has SOME SPR move that
       is strDefect-DOWN and Aobj-UP  (n<=12, 100%).
  (ii) the leaf-onto-leaf PATH-EXTENSION move (move a pendant leaf w onto another leaf v) is
       UNCONDITIONALLY Aobj-nondecreasing, with the closed form (a3_F2_closed.py)
           dAobj = P*(n^2 + n*Q + 4*Q)/(2(n+1)(n+2)) >= 0   (P,Q,n >= 0).

MISSING LINK for RealObligationA: is a leaf path-extension that ALSO strictly reduces root-fixed
strDefect available for EVERY genuine tree?  If yes, RealObligationA's existence form collapses to
"leaf path-extension" whose Aobj clause is the closed-form certificate (ii) and whose strDefect
clause is a finite combinatorial check -- no negative Aobj tail to fight.

This probe answers it exactly at extended n, and (if <100%) reports what the leaf-path-extension
family MISSES so the gap is precise.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, LEAF
from a3_wellposed import strDefect, gen_trees, to_edges, rooted_from
import networkx as nx

def leaves_of(G):
    return [i for i in G.nodes() if G.degree(i) == 1]

def pathext_afters(t):
    """All leaf-onto-leaf path-extensions, re-rooted at original root 0.
    Move pendant leaf w (neighbor u) onto pendant leaf v (v != w, u != v): remove (u,w), add (v,w)."""
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    lv = leaves_of(G)
    for w in lv:
        u = next(iter(G.neighbors(w)))
        for v in lv:
            if v == w or v == u:
                continue
            H = G.copy(); H.remove_edge(u, w); H.add_edge(v, w)
            if H.number_of_edges() != n - 1 or not nx.is_connected(H):
                continue
            adj = {i: list(H.neighbors(i)) for i in range(n)}
            yield rooted_from(adj, 0, -1)

def run(maxn=13):
    genuine = 0
    covered = 0
    aobj_viol = 0
    misses = []
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0:
                continue
            genuine += 1
            a0 = Aobj_node(t)
            hit = False
            for tp in pathext_afters(t):
                if strDefect(tp) < d0:
                    # Aobj-up should be automatic (F2_closed); verify to be safe.
                    if Aobj_node(tp) >= a0:
                        hit = True
                    else:
                        aobj_viol += 1
            if hit:
                covered += 1
            else:
                misses.append((n, t, d0))
    print(f"genuine rooted UTrees (root-fixed strDefect>0), n<={maxn}: {genuine}")
    print(f"  covered by a leaf-path-extension that is strDefect-DOWN and Aobj-UP: {covered}")
    print(f"  NOT covered by leaf-path-extension: {len(misses)}")
    print(f"  (sanity) strDefect-down path-exts that were Aobj-DOWN (should be 0): {aobj_viol}")
    for m in misses[:12]:
        print("   MISS:", m)

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 13)
