"""
A5: Case-B (symmetric multi-hub) move-rule stress test — the RealObligationA residual.

leaf-path-extension (Case A) straightens 93% with a clean F2 Aobj certificate (a4). The 7% misses are
symmetric multi-hub trees whose winning move is a whole-hub relocation (a4_miss_move). This probe tests
DETERMINISTIC candidate rules for Case B against exactly those miss trees, checking all three
RealObligationA clauses (usize preserved [free for SPR], strDefect strictly down, Aobj not down):

  R_greedy_aobj : among strDefect-down SPR moves, pick the one MAXIMIZING Aobj (the argmax witness).
  R_maxgap      : pick the strDefect-down move maximizing the degree gap (deg_src - deg_tgt).
  R_hub_to_leaf : move the largest non-piece subtree onto a lowest-degree (leaf) target.
  R_min_child   : move the SMALLEST non-piece subtree onto the lowest-degree target.

Reports per-rule coverage over the miss set, and extracts a refuting instance (Aobj-DOWN) for any rule
that is not universal — that instance is the kernel-gateable negative control (a5_negctl_instance.json).
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
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
            tp = rooted_from({i: list(H.neighbors(i)) for i in range(n)}, 0, -1)
            if strDefect(tp) < d0 and Aobj_node(tp) >= a0:
                return True
    return False

def relocations(t):
    """All SPR reparents: (tp, movedsize, deg_src, deg_tgt) re-rooted at original root 0."""
    n, edges = to_edges(t)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    deg = {i: G.degree(i) for i in range(n)}
    out = []
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
                out.append((tp, movedsize, deg[src], deg[tgt]))
    return out

# ---- deterministic candidate rules: each returns the chosen after-tree or None ----
def rule(name, t, d0, a0, rels):
    down = [(tp, sz, ds, dt) for (tp, sz, ds, dt) in rels if strDefect(tp) < d0]
    if not down:
        return None
    if name == "R_greedy_aobj":
        best = max(down, key=lambda r: Aobj_node(r[0])); return best[0]
    if name == "R_maxgap":
        best = max(down, key=lambda r: r[2] - r[3]); return best[0]
    if name == "R_hub_to_leaf":
        cand = [r for r in down if r[3] == 1]  # target is a leaf
        if not cand: return None
        best = max(cand, key=lambda r: r[1]); return best[0]  # largest moved subtree
    if name == "R_min_child":
        cand = [r for r in down if r[3] == 1]
        if not cand: return None
        best = min(cand, key=lambda r: r[1]); return best[0]  # smallest moved subtree
    raise ValueError(name)

RULES = ["R_greedy_aobj", "R_maxgap", "R_hub_to_leaf", "R_min_child"]

def run(maxn=12):
    misses = 0
    ok = {r: 0 for r in RULES}          # strDefect-down AND Aobj-up
    applies = {r: 0 for r in RULES}     # rule produced a move at all
    refute = {r: None for r in RULES}   # first (tree, after, a_before, a_after) where Aobj went DOWN
    for n in range(2, maxn + 1):
        for t in gen_trees(n):
            d0 = strDefect(t)
            if d0 == 0: continue
            if pathext_can_straighten(t): continue      # Case A handled
            misses += 1
            a0 = Aobj_node(t)
            rels = relocations(t)
            for r in RULES:
                tp = rule(r, t, d0, a0, rels)
                if tp is None: continue
                applies[r] += 1
                atp = Aobj_node(tp)
                if atp >= a0:
                    ok[r] += 1
                elif refute[r] is None:
                    refute[r] = (t, tp, str(a0), str(atp))
    print(f"Case-B miss trees (root-fixed strDefect>0, leaf-path-ext FAILS), n<={maxn}: {misses}")
    for r in RULES:
        cov = f"{ok[r]}/{misses}"
        note = "UNIVERSAL" if ok[r] == misses and applies[r] == misses else \
               (f"applies {applies[r]}, Aobj-up {ok[r]}")
        print(f"  {r:16s}: {cov:>10s}  [{note}]")
    # export the first refuting instance among the STRUCTURAL rules (for the kernel-gated neg control)
    for r in ("R_maxgap", "R_hub_to_leaf", "R_min_child"):
        if refute[r] is not None:
            t, tp, ab, aa = refute[r]
            print(f"\n  REFUTING instance for {r}: Aobj {ab} -> {aa} (DOWN)")
            print(f"    before={t}\n    after ={tp}")
            json.dump({"rule": r, "before": repr(t), "after": repr(tp),
                       "aobj_before": ab, "aobj_after": aa},
                      open(os.path.join(os.path.dirname(__file__), "a5_negctl_instance.json"), "w"), indent=2)
            break

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
