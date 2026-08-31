"""Phase-0 empirical de-risk for the Lean obligation `StraightProgress_sized`.

GO/NO-GO GATE
-------------
Is `StraightProgress_sized` dischargeable by a LOCAL move?

`StraightProgress_sized` (informal): for every rooted tree t on n vertices that is
NOT a hub-backbone (strDefect(t) > 0), there exists another rooted tree t' on the
SAME n vertices, reachable by a *local* structural move, with

        strDefect(t') < strDefect(t)   AND   Aobj(t') >= Aobj(t).

Iterating such a move drives strDefect to 0 (a hub-backbone) without decreasing Aobj,
which is the "straightening" half of the extremality argument.

Here we take LOCAL = SPR (subtree-prune-and-regraft) distance 1: remove one edge
(splitting the tree into two components) and reattach the pruned component by a single
new edge to any vertex of the other component. We ALSO allow re-choosing the root
(rooting is free -- strDefect depends on the root, Aobj does not).

DEFINITIONS (mirroring the Lean, on ROOTED trees):
  Aobj(T) = per(L(T)) / prod_v deg(v)   -- root-invariant graph property.
      Computed via the exact matching-sum identity
          per(L(T)) = sum over matchings M of prod_{v unmatched} deg(v)
      (reused from kelmans_mixed_load.pi_literal, itself anchored vs a brute permanent).
  isLeaf(node cs)   = (cs == [])
  isCherry(node cs) = (cs == [x] and isLeaf(x))      -- a single leaf child
  isArm(node cs)    = all(isCherry(c) for c in cs)   -- every child is a cherry (incl. empty => leaf)
  isPiece(c)        = isArm(c) or isCherry(c)
  strDefect(node cs)= max(0, (#non-piece children) - 1)
                        + sum(strDefect(c) for c in cs if not isPiece(c))
                      [Nat-truncated subtraction].  strDefect(t) = 0 iff t is a hub-backbone.

Exact rational arithmetic throughout (fractions.Fraction).
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

import networkx as nx

# Reuse the anchored matching-sum Aobj machinery.
from kelmans_mixed_load import pi_literal, _brute_permanent, psi_weighted


# --------------------------------------------------------------------------- Aobj
def Aobj(G: nx.Graph) -> Fr:
    """Aobj(T) = per(L(T)) / prod deg, exact, via the matching-sum identity."""
    return pi_literal(G)


# ---------------------------------------------------- rooted recognizers / defect
# A rooted tree is represented lazily against an unrooted nx.Graph G plus a root r.
# children(v, parent) = neighbours of v other than parent.
def _children(G, v, parent):
    return [w for w in G.neighbors(v) if w != parent]


def isLeaf(G, v, parent):
    return len(_children(G, v, parent)) == 0


def isCherry(G, v, parent):
    ch = _children(G, v, parent)
    return len(ch) == 1 and isLeaf(G, ch[0], v)


def isArm(G, v, parent):
    ch = _children(G, v, parent)
    return all(isCherry(G, c, v) for c in ch)


def isPiece(G, v, parent):
    return isArm(G, v, parent) or isCherry(G, v, parent)


def strDefect(G, v, parent):
    ch = _children(G, v, parent)
    nonpiece = [c for c in ch if not isPiece(G, c, v)]
    local = max(0, len(nonpiece) - 1)
    return local + sum(strDefect(G, c, v) for c in nonpiece)


def rooted_defect(G, root):
    return strDefect(G, root, None)


# --------------------------------------------------------------- SPR neighborhood
def spr_neighbors(G: nx.Graph):
    """Yield every tree on the SAME vertex set at SPR distance 1 from G.

    Remove one edge (u,v) -> two components A (containing u) and B (containing v).
    Reattach: pick a vertex a in the pruned component and a vertex b in the other,
    add edge (a,b).  We yield the resulting graph (as a frozen edge set) once per
    distinct result.  Includes the identity via reattaching the same edge, which we
    drop by comparing edge sets.
    """
    nodes = list(G.nodes())
    orig_edges = frozenset(frozenset(e) for e in G.edges())
    seen = set()
    for (u, v) in list(G.edges()):
        H = G.copy()
        H.remove_edge(u, v)
        compU = nx.node_connected_component(H, u)
        compV = nx.node_connected_component(H, v)
        # Prune component containing v, reattach to some vertex in compU (and vice versa).
        # Both directions are covered by iterating all (a in one comp, b in other).
        for a in compU:
            for b in compV:
                newedges = frozenset(frozenset(e) for e in H.edges()) | {frozenset((a, b))}
                if newedges == orig_edges:
                    continue
                if newedges in seen:
                    continue
                seen.add(newedges)
                Gp = nx.Graph()
                Gp.add_nodes_from(nodes)
                for e in newedges:
                    x, y = tuple(e)
                    Gp.add_edge(x, y)
                # must still be a tree on all n vertices
                if Gp.number_of_edges() == len(nodes) - 1 and nx.is_connected(Gp):
                    yield Gp


# ------------------------------------------------------------------- move witness
def describe_move(G, root, defG, Gp, rootp, defGp):
    """Classify the witnessing SPR move between (G,root) and (Gp,rootp)."""
    eG = frozenset(frozenset(e) for e in G.edges())
    eGp = frozenset(frozenset(e) for e in Gp.edges())
    removed = eG - eGp
    added = eGp - eG
    rem = tuple(sorted(tuple(sorted(e)) for e in removed))
    add = tuple(sorted(tuple(sorted(e)) for e in added))
    reroot = (root != rootp)
    return {
        "removed_edge": rem,
        "added_edge": add,
        "reroot": reroot,
    }


# -------------------------------------------------------------------------- driver
def min_defect_over_roots(G):
    return min(rooted_defect(G, r) for r in G.nodes())


def analyze(n_max=12, verbose_failures=True):
    Aobj_cache = {}

    def aobj(G):
        key = frozenset(frozenset(e) for e in G.edges())
        if key not in Aobj_cache:
            Aobj_cache[key] = Aobj(G)
        return Aobj_cache[key]

    total_rooted_nonbackbone = 0
    failures = []
    tie_moves = 0
    strict_moves = 0
    defect_drops = {}  # drop amount -> count
    move_families = {"reroot_only": 0, "spr": 0, "spr_plus_reroot": 0}
    n_range_done = []
    # Track the SUBSET where the graph is genuinely NOT a hub-backbone under ANY
    # rooting (min defect over roots > 0): these are the cases that CANNOT be
    # discharged by a mere reroot and genuinely need an SPR structural move.
    genuine_total = 0
    genuine_failures = 0
    genuine_families = {"spr": 0, "spr_plus_reroot": 0}
    genuine_ties = 0
    genuine_strict = 0
    genuine_examples = []

    for n in range(2, n_max + 1):
        n_trees = 0
        for T0 in nx.nonisomorphic_trees(n):
            n_trees += 1
            T = nx.convert_node_labels_to_integers(T0)
            aT = aobj(T)
            # Precompute all SPR neighbor graphs once per unrooted tree.
            neighbors = list(spr_neighbors(T))

            # ---- GRAPH-LEVEL "genuine defect" analysis ----
            # A tree is genuinely non-backbone iff NO rooting achieves strDefect 0.
            # For these, a reroot cannot discharge the obligation: a real SPR move
            # (to a DIFFERENT graph) with Aobj non-decreasing and lower min-defect
            # must exist.
            mdT = min_defect_over_roots(T)
            if mdT > 0:
                genuine_total += 1
                g_found = None
                for Gp in neighbors:
                    aGp = aobj(Gp)
                    if aGp < aT:
                        continue
                    mdGp = min_defect_over_roots(Gp)
                    if mdGp < mdT:
                        g_found = (Gp, mdGp, aGp)
                        break
                if g_found is None:
                    genuine_failures += 1
                    if verbose_failures:
                        print(f"  GENUINE-FAILURE n={n} min_defect={mdT} "
                              f"edges={sorted(tuple(sorted(e)) for e in T.edges())}")
                else:
                    Gp, mdGp, aGp = g_found
                    genuine_families["spr"] += 1
                    if aGp > aT:
                        genuine_strict += 1
                    else:
                        genuine_ties += 1
                    if len(genuine_examples) < 20:
                        eT = frozenset(frozenset(e) for e in T.edges())
                        eGp = frozenset(frozenset(e) for e in Gp.edges())
                        genuine_examples.append({
                            "n": n,
                            "edges_before": sorted(tuple(sorted(e)) for e in T.edges()),
                            "min_defect_before": mdT,
                            "min_defect_after": mdGp,
                            "removed": sorted(tuple(sorted(e)) for e in (eT - eGp)),
                            "added": sorted(tuple(sorted(e)) for e in (eGp - eT)),
                            "Aobj_before": aT,
                            "Aobj_after": aGp,
                            "Aobj_delta": aGp - aT,
                            "degseq_before": sorted((T.degree(v) for v in T.nodes()), reverse=True),
                            "degseq_after": sorted((Gp.degree(v) for v in Gp.nodes()), reverse=True),
                        })

            for root in T.nodes():
                defG = rooted_defect(T, root)
                if defG == 0:
                    continue  # already a hub-backbone rooting
                total_rooted_nonbackbone += 1

                # Search for a local move: (a) same graph, different root (reroot),
                # or (b) an SPR neighbor graph with any rooting.
                found = None
                # (a) reroot-only moves on the SAME graph
                for root2 in T.nodes():
                    if root2 == root:
                        continue
                    d2 = rooted_defect(T, root2)
                    if d2 < defG and aT >= aT:  # Aobj identical (same graph)
                        found = (T, root2, d2, aT, "reroot_only")
                        break
                # (b) SPR neighbor graphs (possibly with reroot)
                if found is None:
                    best = None
                    for Gp in neighbors:
                        aGp = aobj(Gp)
                        if aGp < aT:
                            continue  # Aobj must not decrease
                        for root2 in Gp.nodes():
                            d2 = rooted_defect(Gp, root2)
                            if d2 < defG:
                                fam = "spr"
                                cand = (Gp, root2, d2, aGp, fam)
                                # prefer strict Aobj increase & bigger defect drop for reporting
                                if best is None:
                                    best = cand
                                else:
                                    # prefer larger defect drop, then larger Aobj
                                    if (defG - d2) > (defG - best[2]) or aGp > best[3]:
                                        best = cand
                    if best is not None:
                        found = best

                if found is None:
                    failures.append((n, T, root, defG))
                    if verbose_failures and len(failures) <= 25:
                        print(f"  FAILURE n={n} root={root} strDefect={defG}")
                        print(f"    edges={sorted(tuple(sorted(e)) for e in T.edges())}")
                else:
                    Gp, root2, d2, aGp, fam = found
                    drop = defG - d2
                    defect_drops[drop] = defect_drops.get(drop, 0) + 1
                    if aGp > aT:
                        strict_moves += 1
                    elif aGp == aT:
                        tie_moves += 1
                    if fam == "reroot_only":
                        move_families["reroot_only"] += 1
                    else:
                        # did it also require a reroot?
                        info = describe_move(T, root, defG, Gp, root2, d2)
                        if info["reroot"]:
                            move_families["spr_plus_reroot"] += 1
                        else:
                            move_families["spr"] += 1
        n_range_done.append((n, n_trees))
        print(f"[n={n}] {n_trees} nonisomorphic trees processed; "
              f"cumulative non-backbone rooted={total_rooted_nonbackbone}, "
              f"failures so far={len(failures)}")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"n range: 2..{n_max}")
    for (n, c) in n_range_done:
        print(f"  n={n:2d}: {c} nonisomorphic unrooted trees")
    print(f"\nTotal non-backbone rooted trees tested: {total_rooted_nonbackbone}")
    print(f"FAILURES (no local defect-reducing, Aobj-nondecreasing move): {len(failures)}")
    print(f"\nAmong the {total_rooted_nonbackbone - len(failures)} with a witnessing move:")
    print(f"  strict Aobj increase : {strict_moves}")
    print(f"  Aobj tie (equal)     : {tie_moves}")
    print(f"  defect-drop histogram (drop amount -> count): "
          f"{dict(sorted(defect_drops.items()))}")
    print(f"  move family: {move_families}")

    print("\n" + "-" * 70)
    print("GENUINE (graph-level) subset: trees with NO defect-0 rooting")
    print("  (these CANNOT be fixed by rerooting -- they need a real SPR move)")
    print("-" * 70)
    print(f"  genuine non-backbone graphs tested : {genuine_total}")
    print(f"  genuine FAILURES (no SPR move lowers min-defect w/ Aobj>=): {genuine_failures}")
    print(f"  witnessing SPR moves -- strict Aobj increase: {genuine_strict}, ties: {genuine_ties}")
    if genuine_examples:
        print("\n  GENUINE-CASE WITNESS EXAMPLES (need a real SPR move):")
        for ex in genuine_examples:
            print(f"    n={ex['n']} minDefect {ex['min_defect_before']}->{ex['min_defect_after']}  "
                  f"remove {ex['removed']} add {ex['added']}")
            print(f"        degseq {ex['degseq_before']} -> {ex['degseq_after']}")
            print(f"        Aobj {ex['Aobj_before']} -> {ex['Aobj_after']}  "
                  f"(delta = +{ex['Aobj_delta']})")

    if failures:
        print("\n*** VERDICT: NOT LOCALLY DISCHARGEABLE ***")
        print(f"    {len(failures)} stuck configurations found (see above).")
    else:
        print("\n*** VERDICT: LOCAL-MOVE VIABLE ***")
        print("    Every non-backbone rooted tree has a local (SPR<=1 + reroot)")
        print("    move that strictly lowers strDefect without decreasing Aobj.")

    return {
        "total": total_rooted_nonbackbone,
        "failures": failures,
        "strict": strict_moves,
        "ties": tie_moves,
        "defect_drops": defect_drops,
        "move_families": move_families,
    }


# ------------------------------------------------------------------ sanity checks
def _sanity():
    """Verify Aobj and recognizers on tiny known cases."""
    # P3: path 0-1-2.  deg = 1,2,1.  L = [[1,-1,0],[-1,2,-1],[0,-1,1]].
    # per(L): matchings of the path graph: {} -> prod deg =1*2*1=2; {01}->deg(2)=1;
    #   {12}->deg(0)=1.  Total per = 4.  Aobj = 4/(1*2*1)=2.
    P3 = nx.path_graph(3)
    assert Aobj(P3) == Fr(2), Aobj(P3)
    assert _brute_permanent(P3) == 4, _brute_permanent(P3)

    # Star K_{1,3}: center 0, leaves 1,2,3.  deg=3,1,1,1.  prod deg=3.
    # matchings: {} -> 3*1*1*1=3; {0,i} for i=1,2,3 -> prod deg of unmatched (three
    #   vertices: the other two leaves deg1, deg1, and... center matched) = 1*1=1 each
    #   -> 3.  per=6.  Aobj=6/3=2.
    K13 = nx.star_graph(3)
    assert _brute_permanent(K13) == 6, _brute_permanent(K13)
    assert Aobj(K13) == Fr(2), Aobj(K13)

    # recognizer sanity on a small caterpillar rooted at an end:
    #   0-1-2 with a leaf 3 on 1.  Root at 0.
    #   node0 -> child 1; node1 -> children 2,3 (2 leaf, 3 leaf). node1 isArm (both cherries? no:
    #     2 and 3 are leaves not cherries).  isCherry(2 rooted at1)=leaf so isArm needs children cherries.
    G = nx.Graph([(0, 1), (1, 2), (1, 3)])
    # root 0: child 1; 1 has children 2,3 both leaves -> isArm(1)? all children cherries? a leaf
    # is NOT a cherry (cherry = single leaf child), but isArm over EMPTY... here 2,3 are leaves.
    # isCherry(2)=False(leaf). so isArm(1)=all(isCherry(2),isCherry(3))=all(False,False)=False.
    # Actually leaves: isCherry(leaf)=False. So node1 not arm. This is fine, just exercising code.
    _ = rooted_defect(G, 0)
    print("[sanity] Aobj(P3)=2, per(P3)=4, Aobj(K13)=2, per(K13)=6 -- OK")
    print("[sanity] recognizers run without error -- OK")


if __name__ == "__main__":
    _sanity()
    nmax = 12
    if len(sys.argv) > 1:
        nmax = int(sys.argv[1])
    analyze(n_max=nmax)
