"""Phase-0 (B0) de-risk for `StraightProgress_sized` via the SPECIFIC FLP move (RealObligationA, Type-L).

Distinct from `phase0_straightprogress_sized.py` (which tested GENERIC SPR and found 100% coverage
through n=12).  Here we test the ONE move that is actually formalized in Lean -- the leaf-onto-leaf
PATH-EXTENSION (`aobj_flp_context_lift_crest`) -- to measure its Type-L coverage and CHARACTERIZE the
Type-W residual (the ~8% that needs a whole-hub / k-star relocation, Case-B).

THE FLP MOVE (mirrors BGSCLRealOblACaseAIdentity.lean, exact cavity model):
    a node  u = node(leaf :: leaf :: rest)   -- two BARE-LEAF children v,w plus other children `rest`
    becomes u' = node(stem :: rest),  stem = node[leaf]   -- w stacked under v, extending a path.
  Graph form: pick a vertex u with >=2 leaf-neighbours; remove edge (u,w), add edge (v,w).
  Vertex-preserving; `Aobj` non-decreasing (the cert increment P*(n^2+nQ+4Q)/(2(n+1)(n+2)) >= 0);
  reduces `strDefect` exactly when it turns u into an arm (piece).

TAXONOMY (per `RealObligationA` in the Lean):
    Type-L : a genuinely-defective tree (min strDefect over roots > 0) admits an FLP move that
             strictly lowers strDefect with Aobj non-decreasing.
    Type-W : genuinely defective but NO FLP move lowers strDefect -- needs whole-hub relocation.

Exact rational arithmetic (fractions.Fraction), Aobj engine anchored in a3_derisk (matches
unrooted per(L)/prod deg, root-invariant, self-checked).
"""
from __future__ import annotations

import os
import sys
from collections import Counter
from fractions import Fraction as Fr

import networkx as nx

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "telperion", "scratch"))
from a3_derisk import (  # noqa: E402
    LEAF, Aobj_node, strDefect, isPiece, Ztot_sub, qSum, udeg,
)

STEM = (LEAF,)  # node[leaf]


# ----------------------------------------------------------- rooted tuple builders
def rooted_tuple(G: nx.Graph, root, parent=None):
    """Build the nested-tuple UTree rooted at `root` (children order irrelevant to Aobj/defect)."""
    return tuple(rooted_tuple(G, c, root) for c in G.neighbors(root) if c != parent)


def min_defect(G: nx.Graph):
    return min(strDefect(rooted_tuple(G, r)) for r in G.nodes())


def aobj_graph(G: nx.Graph):
    # root-invariant; root anywhere
    r = next(iter(G.nodes()))
    return Aobj_node(rooted_tuple(G, r))


# ----------------------------------------------------------------- the FLP move set
def flp_moves(G: nx.Graph):
    """Yield (G', u, (v,w)) for every FLP site: u has >=2 leaf-neighbours v,w; stack w under v."""
    seen = set()
    for u in G.nodes():
        leaves = [x for x in G.neighbors(u) if G.degree(x) == 1]
        if len(leaves) < 2:
            continue
        # leaves are interchangeable; one representative pair (v,w) per u suffices
        v, w = leaves[0], leaves[1]
        H = G.copy()
        H.remove_edge(u, w)
        H.add_edge(v, w)
        key = frozenset(frozenset(e) for e in H.edges())
        if key in seen:
            continue
        seen.add(key)
        yield H, u, (v, w)


# ------------------------------------------------------- cert oracle at the acted node
def cert_increment(rest_children):
    """The three cone-cert quantities + closed-form increment for a move at u with children
    [leaf, leaf, *rest].  P = prod Ztot(dtSub K over rest), Q = qSum(rest), n = |rest|.
    Increment (subtree Aobj, u as root) = P*(n^2 + n*Q + 4*Q)/(2(n+1)(n+2)).  Returns dict."""
    rest = tuple(rest_children)
    n = len(rest)
    P = Fr(1)
    for K in rest:
        P *= Ztot_sub(K)
    Q = qSum(rest)
    F2_num = n * n + n * Q + 4 * Q                       # cert 1: F2 numerator (>=0)
    incr = P * F2_num / (2 * (n + 1) * (n + 2))          # closed-form Aobj increment
    # direct check: Aobj(after) - Aobj(before) rooted at u
    before = (LEAF, LEAF) + rest
    after = (STEM,) + rest
    direct = Aobj_node(after) - Aobj_node(before)
    return {"n": n, "P": P, "Q": Q, "F2_num": F2_num,
            "closed_form": incr, "direct": direct, "match": incr == direct}


def characterize_typeW(G: nx.Graph):
    """Describe a Type-W residual: degree sequence + whether it is a symmetric multi-hub node[H,H]."""
    degseq = sorted((d for _, d in G.degree()), reverse=True)
    # symmetric-hub signature: two equal-degree adjacent hubs each carrying identical star arms
    hubs = [v for v, d in G.degree() if d >= 3]
    sym = False
    for a in hubs:
        for b in G.neighbors(a):
            if G.degree(b) == G.degree(a) and G.degree(a) >= 3:
                sym = True
    return {"degseq": tuple(degseq), "n_hubs_ge3": len(hubs), "symmetric_adjacent_hubs": sym}


# --------------------------------------------------------------------------- driver
def analyze(n_max=14):
    genuine = 0
    type_L = 0
    type_W = 0
    aobj_violation = 0          # FLP witness that DECREASES Aobj (must be 0)
    cert_mismatch = 0           # closed-form != direct (must be 0)
    drop_hist = Counter()
    typeW_examples = []
    typeW_degseqs = Counter()
    per_n = []

    for n in range(2, n_max + 1):
        n_genuine = n_L = n_W = 0
        for T0 in nx.nonisomorphic_trees(n):
            G = nx.convert_node_labels_to_integers(T0)
            mdG = min_defect(G)
            if mdG == 0:
                continue  # backbone under some rooting -> discharged by reroot (not genuine)
            genuine += 1
            n_genuine += 1
            aG = aobj_graph(G)

            witness = None
            for H, u, (v, w) in flp_moves(G):
                mdH = min_defect(H)
                if mdH >= mdG:
                    continue
                aH = aobj_graph(H)
                if aH < aG:
                    aobj_violation += 1
                    continue
                # cert oracle at u: rest = u's non-leaf-pair children in G, as rooted tuples
                rest = []
                nbrs = list(G.neighbors(u))
                leaves = [x for x in nbrs if G.degree(x) == 1]
                keep_leaf = leaves[0]
                dropped_leaf = leaves[1]
                for c in nbrs:
                    if c in (keep_leaf, dropped_leaf):
                        continue
                    rest.append(rooted_tuple(G, c, u))
                cert = cert_increment(rest)
                if not cert["match"]:
                    cert_mismatch += 1
                witness = (H, mdH, aH, u, cert)
                break

            if witness is not None:
                type_L += 1
                n_L += 1
                _, mdH, _, _, _ = witness
                drop_hist[mdG - mdH] += 1
            else:
                type_W += 1
                n_W += 1
                info = characterize_typeW(G)
                typeW_degseqs[info["degseq"]] += 1
                if len(typeW_examples) < 25:
                    typeW_examples.append({
                        "n": n,
                        "edges": sorted(tuple(sorted(e)) for e in G.edges()),
                        "min_defect": mdG,
                        **info,
                    })
        per_n.append((n, n_genuine, n_L, n_W))
        print(f"[n={n:2d}] genuine defective={n_genuine:4d}  Type-L={n_L:4d}  Type-W={n_W:4d}")

    print("\n" + "=" * 72)
    print("B0 FLP-MOVE COVERAGE SWEEP  (RealObligationA, leaf-path-extension)")
    print("=" * 72)
    print(f"n range: 2..{n_max}")
    print(f"genuine defective trees (min strDefect over roots > 0): {genuine}")
    covL = Fr(type_L, genuine) if genuine else Fr(0)
    print(f"  Type-L (FLP move lowers defect, Aobj non-decreasing): {type_L}"
          f"  ({float(covL)*100:.2f}%)")
    print(f"  Type-W (needs whole-hub relocation)                 : {type_W}"
          f"  ({float(1-covL)*100:.2f}%)")
    print(f"  strDefect-drop histogram on Type-L witnesses        : {dict(sorted(drop_hist.items()))}")
    print(f"\n  Aobj-DECREASE violations on FLP witnesses (must be 0): {aobj_violation}")
    print(f"  cert closed-form != direct increment (must be 0)    : {cert_mismatch}")
    if typeW_degseqs:
        print("\n  Type-W residual degree-sequence histogram (top 12):")
        for ds, c in typeW_degseqs.most_common(12):
            print(f"    {c:3d} x  degseq={ds}")
        print("\n  Type-W witness examples (first appearances):")
        for ex in typeW_examples[:12]:
            print(f"    n={ex['n']} minDefect={ex['min_defect']} degseq={ex['degseq']} "
                  f"symHubs={ex['symmetric_adjacent_hubs']} edges={ex['edges']}")

    verdict = "GO" if aobj_violation == 0 and cert_mismatch == 0 else "STOP"
    print(f"\n*** VERDICT: {verdict} ***")
    if verdict == "GO":
        print("    Every FLP witness raises (or ties) Aobj; every closed-form increment matches the")
        print("    direct cavity computation.  The Type-L local move is sound; Type-W is the residual.")
    else:
        print("    A soundness invariant FAILED -- do NOT proceed to Lean until reconciled.")
    return {"genuine": genuine, "type_L": type_L, "type_W": type_W,
            "aobj_violation": aobj_violation, "cert_mismatch": cert_mismatch,
            "typeW_degseqs": typeW_degseqs}


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    analyze(n_max=nmax)
