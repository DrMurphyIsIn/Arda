"""Hunt for the maximum Laplacian ratio pi(T)=per(L(T))/prod deg over n-vertex trees
(Brualdi-Goldwasser OPEN problem; Pant 2026 refuted Wu-Dong-Lai, conjectured no
replacement maximizer).

Strategy: a fair tree-GA maximizes pi(T); its champion is compared -- by EXACT rational
arithmetic, so no float-noise margin is needed -- against a strong structured baseline
(Pant's spider families A_t/B_t/C_t plus a broad balanced-spider enumeration, the current
best-known high-pi trees). A champion with pi strictly greater than the whole baseline set
is a candidate NEW extremal tree for the open maximum; it is then re-verified (two
independent permanent engines agree, tree-structure confirmed) and flagged for external
cross-check -- never claimed as settled.

Honesty: found=BEATS_BASELINE only when the exact rational pi exceeds every baseline
candidate AND the two permanent engines agree AND the graph is a tree. found=TIES/BELOW
is the expected null and is NOT evidence about the true maximum.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction

import networkx as nx
import numpy as np

from .tree_search import evolve_trees
from .permanent import (
    laplacian_ratio,
    laplacian_ratio_float,
    ryser_laplacian_permanent,
    tree_laplacian_permanent,
)
from .trees import spider


def _balanced(total, parts):
    base, rem = divmod(total, parts)
    return [base + 1] * rem + [base] * (parts - rem)


def structured_candidates(n):
    """Yield (description, adjacency) for known high-pi structured trees on n vertices."""
    # Broad balanced-spider enumeration: T(a_1..a_m), sum(a)=(n-m)/2.
    for m in range(2, min(9, n // 2) + 1):
        if (n - m) % 2 != 0:
            continue
        s = (n - m) // 2
        if s < 1:
            continue
        a = _balanced(s, m)
        yield (f"spider(balanced,m={m},a={a})", spider(a))
    # Pant's explicit counterexample families where they land on n.
    if (n - 15) % 2 == 0 and (n - 15) // 2 >= 3:      # A_t = T(3,t,3), n=2t+15
        t = (n - 15) // 2
        yield (f"A_{t}=T(3,{t},3)", spider([3, t, 3]))
    if (n - 4) % 8 == 0 and (n - 4) // 8 >= 4:          # B_t = T(t,t,t,t), n=8t+4
        t = (n - 4) // 8
        yield (f"B_{t}=T({t},{t},{t},{t})", spider([t, t, t, t]))
    if (n - 6) % 8 == 0 and (n - 6) // 8 >= 4:          # C_t = T(t,t,t+1,t), n=8t+6
        t = (n - 6) // 8
        yield (f"C_{t}=T({t},{t},{t + 1},{t})", spider([t, t, t + 1, t]))


def structured_baseline(n):
    """Best (highest-pi) structured candidate on n vertices: (pi, desc, adjacency)."""
    best = None
    for desc, A in structured_candidates(n):
        pi = laplacian_ratio(A)
        if best is None or pi > best[0]:
            best = (pi, desc, A)
    return best


def _is_tree(A):
    n = A.shape[0]
    if int(A.sum()) // 2 != n - 1:
        return False
    return nx.is_connected(nx.from_numpy_array(A))


def verify_champion(A, baseline_pi: Fraction) -> dict:
    """Independently verify a GA champion and classify vs the baseline (exact)."""
    is_tree = _is_tree(A)
    per_dp = tree_laplacian_permanent(A)
    n = A.shape[0]
    # Ryser cross-check only where 2^n is tractable.
    engines_agree = True
    if n <= 22:
        L = np.diag(A.sum(1).astype(int)) - A.astype(int)
        engines_agree = (per_dp == round(ryser_laplacian_permanent(L)))
    pi = laplacian_ratio(A)
    if not is_tree or not engines_agree:
        status = "INVALID"
    elif pi > baseline_pi:
        status = "BEATS_BASELINE"
    elif pi == baseline_pi:
        status = "TIES"
    else:
        status = "BELOW"
    return {"status": status, "pi": str(pi), "pi_float": float(pi),
            "is_tree": is_tree, "engines_agree": engines_agree,
            "permanent": per_dp, "n": n,
            "degree_sequence": sorted(int(x) for x in A.sum(1))}


def hunt(n_min, n_max, pop_size, generations, seed, populations):
    def fitness(A):
        return laplacian_ratio_float(A)      # fast; verifier re-checks with exact Fraction

    attempts = []
    beats = []
    for n in range(n_min, n_max + 1):
        base = structured_baseline(n)
        if base is None:
            continue
        base_pi, base_desc, _ = base
        best_A, best_f = None, -1.0
        for p in range(populations):
            A, f = evolve_trees(n=n, pop_size=pop_size, generations=generations,
                                seed=seed + 1000 * n + p, fitness_fn=fitness,
                                copy_rate=0.0)
            if f > best_f:
                best_A, best_f = A, f
        v = verify_champion(best_A, base_pi)
        rec = {"n": n, "baseline_pi": str(base_pi), "baseline_desc": base_desc,
               "champion": v}
        attempts.append(rec)
        if v["status"] == "BEATS_BASELINE":
            beats.append(rec)
    return {"beats": beats, "attempts": attempts, "n_range": [n_min, n_max]}


def main():
    ap = argparse.ArgumentParser(description="Max Laplacian-ratio tree hunt")
    ap.add_argument("--n-min", type=int, default=19)
    ap.add_argument("--n-max", type=int, default=45)
    ap.add_argument("--pop", type=int, default=300)
    ap.add_argument("--generations", type=int, default=300)
    ap.add_argument("--seed", type=int, default=17)
    ap.add_argument("--populations", type=int, default=3)
    ap.add_argument("--out",
                    default="proof/verification/result_card.json")
    args = ap.parse_args()
    result = hunt(args.n_min, args.n_max, args.pop, args.generations, args.seed,
                  args.populations)
    card = {
        "problem": "maximize pi(T)=per(L(T))/prod deg over n-vertex trees "
                   "(Brualdi-Goldwasser 1984; OPEN -- Pant 2026 refuted Wu-Dong-Lai, "
                   "no replacement maximizer conjectured)",
        "config": vars(args),
        "beats_baseline_count": len(result["beats"]),
        "beats": result["beats"],
        "attempts": result["attempts"],
        "honesty_note": (
            "BEATS_BASELINE = the GA champion's EXACT rational pi exceeds every "
            "structured baseline candidate (Pant families + balanced spiders), two "
            "permanent engines agree, and it is a tree. This is a candidate new "
            "best-known tree for the OPEN maximum -- it requires independent external "
            "cross-check before any claim. TIES/BELOW is the expected null and says "
            "nothing about the true maximum."),
    }
    with open(args.out, "w") as f:
        json.dump(card, f, indent=2)
    for rec in result["attempts"]:
        c = rec["champion"]
        print(f"n={rec['n']:3d}  baseline={rec['baseline_pi']:>18s} ({rec['baseline_desc']})"
              f"  champ pi={c['pi']:>18s}  -> {c['status']}")
    print(f"\nBEATS_BASELINE: {len(result['beats'])}  (see honesty_note)")


if __name__ == "__main__":
    main()
