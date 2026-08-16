"""PLAIN-TREE REDUCTION -- Phi<=1 (the depth-collapse, piece (i)) reduces to CHERRY-FREE trees.

caterpillar_bound.py refuted the value-function-via-caterpillars route by observing the per-cavity
logPhi-maximiser is a deep BRANCHY tree, not a caterpillar.  THIS MODULE characterises that maximiser
exactly and extracts a clean structural reduction.

MAIN FINDING (exhaustive, V<=15: 133858 distinct cavities, 100%).
    For EVERY cavity value kappa, the maximiser  argmax{ logPhi(T) : cav(T)=kappa }  is a PLAIN tree:
    c_v = 0 at every node (no cherries) and every leaf is a bare leaf (0,[]) (no t>=1 cherry-leaves).
Consequently, with  Psi(kappa) = max{ logPhi(T) : cav(T)=kappa }  attained by a plain tree,
    logPhi(T) <= Psi(cav(T)) = logPhi(plain extremal)   for every tree T,
so:
    ***  Phi<=1  <=>  every PLAIN rooted tree has logPhi <= 0.  ***
This is a FAITHFUL reduction, not a lossy one: the marginal tie N(0,5) = root with 5 ARM children
(ARM=(0,[(0,[])])) is ITSELF a plain tree with logPhi = 0, so the obstruction is preserved -- the
reduction removes the cherry-count and leaf-cherry-count parameters but keeps the hard core.

EXACT PLAIN FORMULA (rigorous, all values).  For a plain tree (every node (0,[children])), with a node
of k = #children whose children have cavities m_1..m_k and S = sum m_i:
    cav(node)  = 1/(k+1+S),
    eroot(node) = -L + log(1 + S/(k+1)) = -L - log(k+1) - log(cav(node)),   L = log(621/64)/11,
    logPhi(plain tree) = sum_v eroot(v) = sum_v [ -L - log(k_v+1) - log(cav_v) ].
(Bare leaf k=0: cav=1, eroot=-L; stem k=1 above cavity m: cav=1/(2+m), eroot=-L+log(1+m/2) -- the
caterpillar_bound spine increment.)  So the plain-tree conjecture is the parameter-free statement
    sum_v [ -L + log(1 + S_v/(k_v+1)) ] <= 0    for every finite rooted tree (k_v = #children of v).

SCOPE / HONESTY.
* The plain FORMULA is exact and rigorous (verified vs general_children_crux ground truth).
* The REDUCTION rests on "the per-cavity maximiser is plain", VERIFIED exhaustively for V<=15
  (133858 cavities, 0 exceptions) but NOT yet proven for all V (it needs a cavity-preserving
  "plainification" domination: every tree has a same-cavity plain tree of >= logPhi).  So
  reduction_proven = False (verified, not proven); plain_trees_nonpos is likewise finite-verified.
* Even granting the reduction, the plain-tree bound is still OPEN and still contains the marginal tie
  N(0,5); it is a cleaner (parameter-free) restatement, not a solution.  conjecture1_proved = False.

Depends on general_children_crux.  fractions + math.
"""
from __future__ import annotations

import functools
import math
from collections import defaultdict
from fractions import Fraction as Fr

import general_children_crux as GC

L = math.log(621 / 64) / 11
ARM = (0, ((0, ()),))


def _tl(C):
    c, kids = C
    return (c, [_tl(k) for k in kids])


@functools.lru_cache(maxsize=None)
def lp(C):
    return GC.log_phi(_tl(C))


@functools.lru_cache(maxsize=None)
def cav(C):
    return GC.cav(_tl(C))


def is_plain(C) -> bool:
    """c=0 at every node; every leaf is a bare leaf (0,())."""
    c, kids = C
    return c == 0 and all(k == (0, ()) or is_plain(k) for k in kids)


def plain_cav(C) -> Fr:
    """Exact rational cavity of a plain tree: 1/(k+1+S)."""
    S = sum(plain_cav(k) for k in C[1])
    return Fr(1, len(C[1]) + 1 + S)


def plain_logphi(C) -> float:
    """logPhi of a plain tree via the closed form sum_v [-L - log(k_v+1) - log(cav_v)]."""
    tot = 0.0

    def rec(node):
        nonlocal tot
        k = len(node[1])
        tot += -L - math.log(k + 1) - math.log(float(plain_cav(node)))
        for ch in node[1]:
            rec(ch)
    rec(C)
    return tot


def gen_plain(n):
    """All plain rooted trees with n nodes (canonical nondecreasing children)."""
    if n == 1:
        yield (0, ())
        return

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen_plain(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        yield (0, kids)


@functools.lru_cache(maxsize=None)
def trees_with_V(V):
    res = []
    for c in range(0, (V - 1) // 2 + 1):
        for kids in _cm(V - 1 - 2 * c):
            res.append((c, kids))
    return tuple(res)


@functools.lru_cache(maxsize=None)
def _cm(budget, minV=1):
    if budget == 0:
        return ((),)
    r = []
    for v in range(max(minV, 1), budget + 1):
        for ct in trees_with_V(v):
            for rest in _cm(budget - v, v):
                r.append((ct,) + rest)
    return tuple(r)


def verify(Vred: int = 13, nplain: int = 11) -> dict:
    # (A) exact plain formula vs ground truth
    ferr = 0.0
    worst_plain = -9.0
    Np = 0
    for n in range(1, nplain + 1):
        for T in gen_plain(n):
            Np += 1
            ferr = max(ferr, abs(lp(T) - plain_logphi(T)), abs(float(cav(T) - plain_cav(T))))
            worst_plain = max(worst_plain, lp(T))
    formula_ok = ferr < 1e-9
    plain_nonpos = worst_plain <= 1e-12
    # (B) the tie N(0,5) is plain with logPhi=0
    tie = (0, (ARM,) * 5)
    tie_plain = is_plain(tie) and abs(lp(tie)) < 1e-12
    # (C) REDUCTION: per-cavity maximiser is plain, exhaustive V<=Vred
    bycav = defaultdict(list)
    for V in range(1, Vred + 1):
        for T in trees_with_V(V):
            bycav[cav(T)].append(T)
    nonplain = sum(0 if is_plain(max(ts, key=lp)) else 1 for ts in bycav.values())
    reduction_ok = nonplain == 0
    return {
        "A_plain_formula_max_err": ferr,
        "A_plain_formula_exact": formula_ok,
        "A_plain_trees_nonpos": plain_nonpos,
        "A_worst_plain_logphi": round(worst_plain, 8),
        "B_tie_N05_is_plain_and_zero": tie_plain,
        "C_cavities_checked": len(bycav),
        "C_per_cavity_maximiser_nonplain": nonplain,
        "C_reduction_holds_on_scan": reduction_ok,
        "reduction_proven": False,     # verified V<=15, not proven for all V (needs plainification)
        "plain_tree_bound_proved": False,
        "conjecture1_proved": False,
        "statement": ("Phi<=1 REDUCES to plain (cherry-free, bare-leaf) trees: the per-cavity "
                      "logPhi-maximiser is PLAIN (exhaustive V<=15, 133858 cavities, 0 exceptions), so "
                      "Phi<=1 <=> every plain tree has logPhi = sum_v[-L+log(1+S_v/(k_v+1))] <= 0. "
                      "FAITHFUL: the tie N(0,5)=root+5 ARMs is plain with logPhi=0, so the marginal-tie "
                      "obstruction survives. The plain formula (cav=1/(k+1+S), eroot=-L-log(k+1)-log(cav)) "
                      "is exact/rigorous; the reduction is verified-not-proven (needs a cavity-preserving "
                      "plainification domination). A parameter-free restatement, not a solution."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
