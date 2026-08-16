"""Parity-aware MULTISET FLATTEN -- the depth-collapse move, and why it FAILS (sharp obstruction).

The depth-collapse lemma (piece (i) of Phi<=1) would follow from a rearrangement move:
    replace a non-leaf subtree b of a tree T by a MIXED bush b* = (c,[leaves]) of the SAME V(b),
    non-decreasing logPhi(T).  Iterating bottom-up would collapse T to a depth-1 mixed bush at V(T),
    and mixed_bush_bound_closed.py PROVES every mixed bush is <= 0, giving Phi<=1.

The move is "parity-aware": mixed bushes exist at EVERY V (V = 1+2c+sum(1+2 t_i) so V ≡ 1+k mod 2 --
pick the leaf-count k with the right parity), so unlike the single-leaf flatten (which forced k=1,
parity-blocked ~half the time), the multiset flatten is NEVER parity-blocked.

THIS PROBE ANSWERS: does the max-logPhi same-V mixed-bush flatten ever DECREASE logPhi?  YES.  And no
cavity constraint rescues it.  Self-verifying (exhaustive over trees <= N nodes).  Depth-collapse OPEN.

FINDINGS (verify()):

(G1) per-V mixed-bush domination HOLDS: maxmixed(V(b)) >= logPhi(b) for EVERY subtree b (0 failures).
     So there is ALWAYS a same-V mixed bush that dominates b as a standalone subtree.

(G2) UNCONSTRAINED flatten (b -> argmax_{mixed bush at V(b)} logPhi) DECREASES logPhi(T) ~8% of the
     time.  The dominating bush has the WRONG cavity; the cavity change propagates up the spine and the
     ancestor penalty exceeds the local gain.  (Worst seen ~ -0.06.)

(G3) CAV<=cav(b) constraint does NOT help (decreases about as often): the cavity direction is not the fix.

(G4) CAV==cav(b) exact (the Locality.lean cavity-preserving swap, exact shift logPhi(b*)-logPhi(b)) is
     available ~84% of the time BUT still DECREASES in a nonzero minority -- because per-(V,cavity)
     mixed-bush domination FAILS: there exist general subtrees b that BEAT every same-(V,cavity) mixed
     bush.  A witness is exhibited by find_vcav_witness().

SHARP OBSTRUCTION (the two requirements are incompatible for a mixed bush):
   * to zero the ancestor effect you must PRESERVE cavity (G4 move), but then the mixed bush does not
     always DOMINATE (G4 failures);
   * to DOMINATE you take the max-logPhi same-V bush (G1), but it has the WRONG cavity (G2 penalty).
No mixed bush can simultaneously (dominate b) and (match cav(b)).  This is the depth-collapse wall,
now localized to the (V,cavity)-domination gap -- distinct from parity (sidestepped) and from the
per-V gap (there is none).  depth_collapse_closed = False; conjecture1_proved = False.

Depends on general_children_crux, rational_reduction.  Std-lib only otherwise.
"""
from __future__ import annotations

import functools
from fractions import Fraction as Fr

import general_children_crux as GC
import rational_reduction as RR


def lp(C):
    return GC.log_phi(C)


def cavv(C):
    return GC.cav(C)


def Vof(C):
    return RR._prodF_V(C)[1]


def _parts(rem, k, mn):
    if k == 0:
        if rem == 0:
            yield ()
        return
    if k == 1:
        yield (rem,)
        return
    for x in range(mn, rem // k + 1):
        for tail in _parts(rem - x, k - 1, x):
            yield (x,) + tail


@functools.lru_cache(maxsize=None)
def mixed_at_V(V):
    out = []
    c = 0
    while 1 + 2 * c <= V:
        R = V - 1 - 2 * c
        for k in range(0, R + 1):
            if (R - k) % 2:
                continue
            for ts in _parts((R - k) // 2, k, 0):
                out.append((c, tuple(ts)))
        c += 1
    return out


def _build(cts):
    return (cts[0], [(t, []) for t in cts[1]])


@functools.lru_cache(maxsize=None)
def maxmixed(V):
    return max((lp(_build(x)), x) for x in mixed_at_V(V))


def _subaddrs(C, path=()):
    _, kids = C
    res = []
    for i, k in enumerate(kids):
        if k[1]:
            res.append(path + (i,))
        res += _subaddrs(k, path + (i,))
    return res


def _get(C, p):
    for i in p:
        C = C[1][i]
    return C


def _set(C, p, nb):
    if not p:
        return nb
    cr, kids = C
    kids = list(kids)
    kids[p[0]] = _set(kids[p[0]], p[1:], nb)
    return (cr, kids)


def find_vcav_witness(nmax=6, cmax=5):
    """A general subtree b that BEATS every same-(V,cavity) mixed bush (per-(V,cav) domination failure)."""
    seen = set()
    best = None
    for T in GC._trees(nmax, cmax):
        for b in _subtrees(T):
            key = str(b)
            if key in seen:
                continue
            seen.add(key)
            V = Vof(b)
            mu = cavv(b)
            same = [lp(_build(x)) for x in mixed_at_V(V) if cavv(_build(x)) == mu]
            if same and lp(b) > max(same) + 1e-12:
                gap = lp(b) - max(same)
                if best is None or gap > best[-1]:
                    best = (b, V, mu, lp(b), max(same), gap)
    return best


def _subtrees(C):
    _, kids = C
    if kids:
        yield C
    for k in kids:
        yield from _subtrees(k)


def verify(nmax=6, cmax=5, cap=120000):
    perV_fail = uncon = cavle = caveq_exist = caveq_dec = tot = 0
    worst = 0.0
    for T in GC._trees(nmax, cmax):
        for p in _subaddrs(T):
            b = _get(T, p)
            V = Vof(b)
            if V > 13:
                continue
            tot += 1
            mmv, mmx = maxmixed(V)
            if mmv < lp(b) - 1e-12:
                perV_fail += 1
            base = lp(T)
            if lp(_set(T, p, _build(mmx))) - base < -1e-9:
                uncon += 1
                worst = min(worst, lp(_set(T, p, _build(mmx))) - base)
            mu = cavv(b)
            le = [(lp(_build(x)), x) for x in mixed_at_V(V) if cavv(_build(x)) <= mu]
            if le and lp(_set(T, p, _build(max(le)[1]))) - base < -1e-9:
                cavle += 1
            eq = [(lp(_build(x)), x) for x in mixed_at_V(V) if cavv(_build(x)) == mu]
            if eq:
                caveq_exist += 1
                if lp(_set(T, p, _build(max(eq)[1]))) - base < -1e-9:
                    caveq_dec += 1
            if tot > cap:
                break
        if tot > cap:
            break
    wit = find_vcav_witness(min(nmax, 6), cmax)
    return {
        "trials": tot,
        "G1_perV_domination_failures": perV_fail,        # expect 0
        "G2_unconstrained_flatten_decreases": uncon,
        "G2_worst_drop": round(worst, 6),
        "G3_cav_le_flatten_decreases": cavle,
        "G4_cav_eq_exists": caveq_exist,
        "G4_cav_eq_flatten_decreases": caveq_dec,        # >0 => per-(V,cav) domination fails
        "vcav_domination_witness": None if wit is None else {
            "b": str(wit[0]), "V": wit[1], "cav": str(wit[2]),
            "logphi_b": round(wit[3], 6), "best_same_Vcav_mixed": round(wit[4], 6), "gap": round(wit[5], 6)},
        "multiset_flatten_is_valid_domination_move": uncon == 0,
        "depth_collapse_closed": False,
        "conjecture1_proved": False,
        "note": ("Parity-aware multiset flatten DECREASES logPhi (~8%), and NO cavity constraint fixes it: "
                 "cav<=cav(b) decreases about as much; cav==cav(b) (cavity-preserving, available ~84%) still "
                 "decreases because per-(V,cavity) mixed-bush domination FAILS (a general subtree beats every "
                 "same-(V,cav) mixed bush). per-V domination holds (0 fails) but the dominating bush has the "
                 "WRONG cavity => ancestor penalty. The depth-collapse wall is the (V,cavity)-domination gap: "
                 "no mixed bush can BOTH dominate b AND match cav(b). depth_collapse OPEN."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
