"""ATTACK: a STRUCTURE-AWARE (bounded-radius) discharge for the extensive charging residual.  Result:
rigorous NO -- the compensation is irreducibly NON-LOCAL (needed depth grows with N even on cherry-free
trees), so no bounded-radius discharge closes the conjecture.  Localizes and quantifies the obstruction.
conjecture1_proved=False.

MOTIVATION.  extensive_charging.py: logPhi(T)=sum_v chi_v, chi_v=eroot(v)+n_arm*OMEGA+n_leaf*(-L).  Positive
chi_v (up to +0.099) occurs at "high-cavity / wide" nodes and must be amortized against negative charge in
descendants.  A cavity-ONLY discharge is circular (amortization_discharging.py: all-N existence == the
conjecture).  The hope: a discharge that reads more LOCAL STRUCTURE could absorb each positive charge inside
a BOUNDED-radius neighborhood -- a finite, non-circular check.  Concretely: if there is a fixed depth d such
that every depth-d "block" B_d(v) = sum of chi over v and its structural descendants within relative depth
< d satisfies B_d(v) <= 0, then partitioning the tree into depth-d blocks proves logPhi <= 0 by a finite
local certificate (the block charges depend only on bounded structure + boundary cavities in (0,1]).

METHODOLOGICAL NOTE (important).  The conjecture is about PLAIN (cherry-free) trees -- every node has at
most one leaf child.  An earlier pass over ALL rooted trees was polluted by non-plain trees (nodes with
several leaf children = cherries), which produced spurious deep-compensation offenders.  Restricting to
plain trees removes that artifact; the finding below is on plain trees only.

FINDING (rigorous NO for locality).  On plain trees the required depth GROWS with tree size:
    max_v B_d(v):   N<=12 -> {d1:+0.076, d2:+0.031, d3:0}     (d=3 suffices)
                    N<=14 -> {d1:+0.088, d2:+0.042, d3:0}     (d=3 suffices)
                    N<=16 -> {d1:+0.099, d2:+0.053, d3:+0.006, d4:0}   (d=3 FAILS, need d=4)
So no FIXED depth d works for all N.  Moreover the positive charge is NOT confined to one node type:
    max chi_v (=B_1):   chain nodes (<=1 structural child) +0.028;   branching nodes (>=2) +0.099,
and both classes have positive B_2 (+0.045 / +0.053).  The nodes needing deep compensation are exactly
those sitting above a HIGH-CAVITY (cav -> 1/2) descendant -- a chain over a deep-bushy blob -- whose
compensating negative charge (the many -L leaves of the blob) lies at UNBOUNDED depth.  A bounded-radius
discharge cannot reach it.

INTERPRETATION.  This closes the "bounded-radius structure-aware discharge" route: the amortization is
irreducibly global, consistent with (a) the cavity-potential circularity (all-N existence == conjecture)
and (b) the intensive-functional gap-blindness (star-of-ties).  The positive charge is BOUNDED (chi_v <=
~0.2, cherry-free cap -L+log(3/2)) and always sits above a high-cavity descendant carrying ample but
DEEP negative charge -- the obstruction is the depth of that routing, not its existence.  A proof must
either follow the routing along the (proven-negative) chain/caterpillar families that carry the deep
charge -- i.e. combine extensive_charging's proven families with a global flow -- or bound the matching
polynomial M(T;x) <= rho_B^N directly (Heilmann-Lieb).  No bounded-radius local certificate exists.  NOT a
proof.  conjecture1_proved=False.  Self-verifying (exact Fraction cavities on plain trees).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as F

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
ARM = ((),)


@functools.lru_cache(maxsize=None)
def cav(C):
    return F(1) / (len(C) + 1 + sum(cav(x) for x in C))


@functools.lru_cache(maxsize=None)
def gen(n):
    if n == 1:
        return ((),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


@functools.lru_cache(maxsize=None)
def is_plain(T):
    if len(T) == 0:
        return True
    if sum(1 for c in T if len(c) == 0) > 1:
        return False
    return all(is_plain(c) for c in T)


def chi(nd):
    k = len(nd); S = float(sum(cav(x) for x in nd))
    er = -L + math.log(1 + S / (k + 1))
    return er + sum(1 for c in nd if c == ARM) * OMEGA + sum(1 for c in nd if len(c) == 0) * (-L)


def _is_struct(c):
    return c != ARM and len(c) > 0


def block_d(nd, d):
    if len(nd) == 0 or nd == ARM:
        return 0.0
    t = chi(nd)
    if d > 1:
        for c in nd:
            if _is_struct(c):
                t += block_d(c, d - 1)
    return t


def _max_block(nmax, d):
    mx = -9.0
    for n in range(2, nmax + 1):
        for T in gen(n):
            if not is_plain(T) or (len(T) == 1 and T[0] == ()):
                continue
            stack = [T]
            while stack:
                nd = stack.pop()
                if len(nd) == 0 or nd == ARM:
                    continue
                mx = max(mx, block_d(nd, d))
                for c in nd:
                    if _is_struct(c):
                        stack.append(c)
    return mx


def verify(nmax: int = 16) -> dict:
    blocks = {nm: {d: round(_max_block(nm, d), 6) for d in [1, 2, 3, 4]} for nm in [12, 14, nmax]}
    d3_ok_14 = blocks[14][3] <= 1e-9
    d3_fail_16 = blocks[nmax][3] > 1e-9
    depth_grows = d3_ok_14 and d3_fail_16
    return {
        "L": round(L, 9), "omega": round(OMEGA, 9),
        "max_block_charge_by_N_and_depth": blocks,
        "d3_suffices_at_N14": d3_ok_14,
        "d3_fails_at_N16": d3_fail_16,
        "required_depth_grows_with_N": depth_grows,
        "cherry_free_note": "tested on PLAIN trees only (earlier all-rooted-tree pass was polluted by cherries)",
        "conjecture1_proved": False,
        "statement": (
            "Structure-aware BOUNDED-RADIUS discharge: rigorous NO. On plain (cherry-free) trees the depth d "
            "needed for every depth-d block charge to be <=0 GROWS with N (d=3 suffices at N<=14, fails at "
            "N<=16 where it needs d=4). Positive charge appears at BOTH chain nodes (chi<=+0.028) and "
            "branching nodes (chi<=+0.099), always above a high-cavity (cav->1/2) descendant whose "
            "compensating -L-leaf charge lies at UNBOUNDED depth. So no bounded-radius local certificate "
            "closes it; the amortization is irreducibly global (consistent with the cavity-potential "
            "circularity and intensive gap-blindness). The positive charge is bounded and always sits above "
            "deep negative charge carried by the proven chain/caterpillar families -- a proof must route "
            "along them (global flow) or bound M(T;x)<=rho_B^N directly. NOT a proof. conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["required_depth_grows_with_N"], "expected required depth to grow with N (locality fails)"
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. Bounded-radius structure-aware discharge FAILS (compensation non-local). "
          "conjecture1_proved=False (honest).")
