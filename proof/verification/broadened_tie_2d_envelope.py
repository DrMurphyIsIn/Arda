"""M3 SINGLE-HUB 2-D ENVELOPE de-risk: the broadened tie is the max over ALL balanced single hubs.

CONTEXT.  A balanced single hub is `a` load-5 arms + `b` load-4 arms + `c` cherries, size 11a+9b+2c.
At aligned size 11K the size-preserving moves are: the CHERRY TRADE (1 load-5 -> 1 load-4 + 1 cherry;
the proven tie edge, m = c) and the BULK SWAP (9 load-5 -> 11 load-4; `hub_bulk_le`).  Parametrize the
whole balanced family at size 11K as
    (a, b, c) = (K - c - 9t, c + 11t, c),   c in {0..5}, t >= 0
so the tie/trade edge is t = 0 and `t` walks the bulk-swap column at fixed cherry count c.  M3 must show
    max over (c, t) of Aobj(a,b,c)  <=  Aobj(tieState K mstar)   (the proven m-argmax, t=0 edge).

`hub_bulk_le` (R47TieBroadened.lean:66) already gives the t-step iff:
    Aobj(t+1) <= Aobj(t)  <->  F * hubQ(a-9, b+11, c) <= hubQ(a, b, c),   F = (513/80)^11 / (621/64)^9,
    hubQ(a,b,c) = 1 + (3a/23 + 3b/19 + c/3)/(a+b+c).
Define `bulkStop(K,c,t)` = that inequality's cleared numerator >= 0 (t-analog of `tradeStop`).  This
script:
  (1) confirms the GLOBAL (c,t) max sits on the t=0 edge at (mstar,0) for K in 5..40;
  (2) confirms each c-branch is t-unimodal, records t*(c) (least t with bulkStop);
  (3) DERIVES the exact `bulkStop` numerator quadratic in (K,c,t) [emitted for the Lean nlinarith] and
      confirms its upward-persistence in t (once bulk stops helping it never re-helps -- the
      `tradeStop_persists` analog);
  (4) confirms `t*(c)=0 for all c  <->  K >= 22` (contiguous), ENUMERATES the finite interior peaks
      (K,c,t>=1) for 5<=K<22 as the Lean patch list, and confirms NO branch peaks at t>=2 in-window;
  (5) confirms F = (513/80)^11/(621/64)^9.

Self-verifying: run() -- every claim an exact-Fraction / sympy assert.  conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

V5 = Fr(621, 64)   # Ztot_armU_five  (load-5 arm)
V4 = Fr(513, 80)   # Ztot_armU_four  (load-4 arm)
CH = Fr(3, 2)      # cherry factor
F_BULK = V4 ** 11 / V5 ** 9


def hubQ(a: int, b: int, c: int) -> Fr:
    d = a + b + c
    return 1 + (Fr(3 * a, 23) + Fr(3 * b, 19) + Fr(c, 3)) / d


def Aobj(a: int, b: int, c: int) -> Fr:
    """The exact Lean hub value hub_Aobj_eq(a,b,c)."""
    return V5 ** a * V4 ** b * CH ** c * hubQ(a, b, c)


def config(K: int, c: int, t: int):
    """(a,b,c) at size 11K on the cherry-c bulk column; None if a<0."""
    a = K - c - 9 * t
    b = c + 11 * t
    if a < 0:
        return None
    return (a, b, c)


def m_of(K: int) -> int:
    """The proven tie-edge argmax mstar (crossover of the cherry trade), from broadened_tie_family."""
    best_m, best_v = 0, None
    for m in range(0, K + 1):
        cfg = config(K, m, 0)  # tie edge: (K-m, m, m)
        if cfg is None:
            continue
        v = Aobj(*cfg)
        if best_v is None or v > best_v:
            best_v, best_m = v, m
    return best_m


# ------------------------------------------------------ (1)+(2) global max on t=0 edge, unimodality
def verify_edge_is_global(Kmax: int = 40) -> dict:
    tstars = {}
    for K in range(5, Kmax + 1):
        mstar = m_of(K)
        edge_val = Aobj(*config(K, mstar, 0))
        # global max over all (c,t)
        for c in range(0, 6):
            col = []
            t = 0
            while True:
                cfg = config(K, c, t)
                if cfg is None:
                    break
                col.append(Aobj(*cfg))
                t += 1
            assert col, (K, c)
            # every config dominated by the tie edge
            for t, v in enumerate(col):
                assert v <= edge_val, ("edge not global", K, c, t, float(v / edge_val))
            # t-unimodality: strictly up to argmax then strictly down
            ts = col.index(max(col))
            for i in range(1, len(col)):
                if i <= ts:
                    assert col[i] > col[i - 1] or ts == 0, ("not up", K, c, i)
                else:
                    assert col[i] < col[i - 1], ("not down", K, c, i)
            tstars[(K, c)] = ts
    return {"edge_is_global_max": True, "K_range": f"5..{Kmax}", "tstars": tstars}


# ------------------------------------------------------------- (3) bulkStop quadratic + persistence
def bulkStop_poly():
    """DERIVE the exact bulkStop numerator: hubQ(a,b,c) - F*hubQ(a-9,b+11,c) >= 0, cleared to an
    integer poly in (K,c,t) via a=K-c-9t, b=c+11t.  Returns sympy Poly (num) and the positive
    denominator scale."""
    K, c, t = sp.symbols("K c t", nonnegative=True)
    a = K - c - 9 * t
    b = c + 11 * t
    F = sp.Rational(513, 80) ** 11 / sp.Rational(621, 64) ** 9

    def Q(aa, bb, cc):
        d = aa + bb + cc
        return 1 + (sp.Rational(3, 23) * aa + sp.Rational(3, 19) * bb + sp.Rational(1, 3) * cc) / d

    expr = Q(a, b, c) - F * Q(a - 9, b + 11, c)     # >= 0  <=>  Aobj(t+1) <= Aobj(t)
    num, den = sp.fraction(sp.together(expr))
    pnum = sp.Poly(sp.expand(num), K, c, t)
    pden = sp.Poly(sp.expand(den), K, c, t)
    return pnum, pden, (K, c, t)


def bulkStop_num_value(pnum, syms, K: int, c: int, t: int) -> Fr:
    Ks, cs, ts = syms
    val = pnum.eval({Ks: K, cs: c, ts: t})
    return Fr(int(sp.numer(val)), int(sp.denom(val)))


def verify_bulkStop(Kmax: int = 40) -> dict:
    pnum, pden, syms = bulkStop_poly()
    # denominators d*(d+? ) are positive; confirm pden all-positive-coeff (so sign is pnum's sign)
    assert all(coef > 0 for coef in pden.coeffs()) or all(coef < 0 for coef in pden.coeffs())
    dsg = 1 if pden.LC() > 0 else -1
    Ks, cs, ts = syms
    # bulkStop(K,c,t) := dsg*pnum >= 0 must agree with Aobj(t+1) <= Aobj(t), and PERSIST upward in t
    for K in range(5, Kmax + 1):
        for c in range(0, 6):
            prev_stop = False
            t = 0
            while True:
                cfg, nxt = config(K, c, t), config(K, c, t + 1)
                if cfg is None or nxt is None:
                    break
                stop = dsg * bulkStop_num_value(pnum, syms, K, c, t) >= 0
                # semantics: stop  <=>  Aobj(t+1) <= Aobj(t)
                assert stop == (Aobj(*nxt) <= Aobj(*cfg)), ("bulkStop mismatch", K, c, t)
                # persistence: once stopped, stays stopped
                if prev_stop:
                    assert stop, ("bulkStop not persistent", K, c, t)
                prev_stop = stop
                t += 1
    # emit the poly (with dsg applied) as {(i,j,k): coeff} for the Lean statement
    emit = {}
    for mono, coef in zip(pnum.monoms(), pnum.coeffs()):
        emit[mono] = int(coef * dsg)
    return {"bulkStop_persistent": True, "dsg": dsg, "pden_const": str(pden.eval({Ks: 0, cs: 0, ts: 0})),
            "poly_Kct": emit}


# --------------------------------------------------- (4) threshold + interior-peak patch enumeration
def verify_threshold_and_patch(Kmax: int = 40) -> dict:
    interior = []       # (K,c,t) with t>=1 that is a branch argmax (the finite Lean patch)
    threshold = None
    for K in range(5, Kmax + 1):
        all_zero = True
        for c in range(0, 6):
            col = []
            t = 0
            while config(K, c, t) is not None:
                col.append(Aobj(*config(K, c, t)))
                t += 1
            ts = col.index(max(col))
            assert ts <= 1, ("t* >= 2 in window", K, c, ts)   # patch stays single-t
            if ts >= 1:
                all_zero = False
                interior.append((K, c, ts))
        if all_zero and threshold is None:
            threshold = K
        if not all_zero:
            threshold = None  # reset: require CONTIGUOUS all-zero tail
    # contiguity: every K >= threshold has all t*=0
    for K in range(threshold, Kmax + 1):
        for c in range(0, 6):
            col = []
            t = 0
            while config(K, c, t) is not None:
                col.append(Aobj(*config(K, c, t)))
                t += 1
            assert col.index(max(col)) == 0, ("t* != 0 past threshold", K, c)
    return {"threshold_K": threshold, "interior_peaks": interior, "no_t_ge_2": True,
            "patch_size": len(interior)}


def run() -> dict:
    out = {}
    assert F_BULK == Fr(86959512306484890624, 87946907297998046875), F_BULK
    out["F_bulk"] = str(F_BULK)
    out["edge_global"] = {k: v for k, v in verify_edge_is_global().items() if k != "tstars"}
    out["bulkStop"] = {k: v for k, v in verify_bulkStop().items() if k != "poly_Kct"}
    bs = verify_bulkStop()
    out["bulkStop_poly_Kct"] = bs["poly_Kct"]
    out["threshold_patch"] = verify_threshold_and_patch()
    out["status"] = {
        "M3_shape": "edge (t=0) is the global (c,t) max for all K>=5; K>=22 => every t*=0 (clean, "
                    "tie_maximal_over_trades closes it); 5<=K<22 => finite interior-peak patch below.",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run()
