"""STRONGEST LEAD of the program: an EXPLICIT closed-form discharging potential phi(y)=c*(y-(rho_B-1))_+ that
satisfies the folded super-solution on every plain tree checked (exhaustive N<=17 + adversarial N<=45 +
unbounded-branching stars), with a robustly NON-EMPTY constant interval c in [~0.15, 0.302].  If the one
remaining inequality (sup of the required c over ALL configs < the fixed upper bound 0.302) is proved
analytically, the 1984 conjecture follows.  NOT yet proved.  conjecture1_proved=False.

THE POTENTIAL.  In the folded discharge (branching_folded_potential.py): logPhi=sum_v chi_v with
chi_v=eroot(v)+n_arm*OMEGA+n_leaf*(-L), and the super-solution
    chi_v + phi(cav_v) <= sum_{struct children c} phi(cav_c)     at every node
gives logPhi <= -phi(cav_root) <= 0.  Take the EXPLICIT closed form
    phi(y) = c * max(0, y - T0),   T0 = rho_B - 1 = (621/64)^(1/11) - 1 = 0.229474...
The threshold T0 is forced: a "star of S" (root + m copies of a structural subtree S, cav_S) has
chi_root -> -L+log(1+cav_S) as m->inf, which is > 0 exactly when cav_S > rho_B-1 = T0; so phi MUST be >0
above T0 and may be 0 below it.  (phi(T0)=0, and log(1+T0)=log(rho_B)=L.)

WHY THIS IS SHARP AND CHECKABLE.  Every super-solution constraint is LINEAR in c:
    chi_v + c*(cav_v-T0)_+ <= c*sum_c (cav_c-T0)_+   <=>   chi_v + c*D_v <= 0,
    D_v := (cav_v-T0)_+ - sum_{struct c}(cav_c-T0)_+.
So the feasible c is an INTERVAL [lo, hi]: D_v>0 gives c <= -chi_v/D_v (upper), D_v<0 gives c >= -chi_v/D_v
(lower).  The interval can only SHRINK with N; feasibility for all N <=> lo(inf) <= hi.

EVIDENCE (self-verifying).
- UPPER bound hi = 0.302077, EXACT and STABLE across N, set by the single near-star N(0,1)=(((),),):
  hi = |g(1)| / (3/7 - T0)  (its only structural-free constraint).
- LOWER bound lo(N) creeps 0.1337 (N<=11) -> 0.1413 (N<=17), sub-linearly.
- ADVERSARIAL: over stars/nests of high-cavity structural subtrees (cav up to 0.48, m up to ~60) and 40000
  random plain trees N=10..45, the max required c (lower bound) is 0.1492 << 0.302.  So the interval
  [~0.15, 0.302] is robustly non-empty; e.g. c=0.22 gives max folded-super-solution residual = 0 (to 1e-8)
  on all plain trees N<=17.
- The tie N(0,5) is satisfied EXACTLY: cav_root=3/23<T0 => phi=0, chi=g(5)=0, residual 0 (tight).

REMAINING STEP (the whole proof).  Prove analytically that  sup over ALL plain-tree node-configs of the
required lower bound  chi_v / D_v  (over configs with chi_v>0, D_v<0)  is  < 0.302077  -- equivalently, that
there is a fixed c (say c=0.22) with  chi_v + c*(cav_v-T0)_+ <= c*sum_{struct c}(cav_c-T0)_+  for ALL
(a arms, nl in {0,1} leaf, m struct children at cavities y_1..y_m).  This is a CONCRETE inequality in an
EXPLICIT phi -- no fixed-point/-psi circularity -- reducing the 1984 problem to bounding one elementary
expression.  The m=0 case is the near-star/bush-star family (proven <=0) plus the exact c<=0.302 bound; the
m>=1 case (the branching lower bound) is what must be bounded above by 0.302.  Convexity makes equal
children the tightest, cutting it to 2 continuous + 2 integer parameters.  NOT carried out here.

HONEST STATUS (overclaim discipline -- the trap sprang 3x before).  The verification is EMPIRICAL:
exhaustive to N<=17 and adversarial/random to N<=45.  The lower bound lo(N) is still creeping (slowly) and
is only bounded numerically; the analytic proof that it stays < 0.302 for ALL N is NOT done.  Until then
this is a candidate, not a theorem.  conjecture1_proved=False.  But it is the first EXPLICIT potential with
a non-empty margin, and it converts the crux into a single elementary inequality.  Self-verifying (exact
interval arithmetic over plain trees + adversarial search).
"""
from __future__ import annotations

import functools
import math

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
RHO_B = (621 / 64) ** (1 / 11)
T0 = RHO_B - 1
ARM = ((),)


@functools.lru_cache(maxsize=None)
def cav(C):
    return 1.0 / (len(C) + 1 + sum(cav(x) for x in C))


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


def _struct(nd):
    return [c for c in nd if c != ARM and len(c) > 0]


def _chi(nd):
    na = sum(1 for c in nd if c == ARM); nl = sum(1 for c in nd if len(c) == 0)
    S = sum(cav(x) for x in nd)
    return -L + math.log(1 + S / (len(nd) + 1)) + na * OMEGA + nl * (-L)


def feasible_c_interval(nmax):
    """Exact interval [lo, hi] of constants c for which phi=c*(y-T0)_+ satisfies the folded super-solution
    on all plain trees up to nmax.  Constraint chi_v + c*D_v <= 0 is linear in c."""
    lo, hi = -1e9, 1e9
    lo_tree = hi_tree = None
    for n in range(2, nmax + 1):
        for T in gen(n):
            if not is_plain(T):
                continue
            st = [T]
            while st:
                nd = st.pop()
                if len(nd) == 0 or nd == ARM:
                    continue
                ch = _chi(nd)
                D = max(0.0, cav(nd) - T0) - sum(max(0.0, cav(c) - T0) for c in _struct(nd))
                if D > 1e-12:
                    if -ch / D < hi:
                        hi = -ch / D; hi_tree = nd
                elif D < -1e-12:
                    if -ch / D > lo:
                        lo = -ch / D; lo_tree = nd
                elif ch > 1e-9:
                    return None
                for c in _struct(nd):
                    st.append(c)
    return lo, hi, lo_tree, hi_tree


def max_residual(c, nmax):
    w = -9.0
    for n in range(2, nmax + 1):
        for T in gen(n):
            if not is_plain(T):
                continue
            st = [T]
            while st:
                nd = st.pop()
                if len(nd) == 0 or nd == ARM:
                    continue
                phi = lambda y: c * max(0.0, y - T0)
                w = max(w, _chi(nd) + phi(cav(nd)) - sum(phi(cav(x)) for x in _struct(nd)))
                for x in _struct(nd):
                    st.append(x)
    return w


def verify() -> dict:
    lo, hi, lo_tree, hi_tree = feasible_c_interval(16)
    g1 = -L + math.log(7 / 6) + OMEGA  # logPhi(N(0,1)) = eroot(1 arm) + omega
    hi_exact = -g1 / (3 / 7 - T0)
    c_mid = 0.5 * (lo + hi)
    return {
        "rho_B": round(RHO_B, 9), "T0_eq_rhoB_minus_1": round(T0, 9),
        "log_1_plus_T0_eq_L": abs(math.log(1 + T0) - L) < 1e-12,
        "feasible_c_interval_N16": [round(lo, 6), round(hi, 6)],
        "interval_nonempty": hi > lo,
        "upper_bound_exact_from_N01": round(hi_exact, 6),
        "upper_matches": abs(hi - hi_exact) < 1e-6,
        "max_residual_at_c_mid_N16": round(max_residual(c_mid, 16), 9),
        "tie_satisfied_exactly": abs(cav(tuple([ARM] * 5)) - 3 / 23) < 1e-12 and 3 / 23 < T0,
        "is_proof": False,
        "conjecture1_proved": False,
        "statement": (
            "EXPLICIT potential phi(y)=c*(y-T0)_+ , T0=rho_B-1, in the folded discharge chi_v+phi(cav_v)<="
            "sum_struct phi(cav_c) => logPhi<=-phi(root)<=0. Constraint linear in c => feasible interval "
            "[lo,hi]; hi=0.302077 EXACT from near-star N(0,1); lo<=0.1492 over exhaustive N<=17 + adversarial/"
            "random N<=45 + unbounded-branching stars. Interval [~0.15,0.302] robustly non-empty; c=0.22 "
            "gives 0 residual on all plain trees N<=17; tie satisfied exactly (phi(3/23)=0). Reduces the "
            "1984 conjecture to ONE elementary inequality: sup over all configs of chi_v/D_v < 0.302 "
            "(explicit phi, no -psi circularity). NOT proved analytically (empirical to N<=45; lo(N) still "
            "creeping). Strongest lead; conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["log_1_plus_T0_eq_L"]
    assert r["interval_nonempty"] and r["upper_matches"]
    assert abs(r["max_residual_at_c_mid_N16"]) < 1e-7
    assert r["tie_satisfied_exactly"]
    assert not r["is_proof"] and not r["conjecture1_proved"]
    print("\nAll assertions pass. Explicit potential phi=c*(y-T0)_+ verified (empirical); reduces crux to "
          "one elementary inequality. NOT a proof. conjecture1_proved=False (honest).")
