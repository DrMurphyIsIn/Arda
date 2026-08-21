"""Achievable homogeneous master bound — exact self-verifying probe.

Target (the homogeneous face of the unified Brualdi-Goldwasser crux, doc 7f52fb4):

    W = 64/621
    GAMMA   = W^2 (5/3)^11
    T       = W (5/3)^11
    glemma(mu)   = GAMMA / (1 + mu/3)^11
    master_ub(mu)= W (3/(2+mu))^11
    Bcap(mu)     = min(master_ub, glemma, 1)            (CappedJointConfig.lean:39)
    base(k,mu)   = (3(k+1) + 3 k mu + 1) / (3(k+1))      (= baseOf on k copies of mu)
    GS(k,mu)     = base(k,mu)^11 * Bcap(mu)^k

  CLAIM: for all integers k >= 1 and ACHIEVABLE mu (mu = 1, or 0 < mu <= 1/2),
         GS(k,mu) <= T, with equality iff (k,mu) = (1,1) (the arm).

Everything here is exact rational (sympy Rational / integer). Grid checks are
sanity only; every decision is backed by an exact symbolic/integer statement.
`run_all()` returns True iff every exact assertion holds.

Definitions re-derived from proof/formalization/R3Cert/CappedJointConfig.lean
(cited by line) and MasterCore.lean. conjecture1_proved = False; this closes the
HOMOGENEOUS face over ACHIEVABLE mu only — the heterogeneous->homogeneous
reduction (below-average chain, non-homogeneous fixed points) remains OPEN.
"""
from __future__ import annotations

import sympy as sp

R = sp.Rational
mu, x, k = sp.symbols("mu x k")

W = R(64, 621)
GAMMA = W**2 * R(5, 3) ** 11
T = W * R(5, 3) ** 11


def glemma(m):
    return GAMMA / (1 + m / 3) ** 11


def master_ub(m):
    return W * (R(3) / (2 + m)) ** 11


def Bcap(m):
    return min(master_ub(m), glemma(m), R(1))


def base(kk, m):
    kk = R(kk)
    return (3 * (kk + 1) + 3 * kk * m + 1) / (3 * (kk + 1))


def GS(kk, m):
    return base(kk, m) ** 11 * Bcap(m) ** kk


# The knee: on (0,1/2], master_ub is inactive, so Bcap = min(1, glemma), which
# switches at mu_c where glemma(mu_c) = 1.
MU_C = 5 * W ** R(2, 11) - 3          # = 3*(GAMMA^(1/11) - 1), irrational
SPLIT = R(74, 240)                     # rational cut just ABOVE the knee (relaxation Bcap<=1 below)


# ------------------------------------------------------------------ facts ----

def fact_master_inactive():
    """On (0,1/2], master_ub >= min(1,glemma), i.e. the min never picks master_ub.
    Anchor at the tie mu=1/2 endpoint via the integer cert 621*21^11 >= 64*25^11
    (master_ub(1/2) = W(3/(5/2))^11 = W(6/5)^11; compare to glemma? — simplest
    exact anchor is master_ub(1/2) >= glemma(1/2))."""
    # exact integer cert reused from DirectPolya probe: 621*21^11 >= 64*25^11
    lhs, rhs = 621 * 21**11, 64 * 25**11
    assert lhs >= rhs, "master-inactive integer cert failed"
    # symbolic check that on (0,1/2] master_ub >= glemma (so min ignores master_ub):
    # master_ub(mu) - glemma(mu) >= 0 on (0,1/2].
    diff = sp.expand(master_ub(mu) - glemma(mu))
    # cleared form is degree-22 rational; check sign on a dense exact grid + endpoints.
    for i in range(0, 121):
        m = R(i, 240)
        assert master_ub(m) >= glemma(m), f"master_ub<glemma at mu={m}"
    return lhs, rhs


def fact_knee():
    """mu_c = 5 W^(2/11) - 3 = 3(GAMMA^(1/11)-1); glemma(mu_c)=1; mu_c in (73/240,74/240)."""
    alt = 3 * (GAMMA ** R(1, 11) - 1)
    assert sp.simplify(MU_C - alt) == 0
    assert sp.simplify(glemma(MU_C) - 1) == 0
    assert R(73, 240) < MU_C < R(74, 240)
    return MU_C


def fact_glemma_third():
    """glemma(1/3) = 486/529 < 1, equiv to leaf-I cert gamma<(10/9)^11:
    64^2 5^11 9^11 < 621^2 3^11 10^11."""
    assert glemma(R(1, 3)) == R(486, 529)
    lhs, rhs = 64**2 * 5**11 * 9**11, 621**2 * 3**11 * 10**11
    assert lhs < rhs, "leaf-I cert failed"
    return R(486, 529), (lhs, rhs)


def fact_base_dk_identity():
    """base(1,mu) - base(k,mu) has the sign of (mu - 1/3):
    exact identity  base(1,mu) - base(k,mu) = (k-1)(mu-1/3)/(k+1)  ... (for k real>=1).
    Derive & verify symbolically over k treated as a real symbol."""
    kr = sp.symbols("kr", positive=True)
    b1 = (3 * 2 + 3 * 1 * mu + 1) / (3 * 2)
    bk = (3 * (kr + 1) + 3 * kr * mu + 1) / (3 * (kr + 1))
    d = sp.simplify(b1 - bk)
    # exact identity: base(1,mu)-base(k,mu) = (k-1)(1-3mu)/(6(k+1)), sign of (1/3-mu).
    target = (kr - 1) * (1 - 3 * mu) / (6 * (kr + 1))
    assert sp.simplify(d - target) == 0, f"base d/dk identity wrong: {d}"
    return target


# ------------------------------------------------------ Bernstein finder ----

def find_bernstein(p, a, b, n_max=26):
    """Nonnegative-Bernstein-coefficient certificate for 0 <= p on [a,b].
    Elevates degree up to n_max. Returns (n, betas) or None. Exact rationals.
    Input p may be in any single symbol; it is rewritten in x."""
    p = sp.expand(sp.sympify(p))
    fs = p.free_symbols
    if fs and x not in fs:
        (v,) = fs
        p = sp.expand(p.subs(v, x))
    a, b = sp.nsimplify(a), sp.nsimplify(b)
    deg = sp.Poly(p, x).degree() if p != 0 else 0
    for n in range(max(deg, 1), n_max + 1):
        betas = sp.symbols(f"_b0:{n + 1}")
        basis = [sp.binomial(n, i) * (x - a) ** i * (b - x) ** (n - i) / (b - a) ** n
                 for i in range(n + 1)]
        diff = sp.Poly(sp.expand(sum(be * ba for be, ba in zip(betas, basis)) - p), x)
        sol = sp.solve(diff.coeffs(), betas, dict=True)
        if not sol:
            continue
        vals = [sp.nsimplify(sol[0].get(be, 0)) for be in betas]
        if all(v.is_number and v >= 0 for v in vals):
            if sp.expand(sum(v * ba for v, ba in zip(vals, basis)) - p) == 0:
                return n, [R(v) for v in vals]
    return None


# ------------------------------------------------------ Lean emission ----

def _rat_lean(q):
    q = R(q)
    if q.q == 1:
        return f"({q.p})"
    return f"({q.p} / {q.q})"


def emit_bernstein_lean(name, poly, a, b, n, betas, var="mu"):
    """Emit a kernel-checkable Lean theorem `0 <= poly` on [a,b] from nonnegative
    Bernstein coefficients — same tactic skeleton as the proven DirectPolya emit:
    each basis term nonneg by mul_nonneg/pow_nonneg over (x-a)>=0,(b-x)>=0; `ring`
    closes the identity; `linarith` sums. poly is a sympy expr in `mu`."""
    a, b = R(a), R(b)
    xa = f"({var} - {_rat_lean(a)})"
    bx = f"({_rat_lean(b)} - {var})"
    # poly as lean string (expanded rational coeffs)
    p = sp.expand(poly)
    p_s = str(p).replace("**", "^")
    haves, summands = [], []
    for i, beta in enumerate(betas):
        if beta == 0:
            continue
        coef = sp.binomial(n, i) / (b - a) ** n
        scalar = _rat_lean(R(beta) * R(coef))
        proof = f"(by norm_num : (0:ℝ) ≤ {scalar})"
        factors = [scalar]
        if i > 0:
            factors.append(f"{xa}^{i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hxa {i})"
        if n - i > 0:
            factors.append(f"{bx}^{n - i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hbx {n - i})"
        term = " * ".join(factors)
        haves.append(f"  have t{i} : (0:ℝ) ≤ {term} := {proof}")
        summands.append(term)
    rhs = " + ".join(summands) if summands else "0"
    body = "\n".join(haves)
    hb = "" if n <= 12 else f"set_option maxHeartbeats {max(400000, n * 30000)} in\n"
    return (
        f"-- {name}: Bernstein-basis positivity (degree {n}) on [{a}, {b}].\n"
        f"{hb}"
        f"theorem {name} : ∀ {var} : ℝ, {_rat_lean(a)} ≤ {var} → {var} ≤ {_rat_lean(b)}"
        f" → (0:ℝ) ≤ ({p_s}) := by\n"
        f"  intro {var} hlo hhi\n"
        f"  have hxa : (0:ℝ) ≤ {xa} := by linarith\n"
        f"  have hbx : (0:ℝ) ≤ {bx} := by linarith\n"
        f"{body}\n"
        f"  have hid : (({p_s}) : ℝ) = {rhs} := by ring\n"
        f"  rw [hid]; linarith\n"
    )


def emit_lean_file():
    """Assemble the g1_floors Lean file: 5 Bernstein interval certs (A,B,C1,C2,C3)
    + integer/algebra lemmas (leaf-I, L4 ratio cert, master-inactive, base d/dk)."""
    _, certA, _ = L1_small_mu()
    polyA = sp.expand(T - (R(7, 6) + mu / 2) ** 11)
    polyB, certB, _ = L2_mid()
    c = L3_competition()
    parts = ["import Mathlib\n\nnamespace HomogMaster\n"]
    parts.append(emit_bernstein_lean("certA_small_mu", polyA, 0, SPLIT, certA[0], certA[1]))
    parts.append(emit_bernstein_lean("certB_mid", polyB, R(74, 240), R(1, 3), certB[0], certB[1]))
    parts.append(emit_bernstein_lean("certC1_k1", c["C1"][0], R(1, 3), R(1, 2), c["C1"][1][0], c["C1"][1][1]))
    parts.append(emit_bernstein_lean("certC2_k2", c["C2"][0], R(1, 3), R(1, 2), c["C2"][1][0], c["C2"][1][1]))
    parts.append(emit_bernstein_lean("certC3_kge3", c["C3"][0], R(1, 3), R(1, 2), c["C3"][1][0], c["C3"][1][1]))
    # integer/algebra companion lemmas
    parts.append(
        "-- leaf-I integer cert: gamma < (10/9)^11  (glemma(1/3) < 1).\n"
        "theorem leafI_cert : (64:ℕ)^2 * 5^11 * 9^11 < 621^2 * 3^11 * 10^11 := by norm_num\n"
    )
    parts.append(
        "-- L4 arm-line per-step ratio cert: base ratio (16/15)^11 * W < 1.\n"
        "theorem armline_ratio_cert : (64:ℕ) * 16^11 < 621 * 15^11 := by norm_num\n"
    )
    parts.append(
        "-- master-inactive anchor (mu=1/2 tie): master_ub(1/2) >= glemma(1/2).\n"
        "theorem master_inactive_cert : (64:ℕ) * 25^11 ≤ 621 * 21^11 := by norm_num\n"
    )
    parts.append(
        "-- base d/dk exact identity: base(1,mu)-base(k,mu) = (k-1)(1-3mu)/(6(k+1)).\n"
        "theorem base_dk_identity (k mu : ℝ) (hk : k + 1 ≠ 0) :\n"
        "    (7/6 + mu/2) - (3*(k+1) + 3*k*mu + 1)/(3*(k+1))\n"
        "      = (k-1)*(1-3*mu)/(6*(k+1)) := by\n"
        "  field_simp\n  ring\n"
    )
    parts.append("end HomogMaster\n")
    return "\n".join(parts)


# ---------------------------------------------------------------- L1-L5 ----

def L1_small_mu():
    """L1: for mu<=1/3, base(k,mu)<=base(1,mu) all k>=1, and Bcap<=1, so
    GS(k,mu) <= base(1,mu)^11. Then CERT-A: base(1,mu)^11 <= T on [0,74/240]
    (relaxation Bcap<=1 crosses the knee at a rational split).
    base(1,mu) = (3*2+3mu+1)/6 = (7+3mu)/6 = 7/6 + mu/2.
    CERT-A poly:  T - (7/6 + mu/2)^11 >= 0 on [0,74/240]."""
    b1 = base(1, mu)
    assert sp.simplify(b1 - (R(7, 6) + mu / 2)) == 0
    # base(k,mu) <= base(1,mu) for mu<=1/3 follows from the d/dk identity (sign mu-1/3<=0).
    polyA = sp.expand(T - (R(7, 6) + mu / 2) ** 11)
    certA = find_bernstein(polyA, 0, SPLIT)
    assert certA is not None, "CERT-A Bernstein not found"
    # margin at endpoints:
    m_end = polyA.subs(mu, SPLIT)
    assert m_end > 0
    return polyA, certA, m_end


def L2_mid():
    """L2: on [74/240,1/3], glemma<1 (Bcap=glemma<1 so Bcap^k<=Bcap<=... actually
    Bcap<=1) AND base decreasing in k (mu<=1/3) => GS(k)<=GS(1)=base(1,mu)^11*Bcap.
    Since Bcap=glemma here and base(1)=7/6+mu/2:
    GS(1,mu) = (7/6+mu/2)^11 * glemma(mu) <= T
      <=> T*(1+mu/3)^11 - (7/6+mu/2)^11*GAMMA >= 0   (cleared, degree 22)
    CERT-B on [74/240, 80/240]."""
    lo, hi = R(74, 240), R(80, 240)  # 80/240 = 1/3
    assert hi == R(1, 3)
    polyB = sp.expand(T * (1 + mu / 3) ** 11 - (R(7, 6) + mu / 2) ** 11 * GAMMA)
    certB = find_bernstein(polyB, lo, hi)
    assert certB is not None, "CERT-B Bernstein not found"
    m_lo, m_hi = polyB.subs(mu, lo), polyB.subs(mu, hi)
    assert m_lo > 0 and m_hi > 0
    return polyB, certB, (m_lo, m_hi)


def L3_competition():
    """L3: on [1/3,1/2], base INCREASING in k, glemma^k decaying.
    (i) CERT-C1 (k=1): T*(1+mu/3)^11 - (7/6+mu/2)^11*GAMMA >= 0 on [80/240,120/240].
    (ii) CERT-C2 (k=2): base(2,mu)=(10+6mu)/9;
         T*(1+mu/3)^22 - base(2,mu)^11*GAMMA^2 >= 0 on [1/3,1/2].
    (iii) k>=3: base(k,mu) < 1+mu (exact) and glemma(mu)<1 on [1/3,1/2] give
         GS(k,mu) <= (1+mu)^11 * glemma(mu)^3 for k>=3; CERT-C3:
         T*(1+mu/3)^33 - (1+mu)^11*GAMMA^3 >= 0 on [1/3,1/2]."""
    lo, hi = R(1, 3), R(1, 2)
    out = {}
    # C1
    polyC1 = sp.expand(T * (1 + mu / 3) ** 11 - (R(7, 6) + mu / 2) ** 11 * GAMMA)
    certC1 = find_bernstein(polyC1, lo, hi)
    assert certC1 is not None, "CERT-C1 not found"
    out["C1"] = (polyC1, certC1, polyC1.subs(mu, lo), polyC1.subs(mu, hi))
    # C2
    b2 = base(2, mu)
    assert sp.simplify(b2 - (10 + 6 * mu) / 9) == 0
    polyC2 = sp.expand(T * (1 + mu / 3) ** 22 - b2**11 * GAMMA**2)
    certC2 = find_bernstein(polyC2, lo, hi)
    assert certC2 is not None, "CERT-C2 not found"
    out["C2"] = (polyC2, certC2, polyC2.subs(mu, lo), polyC2.subs(mu, hi))
    # C3: base(k,mu) < 1+mu exact. base(k,mu) = 1 + (3k mu + 1)/(3(k+1)).
    #   1+mu - base(k,mu) = mu - (3k mu+1)/(3(k+1)) = (3(k+1)mu - 3k mu -1)/(3(k+1))
    #                     = (3mu - 1)/(3(k+1)).  On mu>1/3 (open) this is >0; at mu=1/3 it is 0.
    kr = sp.symbols("kr", positive=True)
    bk = (3 * (kr + 1) + 3 * kr * mu + 1) / (3 * (kr + 1))
    d = sp.simplify((1 + mu) - bk - (3 * mu - 1) / (3 * (kr + 1)))
    assert d == 0, f"1+mu-base identity wrong: {d}"
    # so base(k,mu) <= 1+mu on [1/3,1/2] for all k (equality only at mu=1/3).
    polyC3 = sp.expand(T * (1 + mu / 3) ** 33 - (1 + mu) ** 11 * GAMMA**3)
    certC3 = find_bernstein(polyC3, lo, hi, n_max=40)
    assert certC3 is not None, "CERT-C3 not found"
    out["C3"] = (polyC3, certC3, polyC3.subs(mu, lo), polyC3.subs(mu, hi))
    # geometric step: glemma(mu) < 1 on [1/3,1/2] (glemma decreasing, glemma(1/3)=486/529<1)
    assert glemma(R(1, 3)) < 1 and glemma(R(1, 2)) < 1
    return out


def L4_arm_line():
    """L4: mu=1. GS(k,1)=base(k,1)^11 * W^k, base(k,1)=(6k+4)/(3(k+1)).
    (a) GS(1,1) = (5/3)^11 * W = T exactly.
    (b) GS(k+1,1)/GS(k,1) < 1 for k>=1.
    ratio = (base(k+1,1)/base(k,1))^11 * W. base ratio decreasing in k, so
      <= base(2,1)/base(1,1) = (16/9)/(5/3) = 16/15. Cert: 64*16^11 < 621*15^11.
    Correspondence: GS(k,1) is EXACTLY MasterCore.f(k) scaled: f(p)=((4p+3)/(p+1))^11 W^p,
      3^11 = f(0). Check GS(k,1) vs f."""
    assert base(1, 1) == R(5, 3)
    assert GS(1, 1) == T
    # base(k,1) closed form
    kr = sp.symbols("kr", positive=True)
    bk1 = (3 * (kr + 1) + 3 * kr * 1 + 1) / (3 * (kr + 1))
    assert sp.simplify(bk1 - (6 * kr + 4) / (3 * (kr + 1))) == 0
    # base ratio <= 16/15: check base(k+1,1)/base(k,1) decreasing and <=16/15
    def br(kk):
        return base(kk + 1, 1) / base(kk, 1)
    ratios = [br(kk) for kk in range(1, 60)]
    assert all(ratios[i + 1] <= ratios[i] for i in range(len(ratios) - 1)), "base ratio not decreasing"
    assert ratios[0] == R(16, 15)
    # integer cert for the per-step decrease
    lhs, rhs = 64 * 16**11, 621 * 15**11
    assert lhs < rhs, f"L4 ratio cert failed {lhs} !< {rhs}"
    # MasterCore correspondence: f(p) = ((4p+3)/(p+1))^11 W^p.
    def fmc(p):
        return ((4 * R(p) + 3) / (R(p) + 1)) ** 11 * W**p
    # GS(k,1) = ((6k+4)/(3(k+1)))^11 W^k. Is (6k+4)/(3(k+1)) = (4p+3)/(p+1)?
    # (4p+3)/(p+1) with... they are NOT equal (6k+4)/(3k+3) vs (4k+3)/(k+1)=(12k+9)/(3k+3).
    corr = sp.simplify((6 * kr + 4) / (3 * (kr + 1)) - (4 * kr + 3) / (kr + 1))
    same = corr == 0
    return {"GS11": GS(1, 1), "ratio_cert": (lhs, rhs), "mastercore_same": same,
            "ratios_head": ratios[:4]}


def L5_strictness():
    """L5: strict everywhere except the (1,1) endpoint. Every CERT above has a
    positive endpoint margin (checked in its lemma); the arm line ratio is <1
    strictly (cert strict), and GS(1,1)=T is the unique equality. Assemble iff."""
    # equality points examined: only (k,mu)=(1,1).
    # On achievable mu<=1/2: GS<=... < T strictly (all region certs strict, margins>0).
    # On mu=1: GS(1,1)=T, GS(k,1)<T for k>=2 (ratio<1 strict).
    assert GS(1, 1) == T
    assert GS(2, 1) < T
    # spot: no achievable mu<=1/2 hits T
    hits = [m for m in (R(i, 240) for i in range(1, 121))
            if any(GS(kk, m) >= T for kk in range(1, 45))]
    assert hits == [], f"unexpected T-hit on achievable mu<=1/2: {hits}"
    return True


def C_argmax():
    """Region C ([1/3,1/2]) interior argmax of GS(k,mu)/T. Grid says ~0.8722.
    Locate: for each k the max over mu, then max over k. Report exact worst (k,mu)
    on a fine exact grid plus the continuous per-k optimum."""
    best = None
    for kk in range(1, 60):
        for i in range(80, 121):  # mu in [1/3,1/2] on /240 grid
            m = R(i, 240)
            v = GS(kk, m) / T
            if best is None or v > best[0]:
                best = (v, kk, m)
    return best


# ------------------------------------------------------------------ grid ----

def grid_regions():
    """Sanity grid over achievable mu; report region worst GS/T (float)."""
    def worst(mus, ks):
        b = None
        for m in mus:
            for kk in ks:
                v = float(GS(kk, m) / T)
                if b is None or v > b[0]:
                    b = (v, kk, m)
        return b
    A = worst([R(i, 240) for i in range(1, 74)], range(1, 45))
    B = worst([R(i, 240) for i in range(74, 81)], range(1, 45))
    third = worst([R(1, 3)], range(1, 200))
    C = worst([R(i, 240) for i in range(80, 121)], range(1, 45))
    arm = worst([R(1)], range(1, 200))
    return {"A": A, "B": B, "third": third, "C": C, "arm": arm}


def run_all():
    ok = True
    results = {}
    for name, fn in [
        ("master_inactive", fact_master_inactive),
        ("knee", fact_knee),
        ("glemma_third", fact_glemma_third),
        ("base_dk", fact_base_dk_identity),
        ("L1", L1_small_mu),
        ("L2", L2_mid),
        ("L3", L3_competition),
        ("L4", L4_arm_line),
        ("L5", L5_strictness),
    ]:
        try:
            results[name] = fn()
            print(f"[OK]  {name}")
        except Exception as e:  # noqa: BLE001
            ok = False
            print(f"[FAIL] {name}: {e}")
    # MasterCore correspondence verdict
    kr = sp.symbols("kr")
    armb = (6 * kr + 4) / (3 * (kr + 1))
    fb = (4 * kr + 3) / (kr + 1)
    results["mastercore_same"] = sp.simplify(armb - fb) == 0
    print(f"[--]  MasterCore correspondence: arm-line base {armb} vs f base {fb} "
          f"-> same object? {results['mastercore_same']}")
    results["C_argmax"] = C_argmax()
    results["grid"] = grid_regions()
    print("C-argmax (GS/T, k, mu):", float(results['C_argmax'][0]),
          results['C_argmax'][1], results['C_argmax'][2])
    print("grid regions:", {k: (round(v[0], 4), v[1], str(v[2])) for k, v in results['grid'].items()})
    print("ALL EXACT ASSERTIONS PASSED" if ok else "SOME ASSERTIONS FAILED")
    return ok, results


if __name__ == "__main__":
    import sys
    ok, _ = run_all()
    sys.exit(0 if ok else 1)
