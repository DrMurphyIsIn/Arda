"""DirectPolya per-child ENVELOPE for the config g-step (Case 2 reframe), 2026-08-20.

The config g-step (R3Cert.CappedJointConfig, commit 036fa9e) needs, for every achievable
child config `l = [mu_1..mu_j]` (mu_i in (0,1/2]):

    gstep_factor(l) = baseOf(l)^11 * prod_i Bcap(mu_i) / DENOM  <=  1,

with  W = 64/621,  GAMMA = W^2 (5/3)^11,  DENOM = W (5/3)^11,
      glemma(mu) = GAMMA/(1+mu/3)^11,  master_ub(mu) = W (3/(2+mu))^11,
      Bcap(mu) = min(master_ub, glemma, 1),
      baseOf(l) = (3d+3S+1)/(3d),  d = j+1,  S = sum mu_i.

`Case2Property` (the base>threshold half) is the genuine analytic wall.  The DirectPolya idea:
replace the kinked per-child cap `Bcap` by a LOW-DEGREE per-child ENVELOPE `phi(mu) >= Bcap(mu)`
that (E1) dominates Bcap on (0,1/2] and (E2) still gives baseOf^11 * prod phi <= DENOM.  Both
obligations become Positivstellensatz-shaped -- exactly find_handelman_certificate territory.

FINDINGS (this module, all exact rational arithmetic):

  * Bcap STRUCTURE.  On (0,1/2] master_ub is NEVER the min: master_ub/glemma is decreasing with
    minimum (1/W)(21/25)^11 > 1 at mu=1/2, i.e. 621*21^11 >= 64*25^11.  So Bcap = min(1, glemma).
    The kink is at mu_c with (3+mu_c)^11 = 5^11 W^2 (= 200000000000/385641), mu_c ~ 0.30774,
    bracket mu_c in (73/240, 74/240).

  * ENVELOPE (clean, exact).  phi(mu) = min(1, 87/50 - 12/5 mu) = min(1, (87 - 120 mu)/50):
        phi = 1                on [0, 37/120],
        phi = 87/50 - 12/5 mu  on [37/120, 1/2]   (hits 1 at 37/120, 27/50 at 1/2).
    phi <= 1 everywhere (monotone-safe: adding children only shrinks the product), and
    phi >= Bcap:  on [0,37/120] by Bcap <= 1;  on [37/120,1/2] by phi >= glemma (E1-upper).
    E2 slack cost: at the j=2 worst point the true gstep_factor is 0.7231; with the envelope it
    is 0.7400 -- the envelope eats ~0.017 of the 0.277 margin (leaves margin 0.260).

  * CERTIFICATES (Handelman = nonneg combination of box-constraint products; found via the
    Bernstein basis on the box, which is a subcone of the Handelman cone, and EXACT-verified):
      E1-upper  (deg 12, [37/120,1/2]):           13-term cert, min Bernstein coef 0.00577.
      E2 j=2 UU (deg 12x12, [37/120,1/2]^2):       169-term cert, min coef 7.284.
      E2 j=2 LU (deg 11x12):                       156-term cert, min coef 7.516.
      E2 j=2 LL (deg 11x11, corner base^11<=DENOM):144-term cert, min coef 7.790.

  * j >= 3.  No induction reduces j>=3 to j=2 (adding a small-mu child raises the base while
    phi ~ 1, so gstep_factor is NOT monotone in child count).  But margins GROW with j
    (j=3 binding cell min coef 8.15) so each fixed j is independently certifiable; a per-j
    finite emission closes any bounded j.  There is no structural j<=2 cap in the config
    formalization, so unbounded j remains a genuine open item for the envelope route.

  * conjecture1_proved = False (untouched).

run_all() re-derives every number and re-verifies every certificate identity exactly.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from math import comb

# ----------------------------------------------------------------------------- constants
W = Fr(64, 621)
GAMMA = W**2 * Fr(5, 3)**11
DENOM = W * Fr(5, 3)**11
A = Fr(37, 120)          # envelope knee (rational, just above mu_c)
HALF = Fr(1, 2)


def glemma(mu: Fr) -> Fr:
    return GAMMA / (1 + mu / 3)**11


def master_ub(mu: Fr) -> Fr:
    return W * (Fr(3) / (2 + mu))**11


def Bcap(mu: Fr) -> Fr:
    return min(master_ub(mu), glemma(mu), Fr(1))


def baseOf(l) -> Fr:
    d = Fr(len(l) + 1)
    S = sum(l, Fr(0))
    return (3 * d + 3 * S + 1) / (3 * d)


def phi(mu: Fr) -> Fr:
    """Envelope phi(mu) = min(1, 87/50 - 12/5 mu)."""
    return min(Fr(1), Fr(87, 50) - Fr(12, 5) * mu)


def gstep_factor(l, cap) -> Fr:
    p = Fr(1)
    for m in l:
        p *= cap(m)
    return baseOf(l)**11 * p / DENOM


# --------------------------------------------------------------- dense polynomial helpers
# Polynomials are dicts {exponent-tuple: Fraction}.  Univariate uses 1-tuples.

def _padd(a, b):
    r = dict(a)
    for k, v in b.items():
        r[k] = r.get(k, Fr(0)) + v
        if r[k] == 0:
            del r[k]
    return r


def _pscale(a, c):
    return {k: v * c for k, v in a.items() if v * c != 0}


def _pmul(a, b):
    r = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            r[k] = r.get(k, Fr(0)) + va * vb
            if r[k] == 0:
                del r[k]
    return r


def _ppow(a, n, nvar):
    r = {tuple([0] * nvar): Fr(1)}
    for _ in range(n):
        r = _pmul(r, a)
    return r


def _var(i, nvar):
    e = [0] * nvar
    e[i] = 1
    return {tuple(e): Fr(1)}


def _const(c, nvar):
    return {tuple([0] * nvar): Fr(c)} if c != 0 else {}


# ------------------------------------------------------- Task 1: Bcap structure & the knee

def task1_bcap_structure():
    """master_ub never active on (0,1/2]; Bcap = min(1, glemma); locate mu_c."""
    # master_ub/glemma = (1/W)(3/5)^11 ((3+mu)/(2+mu))^11, decreasing; min at mu=1/2 is
    # (1/W)(21/25)^11.  master_ub >= glemma  <=>  621*21^11 >= 64*25^11.
    lhs, rhs = 621 * 21**11, 64 * 25**11
    master_dominates = lhs >= rhs
    min_ratio = (Fr(1) / W) * Fr(21, 25)**11
    # sanity on a fine grid
    grid_ok = all(master_ub(Fr(k, 480)) >= min(glemma(Fr(k, 480)), Fr(1))
                  for k in range(1, 241))
    # mu_c bracket: glemma decreasing through 1
    lo = max(Fr(k, 240) for k in range(0, 121) if glemma(Fr(k, 240)) >= 1)
    hi = min(Fr(k, 240) for k in range(0, 121) if glemma(Fr(k, 240)) < 1)
    # exact algebraic condition (3+mu_c)^11 = 5^11 W^2
    muc_pow = Fr(5)**11 * W**2
    return {
        "master_ge_glemma_cert": (lhs, rhs, master_dominates),
        "min_ratio_master_over_glemma": min_ratio,
        "grid_master_never_min": grid_ok,
        "mu_c_bracket": (lo, hi),
        "mu_c_pow_condition_(3+muc)^11": muc_pow,
    }


# --------------------------------------------------- Task 2: envelope domination & E2 cost

def task2_envelope():
    """phi >= Bcap on (0,1/2]; envelope continuous at the knee; E2 slack at j=2 worst."""
    # continuity: phi_line(37/120) = 1
    knee_val = Fr(87, 50) - Fr(12, 5) * A
    # phi >= Bcap on a fine grid (exact)
    dom = all(phi(Fr(k, 960)) >= Bcap(Fr(k, 960)) for k in range(1, 481))
    # phi <= 1 everywhere
    le1 = all(phi(Fr(k, 960)) <= 1 for k in range(1, 481))
    # E2 cost at j=2: compare true vs envelope worst
    true_max = max(gstep_factor([Fr(k, 960), Fr(k, 960)], Bcap) for k in range(1, 481))
    env_max = max(gstep_factor([Fr(k, 960), Fr(k, 960)], phi) for k in range(1, 481))
    return {
        "knee_continuity_phi(37/120)": knee_val,
        "phi_dominates_Bcap": dom,
        "phi_le_one": le1,
        "j2_true_worst": true_max,
        "j2_envelope_worst": env_max,
        "j2_margin_eaten": true_max - env_max,     # negative-of-cost is fine; report both
        "j2_envelope_margin": Fr(1) - env_max,
    }


# ------------------------------------------------- Bernstein->Handelman certificate finder

def bernstein_cert_univar(P, x0, x1):
    """P (1-var dense dict) >= 0 on [x0,x1] via Bernstein coeffs.  Returns
    (all_nonneg, min_coef, terms, recon_ok) where terms = [(coef, (k, n-k))] over the
    box constraints [x-x0, x1-x] (a Handelman certificate when all coefs >= 0)."""
    n = max(k[0] for k in P) if P else 0
    c = [P.get((j,), Fr(0)) for j in range(n + 1)]
    # substitute x = x0 + (x1-x0) t : coeffs of the t-poly
    h = x1 - x0
    ct = [Fr(0)] * (n + 1)
    for j in range(n + 1):
        # (x0 + h t)^j = sum_i C(j,i) x0^(j-i) h^i t^i, weighted by c[j]
        for i in range(j + 1):
            ct[i] += c[j] * comb(j, i) * x0**(j - i) * h**i
    betas = [sum(Fr(comb(k, j), comb(n, j)) * ct[j] for j in range(k + 1))
             for k in range(n + 1)]
    terms = [(betas[k] * comb(n, k) / h**n, (k, n - k)) for k in range(n + 1)]
    # exact reconstruction: sum coef (x-x0)^k (x1-x)^(n-k)
    recon = {}
    for coef, (e1, e2) in terms:
        term = _pmul(_ppow(_padd(_var(0, 1), _const(-x0, 1)), e1, 1),
                     _ppow(_padd(_const(x1, 1), _pscale(_var(0, 1), Fr(-1))), e2, 1))
        recon = _padd(recon, _pscale(term, coef))
    recon_ok = _padd(P, _pscale(recon, Fr(-1))) == {}
    return all(b >= 0 for b in betas), min(betas), terms, recon_ok


def bernstein_cert_2d(P, xr, yr):
    """P (2-var dense dict, vars 0=x,1=y) >= 0 on [x0,x1]x[y0,y1] via tensor Bernstein.
    terms = [(coef, (k, dx-k, l, dy-l))] over [x-x0, x1-x, y-y0, y1-y]."""
    (x0, x1), (y0, y1) = xr, yr
    dx = max((k[0] for k in P), default=0)
    dy = max((k[1] for k in P), default=0)
    # coeffs of P(x0+hx s, y0+hy t) in (s,t)
    hx, hy = x1 - x0, y1 - y0
    cst = {}
    for (ex, ey), v in P.items():
        for i in range(ex + 1):
            wx = v * comb(ex, i) * x0**(ex - i) * hx**i
            for j in range(ey + 1):
                w = wx * comb(ey, j) * y0**(ey - j) * hy**j
                cst[(i, j)] = cst.get((i, j), Fr(0)) + w
    betas = {}
    for k in range(dx + 1):
        for l in range(dy + 1):
            s = Fr(0)
            for i in range(k + 1):
                bi = Fr(comb(k, i), comb(dx, i))
                for j in range(l + 1):
                    s += bi * Fr(comb(l, j), comb(dy, j)) * cst.get((i, j), Fr(0))
            betas[(k, l)] = s
    terms = [(betas[(k, l)] * comb(dx, k) * comb(dy, l) / (hx**dx * hy**dy),
              (k, dx - k, l, dy - l))
             for k in range(dx + 1) for l in range(dy + 1)]
    # reconstruct
    xm, ym = _var(0, 2), _var(1, 2)
    fxlo = _padd(xm, _const(-x0, 2))
    fxhi = _padd(_const(x1, 2), _pscale(xm, Fr(-1)))
    fylo = _padd(ym, _const(-y0, 2))
    fyhi = _padd(_const(y1, 2), _pscale(ym, Fr(-1)))
    recon = {}
    for coef, (a1, a2, b1, b2) in terms:
        t = _pmul(_pmul(_ppow(fxlo, a1, 2), _ppow(fxhi, a2, 2)),
                  _pmul(_ppow(fylo, b1, 2), _ppow(fyhi, b2, 2)))
        recon = _padd(recon, _pscale(t, coef))
    recon_ok = _padd(P, _pscale(recon, Fr(-1))) == {}
    mn = min(betas.values())
    return all(b >= 0 for b in betas.values()), mn, terms, recon_ok


# ----------------------------------------------------------- Task 3: run the finders (E1,E2)

def _phi_line_poly(nvar, ivar):
    """87/50 - 12/5 mu_i as a dense poly."""
    return _padd(_const(Fr(87, 50), nvar), _pscale(_var(ivar, nvar), Fr(-12, 5)))


def task3_certificates():
    out = {}
    # E1-upper: P = phi_line(mu)*(1+mu/3)^11 - GAMMA >= 0 on [A, 1/2]
    one_plus = _padd(_const(1, 1), _pscale(_var(0, 1), Fr(1, 3)))
    P_up = _padd(_pmul(_phi_line_poly(1, 0), _ppow(one_plus, 11, 1)),
                 _const(-GAMMA, 1))
    out["E1_upper"] = bernstein_cert_univar(P_up, A, HALF)

    # E2 cells (2 vars).  base2 = (10+3x+3y)/9.
    base2 = _padd(_const(Fr(10, 9), 2),
                  _padd(_pscale(_var(0, 2), Fr(1, 3)), _pscale(_var(1, 2), Fr(1, 3))))
    base2_11 = _ppow(base2, 11, 2)
    phix, phiy = _phi_line_poly(2, 0), _phi_line_poly(2, 1)
    # UU: DENOM - base2^11 phi(x) phi(y)
    P_UU = _padd(_const(DENOM, 2),
                 _pscale(_pmul(base2_11, _pmul(phix, phiy)), Fr(-1)))
    out["E2_UU"] = bernstein_cert_2d(P_UU, (A, HALF), (A, HALF))
    # LU: DENOM - base2^11 * 1 * phi(y)  on [0,A]x[A,1/2]
    P_LU = _padd(_const(DENOM, 2), _pscale(_pmul(base2_11, phiy), Fr(-1)))
    out["E2_LU"] = bernstein_cert_2d(P_LU, (Fr(0), A), (A, HALF))
    # LL: DENOM - base2^11  on [0,A]^2
    P_LL = _padd(_const(DENOM, 2), _pscale(base2_11, Fr(-1)))
    out["E2_LL"] = bernstein_cert_2d(P_LL, (Fr(0), A), (Fr(0), A))
    return out


# ---------------------------------------------------------------- Task 4: j >= 3 assessment

def task4_j3():
    """No j->j+1 monotone induction; but binding cell of each fixed j certifiable.
    Verify j=3 binding cell (all three children in [A,1/2]) via 3D tensor Bernstein."""
    # 'adding a child never increases gstep_factor' is FALSE: for a config whose base is still
    # far below saturation, adding a moderate child raises the base by more than phi(mu)<1
    # suppresses.  Explicit exact witness (ratio > 1) -> no simple j->j+1 induction.
    l = [Fr(1, 240), Fr(1, 80)]
    mu = Fr(79, 240)
    with_extra = gstep_factor(l + [mu], phi)
    without = gstep_factor(l, phi)
    induction_holds = with_extra <= without   # False (ratio ~ 1.58)

    # j=3 binding cell via 3D Bernstein (min coefficient sign only, no full recon storage)
    A3, H3 = A, HALF
    # base3=(13+3(x+y+z))/12 ; P = DENOM - base3^11 phi(x)phi(y)phi(z) on [A,1/2]^3
    base3 = _padd(_const(Fr(13, 12), 3),
                  _padd(_padd(_pscale(_var(0, 3), Fr(1, 4)), _pscale(_var(1, 3), Fr(1, 4))),
                        _pscale(_var(2, 3), Fr(1, 4))))
    base3_11 = _ppow(base3, 11, 3)
    px = _padd(_const(Fr(87, 50), 3), _pscale(_var(0, 3), Fr(-12, 5)))
    py = _padd(_const(Fr(87, 50), 3), _pscale(_var(1, 3), Fr(-12, 5)))
    pz = _padd(_const(Fr(87, 50), 3), _pscale(_var(2, 3), Fr(-12, 5)))
    P3 = _padd(_const(DENOM, 3),
               _pscale(_pmul(base3_11, _pmul(px, _pmul(py, pz))), Fr(-1)))
    dx = max((k[0] for k in P3), default=0)
    dy = max((k[1] for k in P3), default=0)
    dz = max((k[2] for k in P3), default=0)
    hx = hy = hz = H3 - A3
    # substitute and get Bernstein min coefficient
    cst = {}
    for (ex, ey, ez), v in P3.items():
        for i in range(ex + 1):
            wx = v * comb(ex, i) * A3**(ex - i) * hx**i
            for j in range(ey + 1):
                wy = wx * comb(ey, j) * A3**(ey - j) * hy**j
                for m in range(ez + 1):
                    w = wy * comb(ez, m) * A3**(ez - m) * hz**m
                    cst[(i, j, m)] = cst.get((i, j, m), Fr(0)) + w
    mn = None
    allnn = True
    for k in range(dx + 1):
        for l2 in range(dy + 1):
            for m2 in range(dz + 1):
                s = Fr(0)
                for i in range(k + 1):
                    bi = Fr(comb(k, i), comb(dx, i))
                    for j in range(l2 + 1):
                        bj = bi * Fr(comb(l2, j), comb(dy, j))
                        for u in range(m2 + 1):
                            s += bj * Fr(comb(m2, u), comb(dz, u)) * cst.get((i, j, u), Fr(0))
                if s < 0:
                    allnn = False
                if mn is None or s < mn:
                    mn = s
    return {
        "induction_add_child_le": induction_holds,     # expected False
        "add_child_ratio": with_extra / without,
        "j3_binding_all_nonneg": allnn,
        "j3_binding_min_coef": mn,
    }


# ---------------------------------------------------------------------------------- run_all

def run_all():
    print("=" * 74)
    print("DirectPolya envelope probe (config g-step Case 2 reframe) -- exact")
    print("=" * 74)
    ok = True

    print("\n[Task 1] Bcap structure and the knee mu_c")
    t1 = task1_bcap_structure()
    lhs, rhs, dom = t1["master_ge_glemma_cert"]
    print(f"  master_ub >= glemma cert: 621*21^11={lhs} >= 64*25^11={rhs}: {dom}")
    print(f"  min(master_ub/glemma) over [0,1/2] = {float(t1['min_ratio_master_over_glemma']):.4f} (>1)")
    print(f"  grid: master_ub never the min: {t1['grid_master_never_min']}")
    print(f"  => Bcap = min(1, glemma) on (0,1/2]")
    print(f"  mu_c bracket: {t1['mu_c_bracket']} ~ (0.3042, 0.3083)")
    print(f"  mu_c exact: (3+mu_c)^11 = 5^11 W^2 = {t1['mu_c_pow_condition_(3+muc)^11']}")
    ok &= dom and t1["grid_master_never_min"]

    print("\n[Task 2] Envelope phi(mu) = min(1, 87/50 - 12/5 mu)")
    t2 = task2_envelope()
    print(f"  continuity phi(37/120) = {t2['knee_continuity_phi(37/120)']} (=1)")
    print(f"  phi >= Bcap on (0,1/2]: {t2['phi_dominates_Bcap']}")
    print(f"  phi <= 1 everywhere:    {t2['phi_le_one']}")
    print(f"  j=2 TRUE worst gstep    = {float(t2['j2_true_worst']):.6f} (margin {float(1-t2['j2_true_worst']):.6f})")
    print(f"  j=2 ENVELOPE worst      = {float(t2['j2_envelope_worst']):.6f} (margin {float(t2['j2_envelope_margin']):.6f})")
    print(f"  envelope E2 slack cost  = {float(t2['j2_envelope_worst']-t2['j2_true_worst']):.6f}")
    ok &= (t2["knee_continuity_phi(37/120)"] == 1 and t2["phi_dominates_Bcap"]
           and t2["phi_le_one"] and t2["j2_envelope_margin"] > 0)

    print("\n[Task 3] Handelman certificates (Bernstein-on-box, exact-verified)")
    t3 = task3_certificates()
    for name, (nn, mn, terms, recon) in t3.items():
        print(f"  {name}: nonneg={nn} min_coef={float(mn):.6g} nterms={len(terms)} recon_exact={recon}")
        ok &= nn and recon

    print("\n[Task 4] j >= 3 assessment")
    t4 = task4_j3()
    print(f"  add-child monotone (gstep(l+[mu])<=gstep(l)): {t4['induction_add_child_le']} (expected False)")
    print(f"    example ratio = {float(t4['add_child_ratio']):.4f} (>1: no simple induction)")
    print(f"  j=3 binding cell (all upper) nonneg: {t4['j3_binding_all_nonneg']} min_coef={float(t4['j3_binding_min_coef']):.4f}")
    ok &= (not t4["induction_add_child_le"]) and t4["j3_binding_all_nonneg"]

    print("\n" + "=" * 74)
    print(f"run_all: {'ALL EXACT CHECKS PASS' if ok else 'FAILURE'}   conjecture1_proved = False")
    print("=" * 74)
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if run_all() else 1)
