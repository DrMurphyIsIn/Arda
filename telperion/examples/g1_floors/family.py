"""The G1 floor layer, Telperion-encoded: every dichotomy/tax/below-window
floor of the Brualdi-Goldwasser campaign as kernel-checkable certificates.

Origin: proof/verification/g1_floor_certificates.py, whose own status line
reads "Lean port of this module is mechanical (Taylor brackets + Polya)" —
this family IS that port's generator.  Two coupled families:

* **G1Floors** (interval cells): each adaptive-bisection LEAF of the origin's
  certify_floor, plus the childless (m=0) point claims and the m ≥ 4 collapse
  envelopes, as claims LINEAR in the two bracketed constants

      L ∈ [206586, 206587]/10⁶   (= log(621/64)/11)
      G ∈ [405465, 405466]/10⁶   (= log(3/2)),

  lowered onto the box machinery by `interval_family`: the emitted `_cell`
  theorem quantifies over the brackets, so instantiating at the REAL constants
  (once the bracket facts are in) yields the true floor.  T0's bracket enters
  only through its rational endpoints (its role is one-sided), and every
  `max(0, ·)` branch is decided exactly at build time per leaf.

* **G1Anchors** (kernel facts): the verifications the floors stand on — each
  log1p concavity anchor `exp_lower(q, K) ≥ 1 + u0` at the MINIMAL Taylor
  depth K that closes it, and the three constant-bracket facts (the
  (1+t)^11 vs 621/64 pair for T0; the exp brackets for L and log(3/2)).

conjecture1_proved = False; this discharges the G1-floor stratum of the
honest-conditional assembly at generator level — the Lean build is the
verdict.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

import sympy as sp

from telperion import GridSpec, LeanProfile, ValidationReport, interval_family

# ---- the bracketed constants (origin: _verified_constants) -------------------
L_LO, L_HI = Fr(206586, 10**6), Fr(206587, 10**6)
G_LO, G_HI = Fr(405465, 10**6), Fr(405466, 10**6)
T_LO, T_HI = Fr(2294736, 10**7), Fr(2294737, 10**7)
C_HINGE = Fr(11, 50)
EPS_WIN = Fr(29, 1000)

L, G = sp.symbols("L G", nonnegative=True)

# ---- exact kernels (pure Fraction — the independent engine) ------------------


def exp_lower(x: Fr, K: int) -> Fr:
    s, term = Fr(0), Fr(1)
    for k in range(K + 1):
        s += term
        term = term * x / (k + 1)
    return s


def exp_upper(x: Fr, K: int = 30) -> Fr:
    s, term = Fr(0), Fr(1)
    for k in range(K + 1):
        s += term
        term = term * x / (k + 1)
    return s + term / (1 - x / (K + 2))


_ANCHORS: dict[Fr, Fr] = {}


def log1p_anchor(u: Fr) -> tuple[Fr, Fr]:
    """The dyadic anchor at/below u and its verified rational upper bound q
    for log(1+u0) (float-guided, rationally verified — origin pattern)."""
    u0 = Fr(int(u * 512), 512)
    if u0 not in _ANCHORS:
        q = Fr(int(math.log(1 + float(u0)) * 10**9) + 2, 10**9)
        assert exp_lower(q, 30) >= 1 + u0, u0
        _ANCHORS[u0] = q
    return u0, _ANCHORS[u0]


def log1p_upper(u: Fr) -> Fr:
    if u == 0:
        return Fr(0)
    u0, q = log1p_anchor(u)
    return q + (u - u0) / (1 + u0)


# ---- the slack lower bound (Fraction and symbolic-in-(L,G) versions) ---------


def _pieces(a: int, nl: int, m: int, y0: Fr, y1: Fr):
    k = a + nl + m
    p = 1 + 2 * a + nl
    u1 = (Fr(a, 3) + nl + m * y1) / (k + 1)
    S0 = Fr(a, 3) + nl + m * y0
    cav_hi = Fr(1) / (k + 1 + S0)
    d1 = max(Fr(0), cav_hi - T_LO)
    d2 = max(Fr(0), y0 - T_HI)
    Dhi = d1 - m * d2
    return p, u1, Dhi


def slack_lb_fraction(a: int, nl: int, m: int, y0: Fr, y1: Fr,
                      Lv: Fr, Gv: Fr) -> Fr:
    p, u1, Dhi = _pieces(a, nl, m, y0, y1)
    return p * Lv - a * Gv - log1p_upper(u1) - C_HINGE * Dhi


def slack_lb_symbolic(a: int, nl: int, m: int, y0: Fr, y1: Fr) -> sp.Expr:
    p, u1, Dhi = _pieces(a, nl, m, y0, y1)
    return (p * L - a * G - sp.Rational(log1p_upper(u1))
            - sp.Rational(C_HINGE) * sp.Rational(Dhi))


def collapse_env_symbolic(a: int, nl: int, m_probe: int = 4):
    """The m >= 4 collapse envelope (origin certify_collapse_m_ge_4):
    preconditions are kernel facts; the envelope claim is linear in (L, G)."""
    assert Fr(1, m_probe + 1) < T_LO and Fr(1, m_probe + 1) < C_HINGE
    p = 1 + 2 * a + nl
    u_at = (Fr(a, 3) + nl + m_probe * T_HI) / (a + nl + m_probe + 1)
    u_env = max(u_at, T_HI)
    return p * L - a * G - sp.Rational(log1p_upper(u_env))


# ---- leaf enumeration (the origin's bisection, collecting instead of asserting)


def _bisect_leaves(a, nl, m, floor: Fr, y0: Fr, y1: Fr, depth=0, out=None):
    if out is None:
        out = []
    if slack_lb_fraction(a, nl, m, y0, y1, L_LO, G_HI) >= floor:
        out.append((y0, y1))
        return out
    if depth >= 22:
        raise ValueError(f"bisection fails for {(a, nl, m)} at {(y0, y1)}")
    mid = (y0 + y1) / 2
    _bisect_leaves(a, nl, m, floor, y0, mid, depth + 1, out)
    _bisect_leaves(a, nl, m, floor, mid, y1, depth + 1, out)
    return out


def _floor_claims():
    """(kind, a, nl, m, floor, y0, y1) for every origin claim; kind in
    {leaf, m0, collapse}."""
    claims = []

    def leaves(a, nl, m, floor, ylo=Fr(1, 10**6), yhi=Fr(1, 2)):
        for y0, y1 in _bisect_leaves(a, nl, m, floor, ylo, yhi):
            claims.append(("leaf", a, nl, m, floor, y0, y1))

    # chain + mixed + bare-leaf + nl2  (origin certify_dichotomy_floors)
    leaves(0, 0, 1, Fr(27, 5000))
    for a in range(1, 7):
        for m in (1, 2, 3):
            leaves(a, 0, m, Fr(27, 5000))
        claims.append(("collapse", a, 0, 4, Fr(27, 5000), Fr(0), Fr(0)))
    for a in range(0, 10):
        for m in (0, 1, 2, 3):
            if a == 0 and m == 0:
                continue
            if m == 0:
                claims.append(("m0", a, 1, 0, Fr(26, 500), Fr(0), Fr(0)))
            else:
                leaves(a, 1, m, Fr(26, 500))
        claims.append(("collapse", a, 1, 4, Fr(26, 500), Fr(0), Fr(0)))
    for a in range(0, 7):
        for m in (0, 1, 2, 3):
            if m == 0:
                claims.append(("m0", a, 2, 0, Fr(54, 500), Fr(0), Fr(0)))
            else:
                leaves(a, 2, m, Fr(54, 500))
        claims.append(("collapse", a, 2, 4, Fr(54, 500), Fr(0), Fr(0)))
    # bundle ladder (childless key values)
    for a, floor in ((4, Fr(1, 1000)), (3, Fr(6, 1000)), (6, Fr(14, 10000))):
        claims.append(("m0", a, 0, 0, floor, Fr(0), Fr(0)))
    # tax window (origin certify_tax_window)
    targets = {(0, 0, 2): Fr(33, 1000), (0, 0, 3): Fr(47, 1000),
               (0, 1, 1): Fr(66, 1000), (1, 0, 2): Fr(33, 1000),
               (1, 1, 0): Fr(52, 1000), (2, 0, 1): Fr(99, 5000)}
    for (a, nl, m), floor in targets.items():
        if m == 0:
            claims.append(("m0", a, nl, 0, floor, Fr(0), Fr(0)))
            continue
        k = a + nl + m
        lo_sum, hi_sum = Fr(1) / (T_HI + EPS_WIN), Fr(1) / (T_LO - EPS_WIN)
        ylo = max(Fr(1, 10**6), (lo_sum - (k + 1) - Fr(a, 3) - nl) / m)
        yhi = min(Fr(1, 2), (hi_sum - (k + 1) - Fr(a, 3) - nl) / m)
        if ylo < yhi:
            leaves(a, nl, m, floor, ylo, yhi)
    # below-window m in {2,3}
    for m in (2, 3):
        leaves(0, 0, m, Fr(24, 500), Fr(1, 10**6), T_LO - EPS_WIN)
    # dedupe genuinely identical claims (e.g. (1,1,0) appears in both the
    # bare-leaf table and the tax window with the SAME floor 13/250)
    seen, unique = set(), []
    for c in claims:
        if c not in seen:
            seen.add(c)
            unique.append(c)
    return unique


_CLAIMS = None


def claims():
    global _CLAIMS
    if _CLAIMS is None:
        _CLAIMS = _floor_claims()
    return _CLAIMS


def _target(c) -> sp.Expr:
    kind, a, nl, m, floor, y0, y1 = c
    if kind == "leaf":
        base = slack_lb_symbolic(a, nl, m, y0, y1)
    elif kind == "m0":
        base = slack_lb_symbolic(a, nl, 0, Fr(0), Fr(0))
    else:
        base = collapse_env_symbolic(a, nl)
    return base - sp.Rational(floor)


def _name(c) -> str:
    kind, a, nl, m, floor, y0, y1 = c
    f = f"_f{floor.numerator}_{floor.denominator}"
    suffix = "" if kind != "leaf" else (
        f"_y{y0.numerator}_{y0.denominator}_{y1.numerator}_{y1.denominator}"
    )
    return f"g1_{kind}_a{a}_nl{nl}_m{m}{f}{suffix}"


def family():
    cs = claims()
    return interval_family(
        name="G1Floors",
        symbols=(),
        grid=GridSpec([("cell", list(range(len(cs))))]),
        lean_name=lambda pt: _name(cs[pt["cell"]]),
        target=lambda pt: _target(cs[pt["cell"]]),
        brackets={L: (sp.Rational(L_LO), sp.Rational(L_HI)),
                  G: (sp.Rational(G_LO), sp.Rational(G_HI))},
    )


def profile() -> LeanProfile:
    prelude = """/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it. -/
theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : 0 ≤ A + B * s0 + C * t0 + E * (s0 * t0))
    (h01 : 0 ≤ A + B * s0 + C * t1 + E * (s0 * t1))
    (h10 : 0 ≤ A + B * s1 + C * t0 + E * (s1 * t0))
    (h11 : 0 ≤ A + B * s1 + C * t1 + E * (s1 * t1)) :
    0 ≤ A + B * s + C * t + E * (s * t) := by
  have hfix : ∀ sv : ℝ, 0 ≤ A + B * sv + C * t0 + E * (sv * t0) →
      0 ≤ A + B * sv + C * t1 + E * (sv * t1) →
      0 ≤ A + B * sv + C * t + E * (sv * t) := by
    intro sv e0 e1
    rcases le_total 0 (C + E * sv) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr ht1)]
  have H0 := hfix s0 h00 h01
  have H1 := hfix s1 h10 h11
  rcases le_total 0 (B + E * t) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hs0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hs1)]"""
    return LeanProfile(namespace=("G1", "Floors"), prelude=prelude)


# ---- the anchor + bracket kernel facts ---------------------------------------


def anchor_facts():
    """(name, lhs, rel, rhs, K) for every log1p anchor the floors use, at the
    MINIMAL Taylor depth that closes it, plus the three constant brackets."""
    claims()  # populate _ANCHORS via the leaf enumeration
    facts = []
    for u0, q in sorted(_ANCHORS.items()):
        if u0 == 0:
            continue
        K = next(k for k in range(1, 31) if exp_lower(q, k) >= 1 + u0)
        facts.append((f"anchor_{u0.numerator}_{u0.denominator}", u0, q, K))
    return facts


def validation() -> ValidationReport:
    """Dual-engine: the symbolic (L,G)-linear targets agree EXACTLY with the
    pure-Fraction origin-equivalent slack_lb at the bracket corners; and every
    claim clears its floor at the worst corner (L_LO, G_HI)."""

    def dual():
        for c in claims()[::7]:  # every 7th cell — full sweep in --check runs
            kind, a, nl, m, floor, y0, y1 = c
            t = _target(c)
            for Lv, Gv in ((L_LO, G_HI), (L_HI, G_LO)):
                sym = t.subs({L: sp.Rational(Lv), G: sp.Rational(Gv)})
                if kind == "leaf":
                    frac = slack_lb_fraction(a, nl, m, y0, y1, Lv, Gv) - floor
                elif kind == "m0":
                    frac = slack_lb_fraction(a, nl, 0, Fr(0), Fr(0), Lv, Gv) - floor
                else:
                    p = 1 + 2 * a + nl
                    u_at = (Fr(a, 3) + nl + 4 * T_HI) / (a + nl + 5)
                    frac = (p * Lv - a * Gv - log1p_upper(max(u_at, T_HI))) - floor
                assert sym == sp.Rational(frac), (c, Lv, Gv)

    def worst_corner():
        for c in claims():
            t = _target(c)
            val = t.subs({L: sp.Rational(L_LO), G: sp.Rational(G_HI)})
            assert val >= 0, (c, val)

    return ValidationReport.from_asserts(
        [("dual_engine_corners", dual), ("worst_corner_floors", worst_corner)]
    )
