"""The toy example: a 4-cell bilinear box family plus a 3-instance direct family.

The bilinear family is a miniature of the R47 merge-cell structure: for grid
parameters (a, b) and nonnegative reals (u, v), with activities
za = a/(a+u+1), zb = b/(b+v+1) and gain delta = 1/((a+u+1)(b+v+1)),

    before = (1 + za*q) * (1 + zb*r)
    after  = 1 + delta + (za/2)*q + (zb/2)*r + 2*za*zb*(q*r)

so after - before = delta - (za/2) q - (zb/2) r + za*zb (q r): a bilinear form
with positive constant, negative slopes, positive interaction — nonnegative on
the box q in [0, 1/(a(b+v+1))], r in [0, 1/(b(a+u+1))] by four Polya corner
certificates (corners: delta, delta/2, delta/2, za*zb*QR — all manifestly
nonneg/positive-den).  Emitted Lean discharges the corners by `positivity`
and assembles the box via `bilinear_corner_nonneg` (in the profile prelude).
"""
from __future__ import annotations

import sympy as sp

from telperion import (
    BoxAxis,
    GridSpec,
    InequalityFamily,
    LeanProfile,
)

u, v = sp.symbols("u v", nonnegative=True)
q, r = sp.symbols("q r", nonnegative=True)

COMBINATOR_PRELUDE = """/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it.
    (Verbatim from the R47 campaign's CI-green `R47Cert.lean`.) -/
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


def _za(a):
    return sp.Rational(a) / (a + u + 1)


def _zb(b):
    return sp.Rational(b) / (b + v + 1)


def _delta(a, b):
    return sp.Integer(1) / ((a + u + 1) * (b + v + 1))


def box_family() -> InequalityFamily:
    def before(pt):
        return (1 + _za(pt["a"]) * q) * (1 + _zb(pt["b"]) * r)

    def after(pt):
        a, b = pt["a"], pt["b"]
        return (
            1
            + _delta(a, b)
            + (_za(a) / 2) * q
            + (_zb(b) / 2) * r
            + 2 * _za(a) * _zb(b) * (q * r)
        )

    def box(pt):
        a, b = pt["a"], pt["b"]
        return (
            BoxAxis(q, sp.Integer(0), sp.Integer(1) / (a * (b + v + 1))),
            BoxAxis(r, sp.Integer(0), sp.Integer(1) / (b * (a + u + 1))),
        )

    return InequalityFamily(
        name="ToyBox",
        symbols=(u, v),
        grid=GridSpec([("a", [1, 2]), ("b", [1, 2])]),
        lean_name=lambda pt: f"toy_a{pt['a']}b{pt['b']}",
        before=before,
        after=after,
        box=box,
    )


def direct_family() -> InequalityFamily:
    return InequalityFamily(
        name="ToyDirect",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"toy_direct_a{pt['a']}",
        target=lambda pt: (pt["a"] + u) / (u + 1) - sp.Rational(pt["a"]) / (u + 2),
    )


def box_profile() -> LeanProfile:
    return LeanProfile(
        namespace=("Toy",),
        prelude=COMBINATOR_PRELUDE,
        options=("set_option maxHeartbeats 1600000",),
    )


def direct_profile() -> LeanProfile:
    return LeanProfile(namespace=("Toy",))
