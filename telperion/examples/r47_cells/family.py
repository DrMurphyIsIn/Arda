"""The R47 case study: the Brualdi-Goldwasser campaign's 36-cell unified
topped-up merge table, encoded through Telperion's public API.

This is the family that motivated the tool.  Grid: donor load cb in 0..5
(k = 5 - cb borrows), absorber load cA in 0..5.  Continuous symbols (u, v) are
the degree offsets (topped-up: db = k+1+v, da = db+u; direct cb=5: db = 2+v).
The claim per cell: the merged (after) hub-pair amplitude dominates the
unmerged (before) one on the certified sigma-box, under the environment cap
3/16 — with the direct row floored at sr >= 3/23.

Problem-specific constants (from kelmans_unified_merge.py): Wt = 76/115 the
topped-arm weight, V5 = 621/64 the 5-cherry hub value, z15 = 3/23 and
z14 = 3/19 the loaded-arm activities, cap = 3/16.

The origin repository ships its own hand-tooled generator
(proof/verification/gen_r47cert_cells.py) whose emitted Lean — spelled in the
campaign's domain atoms Fw/zw — is CI-green there; see PROVENANCE.md.  This
encoding re-certifies the same 36 cells through the generic pipeline and
freezes Telperion's own rendering for the regeneration-diff protocol.
"""
from __future__ import annotations

import sympy as sp

from telperion import BoxAxis, GridSpec, InequalityFamily, LeanProfile

u, v = sp.symbols("u v", nonnegative=True)
sQ, sr = sp.symbols("sQ sr", nonnegative=True)

CAP = sp.Rational(3, 16)
Z15, Z14 = sp.Rational(3, 23), sp.Rational(3, 19)
WT, V5 = sp.Rational(76, 115), sp.Rational(621, 64)


def Fs(deg, c: int):
    """The loaded-hub factor F(deg, c)."""
    if c == 0:
        return sp.Integer(1)
    D_ = deg + c
    return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D_) * sp.Rational(3, 2) ** (c - 1)


def zs(deg, c: int):
    """The activity z(deg, c) = 3/(3 deg + 4 c)."""
    return sp.Integer(3) / (3 * deg + 4 * c)


def _degrees(pt):
    cb = pt["cb"]
    k = 5 - cb
    db = (2 + v) if cb == 5 else (k + 1 + v)
    da = db + u
    dap = da + db - 1
    return k, da, db, dap


def before(pt):
    cA, cb = pt["cA"], pt["cb"]
    k, da, db, _ = _degrees(pt)
    Fa, Fb = Fs(da, cA), Fs(db, cb)
    za, zb = zs(da, cA), zs(db, cb)
    return Fa * Fb * ((1 + za * sQ) * (1 + zb * (k * Z15 + sr)) + za * zb)


def after(pt):
    cA = pt["cA"]
    k, da, db, dap = _degrees(pt)
    Fap = Fs(dap, cA)
    zap = zs(dap, cA)
    return WT**k * Fap * V5 * (1 + zap * (sQ + k * Z14 + sr + Z15))


def box(pt):
    cb = pt["cb"]
    _, da, db, _ = _degrees(pt)
    q_axis = BoxAxis(sQ, sp.Integer(0), (da - 1) * CAP)
    if cb == 5:
        r_axis = BoxAxis(sr, Z15, (db - 1) * CAP, lo_is_floor=True)
    else:
        r_axis = BoxAxis(sr, sp.Integer(0), v * CAP)
    return (q_axis, r_axis)


def cell_name(pt) -> str:
    cA, cb = pt["cA"], pt["cb"]
    return f"tel_dA{cA}" if cb == 5 else f"tel_dT{cA}{cb}"


def r47_family() -> InequalityFamily:
    return InequalityFamily(
        name="R47Cells",
        symbols=(u, v),
        grid=GridSpec([("cb", [5, 4, 3, 2, 1, 0]), ("cA", [0, 1, 2, 3, 4, 5])]),
        lean_name=cell_name,
        constants={"WT": WT, "V5": V5, "Z15": Z15, "Z14": Z14, "CAP": CAP},
        before=before,
        after=after,
        box=box,
    )


def r47_profile() -> LeanProfile:
    # The corner combinator, verbatim from the origin's CI-green R47Cert.lean.
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
    return LeanProfile(
        namespace=("R47Tel",),
        prelude=prelude,
        options=("set_option maxHeartbeats 4000000",),
    )
