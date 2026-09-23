#!/usr/bin/env python3
"""height_floor_boxes.py -- emitter for lean/HeightFloorBoxes.lean (brick H3, AND_height_floor_kernel).

Emits the finite box cover certifying |G2(s)| > 1/4 on 1/2 <= Re s <= 1, 0 <= Im s <= 55/16, where
G2(s) = (s - 1) + 2^(-s) (s^2 + 11 s + 36) / 24 (HeightFloorEM).  Everything the emitted file asserts is
re-checked by Lean; this script only CHOOSES the numbers:

  * trig table: for t_j = 55 j / 256 (j = 0..16) a rational Taylor point q_j ~ t_j log 2, the Lipschitz
    radius eps_j with t_j * 0.6931471803 - ... <= eps_j (Mathlib's 9-digit log 2 bracket), and dyadic
    brackets (scale 2^-32) of cosT/sinT(q_j, 7) -/+ (Taylor remainder + eps_j).  Exact Fraction arithmetic,
    rounded outward; Lean re-verifies each bracket with norm_num.
  * power table: 2^(-1/2), 2^(-3/4) bracketed at scale 2^-32 by integer power checks.
  * boxes: 2 sigma slabs x 16 height slabs; each box's DI inputs; a Python mirror of DI.evalAB /
    DI.checkAB (exact integers) confirms every box passes before emission; Lean re-runs the check by
    `decide`.

Nothing here is trusted: a wrong number makes the Lean build fail.  mpmath is used only to pick q_j and
for sanity asserts.  conjecture1_proved = False.

Usage: python3 height_floor_boxes.py [out.lean]   (default: lean/HeightFloorBoxes.lean next to this file)
"""
import os
import sys
from fractions import Fraction as Fr
from math import factorial, floor, ceil

import mpmath

mpmath.mp.dps = 50

P = 32                      # dyadic scale of all table brackets
NT = 16                     # height slabs
T = Fr(55, 16)              # top height
NTAY = 7                    # Taylor terms (remainder |q|^14/14! * 2)
LOG2_LO = Fr(6931471803, 10**10)   # Real.log_two_gt_d9
LOG2_HI = Fr(6931471808, 10**10)   # Real.log_two_lt_d9
SIGMA_SLABS = [(Fr(1, 2), Fr(3, 4)), (Fr(3, 4), Fr(1))]


def cosT(q, n):
    return sum(Fr((-1) ** k) * q ** (2 * k) / factorial(2 * k) for k in range(n))


def sinT(q, n):
    return sum(Fr((-1) ** k) * q ** (2 * k + 1) / factorial(2 * k + 1) for k in range(n))


def rem(q, n):
    return abs(q) ** (2 * n) / factorial(2 * n) * 2


def t_(j):
    return T * j / NT


def lit(x):
    """Lean real literal for a Fraction."""
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d/%d : ℝ)" % (x.numerator, x.denominator)


def qlit(x):
    x = Fr(x)
    if x.denominator == 1:
        return "%d" % x.numerator
    return "%d/%d" % (x.numerator, x.denominator)


# ------------------------------------------------------------------------------------------ tables
rows = []
for j in range(NT + 1):
    t = t_(j)
    th = mpmath.mpf(t.numerator) / t.denominator * mpmath.log(2)
    q = Fr(int(mpmath.nint(th * 10**7)), 10**7)
    d1 = t * LOG2_HI - q
    d2 = q - t * LOG2_LO
    eps = Fr(ceil(max(d1, d2, Fr(0)) * 10**9), 10**9)
    assert d1 <= eps and d2 <= eps and eps >= 0
    assert abs(q) / (2 * NTAY + 1) <= Fr(1, 2)
    R = rem(q, NTAY)
    c, s = cosT(q, NTAY), sinT(q, NTAY)
    cLo, cHi = floor((c - R - eps) * 2**P), ceil((c + R + eps) * 2**P)
    sLo, sHi = floor((s - R - eps) * 2**P), ceil((s + R + eps) * 2**P)
    assert Fr(cLo, 2**P) <= Fr(str(mpmath.cos(th))) <= Fr(cHi, 2**P)
    assert Fr(sLo, 2**P) <= Fr(str(mpmath.sin(th))) <= Fr(sHi, 2**P)
    rows.append(dict(j=j, t=t, q=q, eps=eps, cLo=cLo, cHi=cHi, sLo=sLo, sHi=sHi, th=th))


def root_bounds(p, qd):
    """lo, hi with lo^qd * 2^p <= 2^(P qd) <= hi^qd * 2^p, i.e. lo/2^P <= 2^(-p/qd) <= hi/2^P."""
    x = mpmath.mpf(2) ** (-mpmath.mpf(p) / qd)
    lo = int(mpmath.floor(x * 2**P))
    hi = lo + 1
    assert lo ** qd * 2**p <= 2 ** (P * qd) <= hi ** qd * 2**p
    return lo, hi


M12 = root_bounds(1, 2)
M34 = root_bounds(3, 4)

# regimes of sin on [theta_j, theta_{j+1}]: 'low' (<= pi/2), 'mid' (straddles), 'high' (>= pi/2)
PI_LO, PI_HI = Fr(3141592, 10**6), Fr(3141593, 10**6)   # Real.pi_gt_d6, Real.pi_lt_d6


def regime(j):
    a, b = t_(j), t_(j + 1)
    if b * LOG2_HI <= PI_LO / 2:
        return "low"
    if PI_HI / 2 <= a * LOG2_LO:
        return "high"
    return "mid"


# ------------------------------------------------------------------------------------ DI mirror
class DI:
    def __init__(self, lo, hi, e):
        self.lo, self.hi, self.e = lo, hi, e

    def add(I, J):
        E = max(I.e, J.e)
        return DI(I.lo * 2 ** (E - I.e) + J.lo * 2 ** (E - J.e),
                  I.hi * 2 ** (E - I.e) + J.hi * 2 ** (E - J.e), E)

    def neg(I):
        return DI(-I.hi, -I.lo, I.e)

    def mul(I, J):
        c = [I.lo * J.lo, I.lo * J.hi, I.hi * J.lo, I.hi * J.hi]
        return DI(min(c), max(c), I.e + J.e)

    def gap(I):
        return max(I.lo, -I.hi, 0)


def ofInt(z):
    return DI(z, z, 0)


def evalAB(Is, It, Im, IC, IS):
    sq, tq = Is.mul(Is), It.mul(It)
    Pr = sq.add(tq.neg()).add(ofInt(11).mul(Is)).add(ofInt(36))
    Pi = It.mul(ofInt(2).mul(Is).add(ofInt(11)))
    X = IC.mul(Pr).add(IS.mul(Pi))
    Y = IC.mul(Pi).add(IS.mul(Pr).neg())
    return (ofInt(24).mul(Is.add(ofInt(-1))).add(Im.mul(X)),
            ofInt(24).mul(It).add(Im.mul(Y)))


def checkAB(A, B):
    return 36 * 2 ** (2 * A.e) * 2 ** (2 * B.e) < \
        A.gap() * A.gap() * 2 ** (2 * B.e) + B.gap() * B.gap() * 2 ** (2 * A.e)


def box_inputs(i, j):
    s1, s2 = SIGMA_SLABS[i]
    Is = DI(int(s1 * 4), int(s2 * 4), 2)
    It = DI(55 * j, 55 * (j + 1), 8)
    Im = DI(M34[0], M12[1], P) if i == 0 else DI(2 ** (P - 1), M34[1], P)
    r0, r1 = rows[j], rows[j + 1]
    IC = DI(r1["cLo"], r0["cHi"], P)
    reg = regime(j)
    if reg == "low":
        IS = DI(r0["sLo"], r1["sHi"], P)
    elif reg == "high":
        IS = DI(r1["sLo"], r0["sHi"], P)
    else:
        IS = DI(min(r0["sLo"], r1["sLo"]), 2 ** P, P)
    return Is, It, Im, IC, IS, reg


worst = None
for i in range(2):
    for j in range(NT):
        Is, It, Im, IC, IS, reg = box_inputs(i, j)
        A, B = evalAB(Is, It, Im, IC, IS)
        assert checkAB(A, B), (i, j)
        lb = float((Fr(A.gap(), 2 ** A.e) ** 2 + Fr(B.gap(), 2 ** B.e) ** 2) ** 0.5) / 24
        if worst is None or lb < worst[0]:
            worst = (lb, i, j)

# ------------------------------------------------------------------------------------------- emit
def di(I):
    return "⟨%d, %d, %d⟩" % (I.lo, I.hi, I.e)


out = []
w = out.append
w("""/-  HeightFloorBoxes.lean -- brick H3 (AND_height_floor_kernel), part 4: the box cover.

    GENERATED by ../height_floor_boxes.py; DO NOT EDIT BY HAND.  Every number below is re-checked
    here: the trig brackets by `norm_num` against the Taylor bracket `HeightFloor.trig_encl`, the
    `2^(-σ)` brackets by `norm_num` power checks, and each of the %d boxes by `decide` on the exact
    dyadic evaluator `HeightFloor.DI.checkAB` (whose soundness is `HeightFloor.DI.box_sound`).

    Cover: σ ∈ [1/2, 3/4] ∪ [3/4, 1],  t ∈ [55 j/256, 55 (j+1)/256], j = 0..%d.
    Emitter's own mirror of the checker: worst certified lower bound on |G2| over the boxes is
    %.4f (box σ-slab %d, t-slab %d); the threshold is 1/4 and the proved tail is at most 23/100.

    Headline: `G2_norm_gt : 1/2 ≤ σ → σ ≤ 1 → 0 ≤ t → t ≤ 55/16 → 1/4 < ‖G2 (σ + t i)‖`.

    conjecture1_proved = False.  Finite interval arithmetic at low height; nothing here is about RH.
-/
import HeightFloorCheck
import HeightFloorTrig
import HeightFloorEM

open Complex

namespace HeightFloor.Boxes

open HeightFloor
""" % (2 * NT, NT - 1, worst[0], worst[1], worst[2]))

# trig table
w("/-! ### cos / sin at the slab heights `t_j log 2` (dyadic brackets, scale `2^-32`) -/\n")
for r in rows:
    j, t, q, eps = r["j"], r["t"], r["q"], r["eps"]
    tl = lit(t)
    w("theorem trig_%d :" % j)
    w("    ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ Real.cos (%s * Real.log 2) ∧" % (r["cLo"], tl))
    w("    Real.cos (%s * Real.log 2) ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 ∧" % (tl, r["cHi"]))
    w("    ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ Real.sin (%s * Real.log 2) ∧" % (r["sLo"], tl))
    w("    Real.sin (%s * Real.log 2) ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 := by" % (tl, r["sHi"]))
    w("  have hθ : |%s * Real.log 2 - %s| ≤ %s :=" % (tl, lit(q), lit(eps)))
    w("    abs_mul_log_two_sub_le (by norm_num) (by norm_num) (by norm_num)")
    w("  obtain ⟨h1, h2, h3, h4⟩ := trig_encl _ _ _ %d hθ (by norm_num)" % NTAY)
    rr = "|%s| ^ (2 * %d) / ((2 * %d).factorial : ℝ) * 2" % (lit(q), NTAY, NTAY)
    w("  have e1 : ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ cosT %s %d - %s - %s := by" % (r["cLo"], lit(q), NTAY, rr, lit(eps)))
    w("    norm_num [cosT, Finset.sum_range_succ, Nat.factorial]")
    w("  have e2 : cosT %s %d + %s + %s ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 := by" % (lit(q), NTAY, rr, lit(eps), r["cHi"]))
    w("    norm_num [cosT, Finset.sum_range_succ, Nat.factorial]")
    w("  have e3 : ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ sinT %s %d - %s - %s := by" % (r["sLo"], lit(q), NTAY, rr, lit(eps)))
    w("    norm_num [sinT, Finset.sum_range_succ, Nat.factorial]")
    w("  have e4 : sinT %s %d + %s + %s ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 := by" % (lit(q), NTAY, rr, lit(eps), r["sHi"]))
    w("    norm_num [sinT, Finset.sum_range_succ, Nat.factorial]")
    w("  exact ⟨le_trans e1 h1, le_trans h2 e2, le_trans e3 h3, le_trans h4 e4⟩\n")

# power table
w("/-! ### `2^(-σ)` at the slab ends -/\n")
w("theorem m12_hi : (2 : ℝ) ^ (-(1/2 : ℝ)) ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 := by" % M12[1])
w("  have h := two_rpow_neg_le (p := 1) (q := 2) (x := ((%d : ℤ) : ℝ) / 2 ^ 32) (by norm_num)" % M12[1])
w("    (by norm_num) (by rw [two_rpow_neg_nat]; norm_num)")
w("  have e : (-((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = -(1/2 : ℝ) := by norm_num")
w("  rwa [e] at h\n")
w("theorem m34_lo : ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ (2 : ℝ) ^ (-(3/4 : ℝ)) := by" % M34[0])
w("  have h := le_two_rpow_neg (p := 3) (q := 4) (x := ((%d : ℤ) : ℝ) / 2 ^ 32) (by norm_num)" % M34[0])
w("    (by norm_num) (by rw [two_rpow_neg_nat]; norm_num)")
w("  have e : (-((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = -(3/4 : ℝ) := by norm_num")
w("  rwa [e] at h\n")
w("theorem m34_hi : (2 : ℝ) ^ (-(3/4 : ℝ)) ≤ ((%d : ℤ) : ℝ) / 2 ^ 32 := by" % M34[1])
w("  have h := two_rpow_neg_le (p := 3) (q := 4) (x := ((%d : ℤ) : ℝ) / 2 ^ 32) (by norm_num)" % M34[1])
w("    (by norm_num) (by rw [two_rpow_neg_nat]; norm_num)")
w("  have e : (-((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = -(3/4 : ℝ) := by norm_num")
w("  rwa [e] at h\n")
w("theorem m1_lo : ((%d : ℤ) : ℝ) / 2 ^ 32 ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by" % (2 ** (P - 1)))
w("  rw [Real.rpow_neg_one]; norm_num\n")

# boxes
w("/-! ### The %d boxes (each: `decide` on the exact dyadic evaluator) -/\n" % (2 * NT))
mlo_hi = {0: ("m34_lo", "m12_hi"), 1: ("m1_lo", "m34_hi")}
for i in range(2):
    s1, s2 = SIGMA_SLABS[i]
    for j in range(NT):
        Is, It, Im, IC, IS, reg = box_inputs(i, j)
        a, b = t_(j), t_(j + 1)
        w("theorem box_%d_%d (σ t : ℝ) (h1 : %s ≤ σ) (h2 : σ ≤ %s) (h3 : %s ≤ t) (h4 : t ≤ %s) :"
          % (i, j, lit(s1), lit(s2), lit(a), lit(b)))
        w("    1 / 4 < ‖G2 ((σ : ℂ) + (t : ℂ) * I)‖ :=")
        w("  G2_norm_gt_of_AB (DI.box_sound")
        w("    (Iσ := %s) (It := %s)" % (di(Is), di(It)))
        w("    (Im := %s)" % di(Im))
        w("    (IC := %s)" % di(IC))
        w("    (IS := %s)" % di(IS))
        w("    (DI.mem_mk (by norm_num; linarith) (by norm_num; linarith))")
        w("    (DI.mem_mk (by norm_num; linarith) (by norm_num; linarith))")
        w("    (mem_m h1 h2 %s %s)" % mlo_hi[i])
        w("    (mem_cos (by norm_num) h3 h4 (by norm_num) trig_%d.1 trig_%d.2.1)" % (j + 1, j))
        if reg == "low":
            w("    (mem_sin_low (by norm_num) h3 h4 (by norm_num) trig_%d.2.2.1 trig_%d.2.2.2)" % (j, j + 1))
        elif reg == "high":
            w("    (mem_sin_high (by norm_num) h3 h4 (by norm_num) trig_%d.2.2.1 trig_%d.2.2.2)" % (j + 1, j))
        else:
            w("    (mem_sin_mid (by norm_num) h3 h4 (by norm_num)")
            w("      (le_trans (by norm_num) trig_%d.2.2.1) (le_trans (by norm_num) trig_%d.2.2.1))" % (j, j + 1))
        w("    (by decide))\n")

# cover
w("/-! ### The cover -/\n")
for i in range(2):
    s1, s2 = SIGMA_SLABS[i]
    w("theorem slab_%d (σ t : ℝ) (h1 : %s ≤ σ) (h2 : σ ≤ %s) (h3 : 0 ≤ t) (h4 : t ≤ 55 / 16) :"
      % (i, lit(s1), lit(s2)))
    w("    1 / 4 < ‖G2 ((σ : ℂ) + (t : ℂ) * I)‖ := by")
    for j in range(NT - 1):
        b = t_(j + 1)
        lo_h = "h3" if j == 0 else "hb%d" % (j - 1)
        w("  rcases le_total t %s with ha%d | hb%d" % (lit(b), j, j))
        w("  · exact box_%d_%d σ t h1 h2 %s ha%d" % (i, j, lo_h, j))
    w("  exact box_%d_%d σ t h1 h2 hb%d (by linarith)\n" % (i, NT - 1, NT - 2))

w("""/-- **The certified floor of the main part.**  On `1/2 ≤ σ ≤ 1`, `0 ≤ t ≤ 55/16`,
    `‖G2 (σ + t i)‖ > 1/4`. -/
theorem G2_norm_gt (σ t : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) (h3 : 0 ≤ t) (h4 : t ≤ 55 / 16) :
    1 / 4 < ‖G2 ((σ : ℂ) + (t : ℂ) * I)‖ := by
  rcases le_total σ (3 / 4) with hσ | hσ
  · exact slab_0 σ t h1 hσ h3 h4
  · exact slab_1 σ t hσ h2 h3 h4

end HeightFloor.Boxes
""")

here = os.path.dirname(os.path.abspath(__file__))
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "lean", "HeightFloorBoxes.lean")
with open(path, "w") as f:
    f.write("\n".join(out))
print("wrote", path, "; worst certified |G2| lower bound %.4f at box %s" % (worst[0], worst[1:]))
