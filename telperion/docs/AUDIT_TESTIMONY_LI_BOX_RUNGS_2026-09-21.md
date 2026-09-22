The artifact is Li's first five coefficients (rungs 0..4) shown nonnegative with no hypothesis, via a polynomial pair term on the disk cut out by Box 2; five finite inequalities; NOT a proof of anything about RH (Li's criterion needs every rung).

# Audit testimony: LiBoxRungs (li_positivity island)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-21. Branch mm/li-face.
Island: telperion/examples/li_positivity/lean, Lean v4.34.0-rc1, upstream LiCriterion rev 35df682f.
File: LiBoxRungs.lean (302 lines, namespace LowHeightBox, 30 declarations incl. 6 defs).
LowHeightBox.lean re-read at 310 lines (17 declarations, unchanged from my earlier audit of the
310-line version; `riemannZeta_ne_zero_of_unit_interval` present).
Probes: Probes/AuditLiBox_Axioms.lean, Probes/AuditLiBox_Probes.lean. conjecture1_proved = False.

## 1. Verdict

PASS. One sentence: the pair term at rung n is the Chebyshev-type polynomial Q_{n+1}(z) in
z = 1/(ρ(1-ρ)), Box 2 puts z in the closed disk |z - 1/2| <= 1/2, and the three explicit
nonnegative certificates for Q_3, Q_4, Q_5 (with Q_1, Q_2 immediate) are correct polynomial
identities, so rungs 0..4 are hypothesis-free and the registry node RH_li_rungs_lt_five is
proved with a byte-identical statement.

## 2. Kernel evidence (my runs)

Probes/AuditLiBox_Axioms.lean: 34/34 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(30 LiBoxRungs declarations, plus zeta_zero_confined, weighted_paired_sum_formula_of_standard_hypotheses,
xi_hasFiniteOrder, xi_order_le_one). Verbatim:

    'LowHeightBox.li_rungs_lt_five' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option)
on LiBoxRungs.lean and LowHeightBox.lean: nothing. Built .olean exists; only my probes were built.

## 3. Registry byte comparison

missions/rh/lean/Statements/RH_li_rungs_lt_five.lean:
`theorem li_rungs_lt_five : ∀ n : ℕ, n < 5 → 0 ≤ (taylorCoeff riemannXi n).re := by sorry`
(under `open LiCriterion`). Artifact line 299: byte-IDENTICAL statement, no hypothesis. Node toml
status "draft", closure_clean false (awaits grant). Also checked while here: RH_li_ladder_height
and RH_li_rungs_of_height_4000 are byte-identical to LiLadderHeight's
`li_rung_of_zeros_on_line_below` and `li_rungs_of_bands_4000_upto` (both marked proved).

## 4. Mathematics re-derived

(a) Pair term. With w = ρ/(ρ-1) and v = 1/w = (ρ-1)/ρ: liSummand n ρ = 1 - (1-1/ρ)^{-(n+1)}
= 1 - w^{n+1}·… precisely, 1 - 1/ρ = v so liSummand n ρ = 1 - v^{-N} = 1 - w^N, and
1 - 1/(1-ρ) = w so liSummand n (1-ρ) = 1 - w^{-N} = 1 - v^N. Sum 2 - w^N - v^N
(`liPairedSummand_eq_pow`). Checked.
(b) z = 1/(ρ(1-ρ)) = 2 - w - v: 2 - ρ/(ρ-1) - (ρ-1)/ρ = [2ρ(ρ-1) - ρ² - (ρ-1)²]/(ρ(ρ-1))
= -1/(ρ(ρ-1)) = 1/(ρ(1-ρ)) (`zOf_eq`). Checked. So w + v = 2 - z and wv = 1.
(c) Polynomials. p_N = w^N + v^N satisfies p_{N+1} = (2-z) p_N - p_{N-1}, p_0 = 2, p_1 = 2-z;
Q_N = 2 - p_N. I recomputed by sympy: Q_1 = z, Q_2 = 4z - z², Q_3 = 9z - 6z² + z³,
Q_4 = 16z - 20z² + 8z³ - z⁴, Q_5 = 25z - 50z² + 35z³ - 10z⁴ + z⁵, all matching the file, and
Q_6 = 36z - 105z² + 112z³ - 54z⁴ + 12z⁵ - z⁶. Chebyshev form Q_N(2 - 2cos t) = 2 - 2cos(Nt)
verified (symbolically for N <= 4, numerically to 3e-12 for N = 5, 6). The file's
`linear_combination` multipliers (2, 3v+3w, 4v²+6vw+4w²-2, 5v³+10v²w+10vw²-5v+5w³-5w) times
(wv - 1) are the right corrections; the kernel accepted them.
(d) Box 2 to the disk. Box 2: (β-1/2)² <= γ²/3 - 1/4, i.e. γ² >= 3(β-1/2)² + 3/4. Then
Re(ρ(1-ρ)) - 1 = β(1-β) + γ² - 1 >= 3(β-1/2)² + 3/4 - (β-1/2)² - 3/4 = 2(β-1/2)² >= 0
(`re_mul_one_sub_ge_one`; re-proved abstractly in my probe 2). For z = 1/q:
Re z - |z|² = (Re q - 1)/|q|² >= 0, i.e. (Re z)² + (Im z)² <= Re z (`zOf_mem_disk`; probe 3).
Checked.
(e) Certificates, with a = Re z, b = Im z, d = a - (a²+b²) >= 0 on the disk, s = a²+b², B = b²:
- Re Q_1 = a >= a² + b² >= 0. Re Q_2 = 4a - a² + b² = 3a + 2b² + d >= 0.
- Re Q_3 = a³ - 6a² - 3ab² + 9a + 6b² = 15B + 4d³ + 12d²s + 3d² + 12ds² + 3ds + 9d + 4s³:
  verified symbolically (sympy expand of both sides equal).
- 14 s · Re Q_4 = 433B² + 112Bd²s + 438Bd² + 224Bds² + 408Bds + 44Bd + 112Bs³ + 44Bs + 5d⁴
  + 44d³ + 20ds³ + 180ds + 15s⁴ + 27s²: verified symbolically. The s = 0 case (z = 0) is handled
  separately in the file (P = 0 there). Checked.
- s² · Re Q_5 = 68B³ + 72B²d² + 16B²ds² + 128B²ds + 16B²s³ + 4B²s + 4Bd⁴ + 70Bd²s + 4Bds³
  + 11Bds² + 14Bds + 3Bs² + 2d⁴s + 3d³s² + 14d³s + d²s² + 11ds² + s⁵: verified symbolically;
  s = 0 handled. Checked.
All coefficients nonnegative, so `positivity` closes each. The file's stated real-part expansions
of Q_3, Q_4, Q_5 also match sympy.
(f) Numerical minimisation of Re Q_N over the closed disk (801 radii x 720 angles):
N = 1..5 minimum 0 at z = 0 (the boundary point where d = s = 0); N = 6 minimum -1.837 at
z = 0.765 + 0.424i; N = 7 minimum -6.99. So the disk method stops at N = 5 exactly as the file
says. My probe 4 proves in Lean that z = 29/39 + (17/39)i lies in the disk and Re Q_6(z) < 0.
(g) Tsum step. `taylorCoeff_re_nonneg_of_termwise` passes Re through the tsum by cases on
summability (non-summable tsum is 0, Re 0 = 0); m(ρ) is a natural number. Sound either way.
(h) The first zero has z = 0.0049990 with Re z - |z|² = 0.004974 > 0, consistent.

## 5. Probes (Probes/AuditLiBox_Probes.lean)

Expected successes, all elaborated: rung 3 re-composed from the pieces (1); Box 2 to Re q >= 1
(2); Re q >= 1 to the disk (3); Q_6 negative at a rational disk point (4); consumption at rung 4
(5); Q_5(1) = 1 (6). Expected failures, each at the intended point:

    Probes/AuditLiBox_Probes.lean:42:66: error: unsolved goals   -- li_rungs_lt_five at n = 5
    Probes/AuditLiBox_Probes.lean:46:31: error: unsolved goals   -- termwise lemma at n = 5

## 6. Overclaim grep

LiBoxRungs.lean lines 28-29: "Nothing here proves, or bears on, whether RH holds: Li's criterion
needs ALL rungs; these are the first five. conjecture1_proved = False." No other RH language.

## 7. What this does and does not establish

Established, hypothesis-free: 0 <= Re(taylorCoeff riemannXi n) for n = 0..4 (Li's λ₁..λ₅) in the
upstream vocabulary, with the Arb enclosure hypotheses of the emitted rung certificates no longer
needed for these five. Not new knowledge about the coefficients (they are known positive
numerically); kernel novelty only. Rung 5 and beyond need height (LiLadderHeight). NOT a proof of
anything about RH. conjecture1_proved = False.
