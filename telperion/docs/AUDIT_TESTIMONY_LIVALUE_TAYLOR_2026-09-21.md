# Audit testimony: E6Bridge19, LiValue by Taylor bookkeeping, 2026-09-21

THE BOMBIERI-LAGARIAS VALUE IDENTITY MODULO THE DERIVATIVE PARTIAL FRACTION OF ξ AND THE ABSENCE OF
A REAL ZERO IN (0, 1). NOT A PROOF OF ANYTHING ABOUT THE RIEMANN HYPOTHESIS. E6Bridge19 proves
`LiValue n` (0 < n), hence the rh node RH_bl_explicit_formula through E6Bridge15's convergence
half, from two `def : Prop` hypotheses: `RvMBridge18.XiLogDerivDerivEq` (the derivative partial
fraction, itself reduced by E6Bridge20/21/22 to `LocalCountSum` and `StripDerivBound`) and
`NoRealZeroInUnitInterval`. Nothing is concluded about where the zeros are.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge19.lean (1594 lines at audit time,
namespace RvMBridge19, imports E6Bridge15, E6Bridge20, E6Bridge21 and three Zeta23 files); memo
LIVALUE_TAYLOR_2026-09-21.md; the author's composition probe Probes/E6Bridge22_taylor_probe.lean.
Probes: Probes/Audit19_Axioms.lean, Probes/Audit19_Probes.lean, plus mpmath. No git state
changed; no other file edited.

Overall verdict: PASS. No defect found in the artifact. The Λ-form correction is right with the
pole terms carrying the product-rule signs; the power-sum expansion's radius, the paired first
power sum via the FTC and the reflection fold, the closed forms at s = 1, and the finite-sum
assembly all re-derive and reproduce Li's λ_n numerically to ~1e-30. One finding, not a defect of
the artifact: the author's composition probe is stale (it references `RvMBridge19.xi` and
`RvMBridge19.XiDerivPartialFraction`, which the current file no longer defines), so it fails and
its theorems carry sorryAx; I replaced it by my own axiom-clean composition.

## 1. Kernel: PASS

`lake build` (full): `Build completed successfully (8869 jobs)` on the final run (one earlier run
during the audit reported a failure while newer modules E6Bridge23/25/26 were being added by
other agents; `lake build E6Bridge19` alone succeeded, 3749 jobs, and the full build was green
again). E6Bridge19 in defaultTargets (lakefile line 9); guard 127 RvMBridge19 lines.
Probes/Audit19_Axioms.lean prints axioms for all 147 mechanically extracted declarations: 147 of
147 read `[propext, Classical.choice, Quot.sound]`, no sorryAx. Token grep (excluding "partial
fraction"): only the header's backticked `sorry` mention (line 7) and the name
`bl_explicit_formula_of_partialFraction` (line 1394). Imported by E6Bridge25, the guard and two
probes. `#check liValue_of : XiLogDerivDerivEq → NoRealZeroInUnitInterval → ∀ n, 0 < n → LiValue n`;
`bl_explicit_formula_of_growth : XiDiffExtGrowthRight → NoRealZeroInUnitInterval → ∀ n, 0 < n →
Tendsto (liZeroSum n) atTop (𝓝 (archSide n + finiteSide n))`.

## 2. The Λ-form correction: PASS

`LambdaDerivPartialFraction : ∀ s, s ≠ 0 → s ≠ 1 → ¬IsNontrivialZero s → deriv (logDeriv Λ) s =
-Σ' m/(s-ρ)² + 1/s² + 1/(s-1)²` (line 84-86). Signs: ξ = (s(s-1)/2)·Λ off {0, 1}, so logDeriv ξ =
1/s + 1/(s-1) + logDeriv Λ and (logDeriv ξ)' = -1/s² - 1/(s-1)² + (logDeriv Λ)', i.e.
(logDeriv Λ)' = (logDeriv ξ)' + 1/s² + 1/(s-1)²: exactly `deriv_logDeriv_lambda_eq` (line 1452),
which my probe consumes (`audit_pole_signs`, axiom-clean). Forward `lambdaDerivPartialFraction_of_xi`
is that identity plus the ξ form. Converse `xiDerivPartialFraction_of_lambda`: off {0, 1} rewrite
back; at s = 0 (not a zero, ξ(0) = 1/2) both sides are continuous at 0 (deriv (logDeriv ξ) analytic
where ξ ≠ 0; the tsum side analytic on a ball around 0 free of zeros) and agree on the punctured
neighbourhood (`eq_of_continuousAt_of_eventually_ne`); at s = 1 by the symmetry s ↦ 1 - s
(`deriv_logDeriv_xi_one_sub`, `tsum_zero_series_one_sub` via `oneSubEquiv` and `zeroMult_one_sub`).
`xiDerivPartialFraction_iff` composes both (probe 3 consumes both directions). The brief's
`XiDerivPartialFraction` name is from an earlier revision; the current file states
`xiLogDerivDerivEq_def` (an `rfl` restatement of RvMBridge18.XiLogDerivDerivEq, probe 1) and uses
`XiLogDerivDerivEq` directly.

## 3. powerSum_eq_taylor: PASS

For |s| < |ρ|, 1/(s-ρ)² = ρ⁻²(1 - s/ρ)⁻² = Σ_k (k+1) s^k ρ^{-(k+2)}; the k-th derivative of
(s-ρ)⁻² at 0 is (-1)^k (k+1)!/(0-ρ)^{k+2} = (k+1)!/ρ^{k+2} (`coef k = (-1)^k (k+1)!`, `coef_succ`).
With (logDeriv ξ)' = -Σ m/(s-ρ)² on the ball (`deriv_logDeriv_xi_eventuallyEq hP`), termwise
differentiation (`iteratedDeriv_tsum_zterm` from the generic `iteratedDeriv_tsum_ball`, an
induction on k with a summable majorant u k for every derivative order on the ball, Weierstrass
M-test) gives iteratedDeriv k (logDeriv ξ)' 0 = -(k+1)! powerSum (k+2), i.e. (k+1) powerSum (k+2) =
-iteratedDeriv k ((logDeriv ξ)') 0 / k! (`powerSum_eq_taylor`, #check matches). Radius:
`exists_zero_radius` takes r = min(1, min ‖ρ‖ over the finitely many zeros with |Im ρ| < 1)
(`smallZeros_finite` from Zeta23's finite window), r > 0 since every nontrivial zero is nonzero;
zeros with |Im ρ| ≥ 1 have ‖ρ‖ ≥ |Im ρ| ≥ 1 ≥ r. So every nontrivial zero has ‖ρ‖ ≥ zeroRadius > 0
(probe 7 consumes `zeroRadius_le`, `zeroRadius_pos`), and the ball of radius zeroRadius around 0
is zero-free (`not_nontrivialZero_of_mem_ball`) with ‖s - ρ‖ ≥ ‖ρ‖/2 there (`norm_sub_ge_half`),
giving the majorant. `summable_powerSum (2 ≤ j)` and `powerSum_conj`/`powerSum_re` (the power
sums are real, by the conjugation reindexing of E6Bridge15).

## 4. The paired first power sum: PASS

`xi_ne_zero_on_segment (hR) : ξ(σ) ≠ 0` for real σ: by `xi_eq_zero_iff` a zero would be a
nontrivial zero with Im = 0 and 0 < σ < 1, excluded by hR (and ξ(0) = ξ(1) = 1/2 covers the
endpoints). Hence logDeriv ξ is differentiable on [0, 1] (`hasDerivAt_logDeriv_xi`) and the FTC
gives ∫₀¹ (logDeriv ξ)' = logDeriv ξ 1 - logDeriv ξ 0. Termwise: with zterm 0 ρ σ = m/(σ-ρ)²,
∫₀¹ m/(σ-ρ)² dσ = m[-1/(σ-ρ)]₀¹ = -(m/(1-ρ) + m/ρ) (`integral_zterm_zero`, needs Im ρ ≠ 0 for
nontrivial zeros under hR, `im_ne_zero_of_nontrivial`), so ∫₀¹ (logDeriv ξ)' = -Σ ∫ zterm = Σ (m/ρ +
m/(1-ρ)) (`tsum_inv_add_inv_one_sub`, the interchange by `hasSum_integral_zterm` with the segment
majorant `segBound` over the countable zero set and dominated convergence). Fold: refTerm ρ =
m(1/(1-ρ) - 1/conj ρ) satisfies refTerm(reflect ρ) = -refTerm ρ (reflect ρ = 1 - conj ρ,
`zeroMult_reflect`), so Σ refTerm = 0 by the reflection reindexing (`tsum_refTerm`); hence
Σ m/(1-ρ) = Σ m/conj ρ and Σ m(1/ρ + 1/(1-ρ)) = Σ m(1/ρ + 1/conj ρ) = 2 Σ m Re(1/ρ) =
2·pairedPowerSum 1. With logDeriv ξ 1 = -logDeriv ξ 0 (`logDeriv_xi_one_sub` at 0), pairedPowerSum 1
= -logDeriv ξ 0 (`pairedPowerSum_one_eq`, #check matches). Re-derived; correct.

## 5. The closed forms: PASS

`eta_eq : eta j = -(iteratedDeriv j (logDeriv ζ₁) 1)/j!` where Mathlib's riemannZeta₁ = (s-1)ζ(s)
is entire with ζ₁(1) = 1: RHDefs's zetaLogDerivReg = -ζ'/ζ - 1/(s-1) (extended by -γ at 1) equals
-logDeriv ζ₁ near 1 (`logDeriv_zeta_eq_near_one`: logDeriv ζ = -1/(s-1) + logDeriv ζ₁;
`zetaLogDerivReg_eventuallyEq`), consistent at 1 since ζ₁'(1) = γ. Sign checked: η₀ = -γ (mpmath
-0.5772156649, 1e-30). Digamma tower: from Zeta23's series ψ(z) = -γ - 1/z + Σ(1/n - 1/(n+z)),
ψ(s/2) = -γ - 2/s + dtail s near 1 (`psiHalf_eq`), and the (k+1)-st s-derivative at 1 is
-2(-1)^{k+1}(k+1)!(1 - 2^{-(k+2)}) ζ(k+2) (`iteratedDeriv_psiHalf`): by hand, ψ^{(m)}(z) =
(-1)^{m+1} m! Σ (n+z)^{-(m+1)}, the chain rule gives 2^{-m} ψ^{(m)}(1/2) = 2^{-m}(-1)^{m+1} m!
2^{m+1}(1 - 2^{-(m+1)}) ζ(m+1) = 2(-1)^{m+1} m! (1 - 2^{-(m+1)}) ζ(m+1), and m = k+1 gives the
stated form (odd-index sums via `tsum_odd_inv_pow`). mpmath: numeric (k+1)-st derivative vs
formula, |diff| ≤ 1.6e-30 for k = 0, 1, 2. `archCoeff_zero = -(log π)/2 - log 2 - γ/2` from ψ(1/2)
= -γ - 2 log 2 (Mathlib `digamma_one_half`; mpmath -1.9635100260). `archCoeff_succ k =
(-1)^{k+2}(1 - 2^{-(k+2)}) ζ(k+2)`. `taylorOne_eq k : taylorOne k = (-1)^k + archCoeff k - eta k`
from logDeriv ξ = 1/s + (-(log π)/2 + ψ(s/2)/2) + logDeriv ζ₁ near 1 (`logDeriv_xi_eq_closed`),
the 1/s Taylor coefficient (-1)^k (`iteratedDeriv_one_div`).

## 6. The assembly: PASS

`liKernel_re`/`liPaired_eq_sum`: Re(1 - (1 - 1/ρ)^n) = Σ_{m<n} (-1)^m C(n, m+1) Re(1/ρ^{m+1})
(binomial); `liLimit_eq_sum`: liLimit n = Σ_{m<n} (-1)^m C(n, m+1) pairedPowerSum (m+1) (finite sum
through the tsum, each summable). `pairedPowerSum_succ_eq hP hR` converts every paired power sum
to Taylor data at 0 (j ≥ 2 by `powerSum_eq_taylor` and realness, j = 1 by `pairedPowerSum_one_eq`),
and `taylorZero_eq k : taylorZero k = (-1)^{k+1} taylorOne k` moves the data from 0 to 1 by the
antisymmetry logDeriv ξ(s) = -logDeriv ξ(1 - s) (`iter_deriv_comp_add_const`), so
`liLimit_eq_taylorOne : liLimit n = Σ_{m<n} C(n, m+1) taylorOne m`. Then `taylorOne_eq` and the
three finite rearrangements: `sum_choose_alt` (Σ C(n, m+1)(-1)^m = 1 for n > 0, the alternating
binomial identity), `sum_choose_eta` (reindex to Σ_{j=1}^n C(n, j) eta (j-1) = -finiteSide),
`sum_choose_archCoeff` (= -(n/2)(γ + log π + 2 log 2) + Σ_{j=2}^n (-1)^j C(n,j)(1 - 2^{-j}) ζ(j),
the archSide minus its leading 1), giving `liValue_of : LiValue n` EXACTLY as RHDefs writes archSide
n + finiteSide n. By hand at n = 1: liLimit 1 = pairedPowerSum 1 = -logDeriv ξ 0 = logDeriv ξ 1 =
taylorOne 0 = 1 + archCoeff 0 - eta 0 = 1 - (log π)/2 - log 2 - γ/2 + γ = 1 + γ/2 - log(4π)/2 =
0.0230957089661...; archSide 1 + finiteSide 1 = [1 - (1/2)(γ + log π + 2 log 2)] + [-eta 0] =
the same. mpmath (Cauchy integrals on |s - 1| = 1/2, Re ξ > 0.49 on that circle so the principal
log is the analytic branch): archSide n + finiteSide n vs Li's λ_n = (1/(n-1)!) dⁿ/dsⁿ[s^{n-1} log
ξ(s)] at 1: n = 1: 0.023095708966121 (|diff| 1.0e-31); n = 2: 0.0923457352280467 (6.2e-31); n = 3:
0.207638920554325 (3.1e-30); n = 4: 0.368790479492242 (9.8e-30), matching the memo's table
(lines 155-160) digit for digit.

## 7. Obligation honesty and the composition: PASS

hP and hR are consumed only as hypotheses (#check of `liValue_of`, `bl_explicit_formula_of_growth`,
`liValue_of_lambda`). `NoRealZeroInUnitInterval` is not automation-closable (`Audit19_Probes.lean:
39:38: unsolved goals`; `40:38: unsolved goals` after aesop). LiValue does not follow from hR alone
(`43:66: don't know how to synthesize placeholder for argument hP`). The memo (lines 54-58) states hR
is used ONLY to integrate along [0, 1] and names the alternative path 0 → it → 1 + it → 1 avoiding
it, and (line 183-188) that XiLogDerivDerivEq rests on XiDiffExtGrowthRight via E6Bridge20/21 and
that hR is discharged in E6Bridge25 (not audited here). The COMPOSITION through E6Bridge22: my
`audit_liValue_of_two (h1 : LocalCountSum) (h2 : StripDerivBound) (hR) (n) (hn) : LiValue n :=
liValue_of (xiLogDerivDerivEq_of_two h1 h2) hR n hn` and `audit_bl_of_two` (the node) are
axiom-clean. FINDING (probe staleness, not an artifact defect): the author's
Probes/E6Bridge22_taylor_probe.lean references `RvMBridge19.xi` and
`RvMBridge19.XiDerivPartialFraction`, neither of which exists in the current file (which opens
`RvMBridge18.xi` and uses `XiLogDerivDerivEq`); running it gives `10:25: Unknown identifier
RvMBridge19.xi`, `13:4: Unknown identifier RvMBridge19.XiDerivPartialFraction`, and all three of
its theorems print `sorryAx`. The memo's line 185-188 "Registration: E6Bridge19 is not in
lakefile.toml defaultTargets nor in AxiomGuardRvMBridge" is also stale (it is in both now).
Recommend regenerating that probe and the memo's registration note.

## 8. Overclaim: PASS

Grep over E6Bridge19.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, LiValue proved, B7 proved/closed): the only
hits are the two disclaimers (file line 41 "conjecture1_proved = False. Nothing here says anything
about whether RH holds."; memo line 7 the same).

## Probe inventory

- Probes/Audit19_Axioms.lean: 147 axiom prints, 5 #check.
- Probes/Audit19_Probes.lean: `audit_liValue_of_two`, `audit_bl_of_two`, `audit_pole_signs`
  (axiom-clean); the rfl restatement, both directions of the Λ-form iff, the growth corollary at
  n = 3, the radius facts (all elaborate); 3 expected failures (two automation attempts on
  NoRealZeroInUnitInterval; LiValue from hR alone).
- mpmath (30 digits): η₀, η₁ by Cauchy integral; archSide + finiteSide vs Li's λ_n for n = 1..4;
  the digamma tower for k = 0, 1, 2; ψ(1/2).
- Probes/E6Bridge19_probe.lean is the author's own and was not relied on;
  Probes/E6Bridge22_taylor_probe.lean is stale (section 7).
