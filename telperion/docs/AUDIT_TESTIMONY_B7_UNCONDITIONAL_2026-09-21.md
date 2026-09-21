The artifact is the last obligation discharged and the Bombieri-Lagarias explicit formula on Li's class proved unconditionally; identities about zeros and primes; NOT a proof of anything about RH.

# Audit testimony: E6Bridge24 (StripDerivBound) + E6Bridge27 (unconditional B7 assembly)

Auditor: auditor-forward (blind, adversarial). Date: 2026-09-21.
Worktree: /Users/peterwmurphy/arda-goal-weil, island telperion/examples/rvm_bridge/lean,
Lean v4.33.0-rc2, Zeta23 pinned fbdc36bbf17d20af3fd0447c6d1a8a02773c9844.
Files: E6Bridge24.lean (882 lines, namespace RvMBridge24), E6Bridge27.lean (36 lines, namespace RvMBridge27).
Probes: Probes/Audit24_Axioms.lean, Probes/Audit24_Probes.lean. conjecture1_proved = False.

## 1. Verdict

PASS for both modules. E6Bridge24 discharges `StripDerivBound` exactly as declared in E6Bridge22
(same `def : Prop`, consumed unchanged); E6Bridge27 composes the three discharged facts into the
registry node statement byte for byte with no hypothesis. All declarations are kernel-clean.

One-sentence verdicts:
- E6Bridge24: the Landau local partial fraction plus digamma Stirling plus Cauchy on a zero-free
  circle gives the strip derivative bound honestly, with the two plan adjustments (symmetric
  difference of Landau ball and window; low heights by compactness) both correct.
- E6Bridge27: three one-line compositions, the node theorem is the registry statement
  verbatim with no hypothesis, and the file says identities hold whether or not RH holds.

## 2. Kernel evidence (my own runs)

Probes/Audit24_Axioms.lean: 36/36 declarations (31 RvMBridge24, 3 RvMBridge27, 2 Zeta23 inputs)
report `[propext, Classical.choice, Quot.sound]`. Probes/Audit24_Probes.lean re-confirms:

    'RvMBridge27.bl_explicit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RvMBridge27.liValue' depends on axioms: [propext, Classical.choice, Quot.sound]
    'RvMBridge27.xi_logDeriv_deriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

Full `lake build`: green (8873 jobs). Guard: 30 + 4 lines.
Token grep (sorry/admit/native_decide/axiom/opaque/unsafe/implemented_by/extern/partial/set_option)
on both files: only E6Bridge24.lean:217, a lemma NAME containing the substring; no tokens.

## 3. Registry byte comparison (E6Bridge27)

missions/rh/lean/Statements/RH_bl_explicit_formula.lean:

    theorem bl_explicit_formula (n : ℕ) (hn : 0 < n) :
        Tendsto (BombieriLagarias.liZeroSum n) atTop
          (𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n)) := by sorry

E6Bridge27 `bl_explicit_formula`: identical statement text (python byte comparison), no
hypothesis, proof term `RvMBridge25.bl_explicit_formula_of_two RvMBridge23.local_count_sum
RvMBridge24.stripDerivBound n hn`. The six BombieriLagarias definitions (liKernel, liZeroSum,
archSide, zetaLogDerivReg, eta, finiteSide) are byte-identical between RHDefs.lean and
E6Bridge15.lean (re-confirmed this audit).

## 4. Independent re-composition (probe 1)

Bypassing E6Bridge25's packaged lemma, I rebuilt the chain from the primitives:
`RvMBridge22.xiLogDerivDerivEq_of_two local_count_sum stripDerivBound` gives XiLogDerivDerivEq;
`RvMBridge19.liValue_of` with `RvMBridge25.noRealZeroInUnitInterval` gives LiValue n;
`RvMBridge15.bl_explicit_formula_of` gives the node. All three kernel-clean (audit_partialFraction,
audit_liValue, audit_node). So the node depends on exactly the three discharged facts and nothing else.

## 5. E6Bridge24 mathematics, re-derived by hand

Obligation (E6Bridge22, unchanged): ∃ C, ∀ s with 1/4 ≤ Re s ≤ 9/4, 5 ≤ |Im s|, s not a zero,
‖ξ'/ξ)'(s) + Σ_{window s} m/(s-ρ)²‖ ≤ C (1 + log(2 + |Im s|)).

(A) exists_window_bound: window s has heights within 2 of Im s, covered by 5 unit intervals,
so Σ_window m ≤ 5 A₀ log(|Im s| + 6) from Zeta23.RvM.zeta_local_zero_count. Checked.
(B) norm_digamma_le_log: from digamma_stirling (‖ψ(z) - log z + 1/(2z)‖ ≤ 3/Im z²) with
0 < Re z ≤ 2, |Im z| ≥ 1: ‖log z‖ ≤ log(2+|Im z|) + π, ‖1/(2z)‖ ≤ 1/2, 3/Im z² ≤ 3. Sum
≤ log(2+|Im z|) + π + 7/2. Checked.
(C) landau_window: repackages Zeta23.WeilEF.zeta_logDeriv_partial_fraction (ball radius
22/25 * 91/50 = 1.6016 about 2 + it, |t| ≥ 6, comparison ball 3/2) with 1.6016 ≤ 161/100 and
8/5 < 1.6016 for the complement. zeroMult = analyticOrderNatAt on the zero set. Checked.
(D) Fwin / FwinExt: logDeriv ξ minus the window partial fraction; extended across zeros by
limUnder. FwinExt_differentiableOn on ball s (1/2) uses removable singularities (the window
contains every zero within 1/2 of s since 1/2 < 2). deriv_FwinExt at a non-zero s equals
(ξ'/ξ)'(s) + Σ m/(s-ρ)², which is exactly the obligation's quantity. Checked.
(E) exists_radius: finitely many zeros in the window, so some r in (1/4, 1/2) has a zero-free
sphere. Cauchy: ‖deriv FwinExt s‖ ≤ B/r ≤ 4B where B bounds FwinExt on the sphere. Checked.
(F) Fwin_bound_core (the heart). For w on the sphere with 1/2 ≤ Re w ≤ 7/2, |Im w| ≥ 6, w not
a zero: logDeriv ξ w = 1/w + 1/(w-1) - (log π)/2 + ψ(w/2)/2 + logDeriv ζ w. Using landau_window
with Z about c = 2 + i Im w: ‖logDeriv ζ w - Σ_Z m/(w-ρ)‖ ≤ C log(|Im w|+3). Then
Σ_Z - Σ_window splits as (Z \ W) - (W \ Z):
  - ρ ∈ Z \ W: |Im ρ - Im s| > 2 and dist(w,s) ≤ 1/2 give |Im ρ - Im w| > 3/2, so ‖w-ρ‖ ≥ 3/2
    (probe 2, audit_far_part); the term is ≤ (2/3) Σ_Z m ≤ (2/3) C log(|Im w|+3).
  - ρ ∈ W \ Z: dist(ρ,c) > 8/5 and dist(w,c) ≤ 3/2 give ‖w-ρ‖ ≥ 1/10 (probe 2,
    audit_near_part); the term is ≤ 10 Σ_W m ≤ 10 A log(|Im s|+6).
  Digamma: Re(w/2) ∈ (0, 7/4], |Im(w/2)| ≥ 3 satisfy (B) (probe 3). |Im w| ≤ |Im s| + 1/2, and
  log(|Im s| + 13/2) ≤ log 3 + log(2 + |Im s|) etc. absorb into K (1 + log(2 + |Im s|)) with
  K = (1/3 + log π/2 + (π + 7/2)/2 + 1/2) + (C log 2 + C) + (2/3 C log 2 + 2/3 C)
      + (10 A log 3 + 10 A). Nonnegative, independent of s. Checked.
(G) Left half of the sphere (Re w < 1/2): Fwin_one_sub gives Fwin (1-s) (1-w) = -Fwin s w
(ξ(1-z) = ξ(z), window reflects to window, zeroMult reflects). 1 - w has 1/2 ≤ Re ≤ 7/2 and
the same |Im| (probe 4), so (F) applies at (1-s, 1-w). Checked.
(H) sphere_bound / target_bound_high: needs |Im w| ≥ 6 on the sphere, so |Im s| ≥ 13/2;
K₂ = 4K via r > 1/4. target_bound_low: |Im s| ≤ 7 by compactness of Icc(1/4,9/4) × Icc(-7,7)
for xiDiffExt (continuous, no zeros at |Im| < 14.13 anyway) plus the far-sum comparison
2((13/4 + 2*49) B₁). Overlap 13/2 ≤ |Im s| ≤ 7 covers 5 ≤ |Im s| (probe 5). Checked.
(I) stripDerivBound: C = K₁ + K₂, split at |Im s| ≤ 7. Consumed by
xiDiffExtGrowthRight_of_localCount and xiLogDerivDerivEq_of_localCount with E6Bridge22 unchanged.

Two plan adjustments recorded in docs/STRIP_DERIV_BOUND_2026-09-21.md lines 28-40 (Landau ball
1.6016 + 1/2 > 2 is NOT inside the window, hence the symmetric difference; low heights without
Landau). Both are the proofs I re-derived above, not weakenings.

## 6. Probes (Probes/Audit24_Probes.lean)

Expected successes (all elaborated, kernel-clean): chain re-composition (probe 1); abstract
distance steps 3/2 and 1/10 (probe 2); digamma hypotheses (probe 3); reflected point (probe 4);
regime overlap (probe 5); consumption of target_bound_low (probe 7).
Expected failure (fails exactly as intended): applying stripDerivBound AT a zero,

    Probes/Audit24_Probes.lean:71:26: error: Application type mismatch: The argument hs
    has type IsNontrivialZero s but is expected to have type ¬IsNontrivialZero s

The off-zero hypothesis is load-bearing; the bound cannot be misapplied at a zero.

## 7. Numeric re-check of the node (mpmath, dps 20, first 2000 zeros paired, density tail)

    lambda_1 closed form 1 + gamma/2 - log(4 pi)/2 = 0.0230957089661 ; archSide 1 + finiteSide 1 = 0.0230957089661
    n=1: zeros(2000, paired) = 0.0226533708596 + tail 0.000442436093414 -> 0.0230958069531, |diff| = 9.8e-8
    n=2: closed form = 0.092345735228 ; zeros + tail -> 0.0923461271969, |diff| = 3.9e-7
    gamma_2000 = 2515.28648292

archSide n + finiteSide n was computed from the file's definitions (eta_j by a Cauchy integral on
|s-1| = 1/2 of -ζ'/ζ - 1/(s-1)); liZeroSum from mp.zetazero. Agreement to well inside the tail
truncation. This checks the identity is the true Bombieri-Lagarias formula, not a vacuous one.

## 8. Overclaim grep

E6Bridge24.lean, E6Bridge27.lean, docs/STRIP_DERIV_BOUND_2026-09-21.md: no "RH proved", "Riemann
hypothesis holds", or similar. E6Bridge27 lines 12-13 read "NOT a proof of anything about RH: these
are identities about the zeros and the primes, valid whether or not RH holds.
conjecture1_proved = False." The memo carries conjecture1_proved = False at line 17.

## 9. What this does and does not establish

Established unconditionally: for every n ≥ 1 the paired zero sum Σ_ρ (1 - (1 - 1/ρ)^n) converges
(ordered by height) to archSide n + finiteSide n, an explicit constant from ζ(k), γ, log π and
the Laurent coefficients of ζ'/ζ at 1. Li's criterion (RH iff all λ_n ≥ 0) is a separate
equivalence; nothing here evaluates the sign of any λ_n by proof. NOT a proof of anything about RH.
