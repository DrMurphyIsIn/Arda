# Audit testimony: E6Bridge7, discharge of O2 GaussianDominance (2026-09-21)

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge7.lean (612 lines, namespace
RvMBridge7, imports E6Bridge6) and section 5 of telperion/docs/WEIL_CONVERSE_ATTACK_2026-09-20.md.
Probes written by the auditor: Probes/Audit7_Axioms.lean, Probes/Audit7_Shape.lean, plus a
Python numeric check recorded below. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. `RvMBridge7.gaussian_dominance` is a kernel-checked,
axiom-clean, RH-free proof of `RvMBridge6.GaussianDominance` for an arbitrary off-line
nontrivial zero of the actual zero multiset; the window finiteness, the multiplicity lower
bound, the generic centre, the maximiser, the phase and the tail all come from unconditional
inputs, and the final inequality closes with the constants as stated. The Weil converse now
rests on the single zero-free Fourier obligation GaussianApprox. RH is not proved.
conjecture1_proved = False.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8833 jobs).`
Probes/Audit7_Axioms.lean prints axioms for all 35 declarations of the file (every
theorem/lemma/def line, extracted mechanically) plus Zeta23.zetaSeam: 36 of 36 lines read
`depends on axioms: [propext, Classical.choice, Quot.sound]`. No sorryAx.
`#check` output:
```
RvMBridge7.gaussian_dominance : RvMBridge6.GaussianDominance
RvMBridge7.weil_positivity_implies_rh_of_approx : RvMBridge6.GaussianApprox →
  (∀ (g : ℝ → ℂ), WeilExplicit.IsWeilTest g → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) →
    RiemannHypothesis
```
Token grep for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|
set_option`: only hit is line 12, the phrase "#print axioms" in the header comment.

## 2. Vacuity smuggling: PASS (examined hardest)

(a) No RH input. Grep for `RiemannHypothesis|RH_implies|hRH|rh_implies|on_line` in
E6Bridge7.lean: the only hit is line 609, the conclusion type of the corollary
`weil_positivity_implies_rh_of_approx`. `gaussian_dominance` (lines 519-598) takes
`ρ₀`, `h₀ : IsNontrivialZero ρ₀`, `hre₀ : ρ₀.re ≠ 1/2` and nothing else. No lemma in the file
forces a zero onto the line; the only statements about the zero set consumed are
`zetaSeam.finite_window` and `zetaSeam.one_le_mult` (unconditional, section 2(b)) and E6Bridge6's
reflection facts.

(b) Window finiteness. `windowSet_finite ρ₀ := zetaSeam.finite_window (ρ₀.im - 1) (ρ₀.im + 1)`
(E6Bridge7.lean:200-201). Upstream, `zetaSeam : ZetaSeam := ZetaSeam.of_reflect zeta_reflect_zero
zeta_mult_reflect` (Zeta23/Statement/SeamClosed.lean:22) and the field is
`ZetaSeam.finite_window_holds` (Zeta23/Statement/Seam.lean:91-107), proved by local finiteness of
the zeros of the analytic function zeta on the compact box [0,1] x [T1,T2] (identity theorem on
the connected set C minus {1}, `eqOn_zero_or_eventually_ne_zero_of_preconnected`, plus a finite
subcover). It is a theorem, not an assumption; it is the identity-theorem route rather than the
counting route the E6Bridge7 header words suggest, and either is unconditional. Axiom-clean
(section 1). `one_le_mult` is the companion field `ZetaSeam.one_le_mult_holds`.

(c) M > 0 from ρ₀ alone. `exists_generic_centre hre₀` gives `|c - ρ₀.im| < |1/2 - ρ₀.re|`
(line 239-251); in `gaussian_dominance`, `hM0 : 0 < M` is derived (lines 530-540) from
`phi c ρ₀ ≤ M` (ρ₀ is in its own window, `self_mem_window h₀`) and `0 < phi c ρ₀`, the latter
from `(ρ₀.im - c)^2 < (1/2 - ρ₀.re)^2` by `pow_lt_pow_left₀ hcI`. Only h₀ (strip) and hre₀ are
used. Audit7_Shape.lean confirms the off-line hypothesis is what makes this work:
`audit_phi_nonpos_on_line : ρ₀.re = 1/2 → phi c ρ₀ ≤ 0` (axiom-clean), and with hre₀ deleted
both `exists_generic_centre` (`Audit7_Shape.lean:30:30: error: Tactic assumption failed`) and
`0 < phi c ρ₀` (`Audit7_Shape.lean:35:2: error: linarith failed`) fail.

(d) Phase lemma is genuine trigonometry. `exists_lam_trig` (lines 118-175): for x = 0 the bracket
is -y^2 = -(0 + y^2) for every lam; for x ≠ 0 it takes θ = arg(-(x+iy)^2) with `Complex.cos_arg`,
`sin_arg` and ‖z₀‖ = x^2 + y^2, so (x^2-y^2) cos θ + 2xy sin θ = -[(x^2-y^2)^2 + 4x^2y^2]/(x^2+y^2)
= -(x^2+y^2), then lam = (θ + 2πk)/(4xy) with k from `exists_int_gt`/`exists_int_lt` by the sign
of xy and `Real.cos_add_int_mul_two_pi`. Numeric instance x = 1, y = 1/4, lam₀ = 100 (Python,
following the file's construction): max |bracket| = sqrt((15/16)^2 + (1/2)^2) = 1.0625 = 17/16,
target -1.0625; θ = -2.6516, k = 17, lam = 104.1625 ≥ 100, bracket(lam) = -1.0625, |diff| = 0.
The Lean instantiation `exists_lam_trig 100 1 (1/4)` elaborates (Audit7_Shape.lean probe 5).
`re_gaussTest` (the real-part formula) was also checked numerically at three random points on
the strip against direct complex evaluation: |diff| ≤ 1.4e-17.

(e) Tail is lam-uniform for lam ≥ 1 with explicit constants and a summable majorant.
`majorant ρ₀ c M η lam ρ = e^{2 lam (M-η)} [ρ ∈ window] m wsq + m C₁/(1+|γ_ρ|^2)` with
C₁ = e^{1/2}(2c^2 + 13/4)/min(1,1)^2, the E6Bridge6 strip constant at lam = 1 (lines 343-349).
`norm_term_le_majorant` (lines 366-435): inside the window off the pair, `phi ≤ M - η` and
lam > 0 give e^{2 lam phi} ≤ e^{2 lam (M-η)}; outside the window `phi_neg_of_not_mem_window`
gives phi < 0 so for lam ≥ 1, e^{2 lam phi} ≤ e^{2 phi} and the term is at most its lam = 1
value, bounded by `norm_gaussTest_mul_le c 1`; non-zeros give term = 0. `summable_majorant`
(line 359-364) is `summable_of_ne_finset_zero` (finite window part) plus
`summable_mult_div_one_add_normSq` (E6Bridge6, from Zeta23 `zero_sum_inv_sq`, the local
count). The majorant does not depend on the summability of anything that could fail; it is
lam-uniform in shape with lam entering only through the factor e^{2 lam (M-η)}. `tail_bound`
(lines 470-490) then gives ‖tail‖ ≤ e^{2 lam (M-η)} A + B with A = Σ_window m wsq (finite sum,
`constA`) and B = Σ' m C₁/(1+|γ|^2) (`constB`, a genuine tsum of a summable family).
Note: `min 1 1` in C₁ is literally 1 (a leftover of instantiating the general constant at
lam = 1); harmless.

(f) Generic centre and the pair. `badOf ρ ρ'` is the unique c with phi_c ρ = phi_c ρ' when
Im ρ ≠ Im ρ' (`eq_badOf_of_phi_eq`, lines 220-228: linear in c, denominator 2(Im ρ - Im ρ')).
`badSet ρ₀` is the Finset image of badOf over window × window, hence finite (lines 231-233).
`exists_generic_centre` picks c in the open interval |c - Im ρ₀| < |1/2 - Re ρ₀| minus the bad
set via `Set.Ioo_infinite` and `Set.Infinite.sdiff` (lines 239-251); the interval is nonempty
because hre₀ makes its radius positive. `eq_or_eq_reflect_of_phi_eq` (lines 255-277): a tie
at a generic centre forces equal ordinates, then (1/2 - Re ρ)^2 = (1/2 - Re ρ')^2, factored as
(Re ρ - Re ρ')(Re ρ + Re ρ' - 1) = 0, so ρ = ρ' or ρ = 1 - conj ρ' = reflect ρ'. The two pair
terms have the SAME real part and add: `audit_term_reflect : term c lam (reflect ρ) =
conj (term c lam ρ)` (Audit7_Shape.lean, axiom-clean, via E6Bridge6 `zeroMult_reflect`,
`gammaOf_reflect`, `gaussTest_conj`); `zeroSide_pair_split` (E6Bridge6) writes the pair as
2 m(ρ₁) Re G(γ₁). The maximiser ρ₁ from `Finset.exists_max_image` on the window, and the gap
η from a second `exists_max_image` on the window minus the pair (η := 1 if that set is empty),
lines 281-315.

(g) Final inequality. From `re_zeroSide_le` and the phase, hmain reads
Re S ≤ -2K e^{2 lam M} + e^{2 lam (M-η)} A + B with K = m₁ wsq₁ > 0 (m₁ ≥ 1 by `one_le_mult`,
wsq₁ > 0 since ρ₁ is off the line), M > 0, η > 0, and lam ≥ max(1, A/(2ηK), B/(2MK)).
Re-derivation: A/K ≤ 2 lam η ≤ 2 lam η + 1 ≤ e^{2 lam η} gives e^{2 lam (M-η)} A ≤ K e^{2 lam M};
B/K ≤ 2 lam M < 2 lam M + 1 ≤ e^{2 lam M} gives B < K e^{2 lam M}; so
Re S ≤ -2K e^{2 lam M} + K e^{2 lam M} + B < 0. I re-proved exactly this abstract inequality
independently: `audit_final_ineq` in Audit7_Shape.lean, axiom-clean, with the file's constants
and the file's lam threshold.

## 3. Independent mathematics: PASS, no gap

Paper (five steps) and the Lean lemma for each:
1. Window: nontrivial zeros with |Im ρ - Im ρ₀| ≤ 1 (half-open) form a finite set.
   [`windowSet_finite`, `window`, `mem_window`, `self_mem_window`.]
2. Generic centre: c with |c - Im ρ₀| < |δ₀| avoiding the finitely many tying centres;
   then phi_c(ρ₀) > 0. [`badOf`, `eq_badOf_of_phi_eq`, `badSet`, `exists_generic_centre`; the
   positivity in `gaussian_dominance` lines 530-540.]
3. Maximiser and gap: ρ₁ = argmax phi_c on the window, M > 0 so ρ₁ off the line; ties are the
   reflected pair only; η > 0 with phi ≤ M - η elsewhere in the window.
   [`exists_maximiser_gap`, `eq_or_eq_reflect_of_phi_eq`; h₁ and hy₁ in the main proof.]
4. Tail: outside the window phi < 0 and the term is at most its lam = 1 value, summable by the
   local count; inside off the pair at most m wsq e^{2 lam (M-η)}.
   [`phi_neg_of_not_mem_window`, `majorant`, `norm_term_le_majorant`, `summable_majorant`,
   `tsum_majorant`, `tail_bound`, `constA`, `constB`.]
5. Phase and assembly: pick lam ≥ lam₀ with Re G(γ₁) = -wsq₁ e^{2 lam M}; then
   Re S ≤ -2K e^{2 lam M} + A e^{2 lam (M-η)} + B < 0.
   [`exists_lam_trig`, `exists_lam_re_gaussTest`, `re_zeroSide_le`, `gaussian_dominance`.]

Gaps: none. Two remarks, neither a defect. (i) The pair split does not need reflect ρ₁ to lie
in the window; it is an algebraic split of the tsum, and `zeroMult_reflect` (E6Bridge6) makes
the reflected term the conjugate. (ii) The header's phrase "the summable local-count majorant"
is right for B (`zero_sum_inv_sq`), while the window finiteness itself comes from analyticity,
not from a count (section 2(b)).

## 4. Consumption of the O2 shape: PASS

`example : RvMBridge6.GaussianDominance := RvMBridge7.gaussian_dominance` and the composition
`RvMBridge6.weil_positivity_implies_rh_of' hA RvMBridge7.gaussian_dominance hpos :
RiemannHypothesis` both elaborate with no error (Audit7_Shape.lean, probes 1). The off-line
hypothesis is load-bearing: with it deleted, `exists_generic_centre` and the `0 < phi c ρ₀`
step both fail (section 2(c) evidence lines), and on the line phi_c ≤ 0 is a theorem.

## 5. Memo section 5 honesty: PASS

The section states the result ("kernel-checked with no sub-obligation"), which section 1 here
verifies; it says the converse "now rests on the single zero-free Fourier obligation O1'",
which matches the corollary's type; and it records each Lean choice against the section 2 plan
(coordinates, window, generic centre with `Set.Ioo_infinite`/`Set.Infinite.sdiff`, maximiser
and gap with η := 1 in the empty case, outside-window negativity, the majorant and the three
tsum comparison lemmas, the phase via `Complex.cos_arg`/`sin_arg` and integer choice, the
assembly threshold lam₀ with `Real.add_one_le_exp` twice). Every lemma it names exists in the
file with the described role. It notes that no GenericCentre sub-obligation was needed, which
is true. No overclaim: RH is not mentioned as proved; the file header ends "No RH progress is
claimed ... conjecture1_proved = False."

## Probe inventory

- Probes/Audit7_Axioms.lean: 36 axiom prints, 2 #check lines.
- Probes/Audit7_Shape.lean: 2 shape-consumption examples (success), `audit_term_reflect`
  (success), `audit_phi_nonpos_on_line` (success), 2 expected failures with the off-line
  hypothesis deleted, the concrete phase instantiation (success), `audit_final_ineq` (success).
- Python numeric check: phase lemma at x = 1, y = 1/4, lam₀ = 100 (exact hit, lam = 104.1625);
  `re_gaussTest` formula vs direct evaluation at three random strip points (|diff| ≤ 1.4e-17).
- Probes/E6Bridge7_probe.lean is the author's own probe and was not relied on.
