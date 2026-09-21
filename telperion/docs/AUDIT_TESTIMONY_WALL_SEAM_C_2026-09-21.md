# Audit testimony: E6Bridge12, the ladder-certified region (seam C), 2026-09-21

AN INSTRUMENT WITH A LOAD-BEARING ON-LINE HYPOTHESIS, NOT A PROOF OF THE RIEMANN HYPOTHESIS.
E6Bridge12 proves that the Gaussian zero sum F(c, lam) is nonnegative for large lam GIVEN the
hypothesis `WindowOnLine c D` (every nontrivial zero with |Im ρ - c| ≤ D is on the line) plus a
certified near zero (or a finite dominance certificate). That hypothesis is exactly what a
finite Turing verification supplies for bounded c and nothing supplies beyond; the file asserts
nothing about zeros outside the window. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge12.lean (476 lines, namespace
RvMBridge12, imports E6Bridge6 and E6Bridge7) and memo WALL_SEAM_C_LADDER_REGION_2026-09-21.md.
Probes: Probes/Audit12_Axioms.lean, Probes/Audit12_Probes.lean. No git state changed; no other
file edited.

Overall verdict: PASS. No defect found. The split, tail bound, near floor, threshold arithmetic
and dominance form are all correct as written; the window finiteness is a theorem; the on-line
hypothesis is load-bearing and the hypotheses are jointly satisfiable; the memo describes the
ladder's binders honestly and as a registry-level composition.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8841 jobs).` E6Bridge12 in defaultTargets
(lakefile.toml line 9) and a lean_lib (line 107); the guard carries 29 RvMBridge12 lines.
Probes/Audit12_Axioms.lean prints axioms for all 36 declarations: 36 of 36 read
`[propext, Classical.choice, Quot.sound]`, no sorryAx. Token grep for `sorry|admit|native_decide|
axiom|opaque|unsafe|implemented_by|extern|partial|set_option`: only hit is line 46, the phrase
"#print axioms" in the header comment. Imports: `E6Bridge6`, `E6Bridge7` only (lines 60-61).

## 2. The split: PASS

`zeroSide_split` (lines 188-194): zeroSide (gaussTest c lam) = Σ'_{winSet} term + Σ'_{winSetᶜ} term
by `Summable.tsum_add_tsum_compl`, both parts summable via `summable_term_subtype` =
`(summable_gauss_zeroSide c lam hlam).subtype` (lam > 0). Probe confirms both Summable facts
elaborate. The window index set `winSet c D = {ρ | |Im ρ - c| ≤ D}` is NOT assumed finite for the
split (it need not be; the tsum over it is a genuine sum by summability). The FINITE certified
window used in the dominance form is `zeroWindowSet c D = {nontrivial zeros} ∩ winSet c D`, and
`zeroWindowSet_finite` (lines 383-388) is a theorem: it is a subset of Zeta23's
`zetaSeam.finite_window (c - D - 1) (c + D)`, which upstream is `ZetaSeam.finite_window_holds`
(identity theorem + compactness, audited 2026-09-21 for E6Bridge7). `re_window_eq_windowSum`
(lines 424-440) collapses the window tsum to the Finset sum via `tsum_subtype` + `tsum_eq_sum`
(summands off the finite zero window vanish by `term_eq_zero_of_not_nontrivial`), using
`re_term_of_on_line` under hwin for each term. Correct.

## 3. The tail bound: PASS

`phi_le_of_far` (lines 207-221): for a strip zero |1/2 - Re ρ| < 1/2 so (1/2 - Re ρ)² ≤ 1/4, and
D < |Im ρ - c| with D ≥ 0 gives D² ≤ (Im ρ - c)²; hence phi_c ρ ≤ 1/4 - D². Both directions
checked. `norm_term_le_tail` (lines 225-266): for lam ≥ 1, e^{2 lam phi} = e^{2(lam-1)phi} e^{2 phi}
≤ e^{2(lam-1)(1/4 - D²)} e^{2 phi} because lam - 1 ≥ 0 and phi ≤ 1/4 - D² (the nlinarith step uses
`mul_le_mul_of_nonneg_left hφ (sub_nonneg.mpr hlam)`; valid whatever the sign of 1/4 - D²). The
lam = 1 term ‖term c 1 ρ‖ = m ‖gaussTest c 1 (γ_ρ)‖ ≤ m C₁/(1 + |γ_ρ|²) by E6Bridge6's
`norm_gaussTest_mul_le c 1` (strip |Im γ| ≤ 1/2), which is `tailWeight c ρ`; non-zeros give 0.
`tail_bound_window` (lines 270-296): ‖Σ'_{Sᶜ}‖ ≤ Σ' ‖term‖ ≤ Σ'_{S} E·tailWeight ≤ Σ'_ℂ E·tailWeight
= E · constB c with E = e^{2(lam-1)(1/4 - D²)}, by `norm_tsum_le_tsum_norm`, `tsum_le_tsum`,
`tsum_subtype_le`, `tsum_mul_left`. `tsum_tailWeight : Σ' tailWeight c = constB c` is `rfl`
(line 96), and `constB c` (E6Bridge7) is the tsum of E6Bridge7's lam = 1 majorant, summable by
`summable_mult_div_one_add_normSq` (local zero count), lam-independent and finite. Direction of
every inequality verified. Re-derived on paper: correct.

## 4. The near floor: PASS

`near_term_ge` (lines 134-157): under hline (ρ on the line) `re_term_of_on_line` gives
Re term = m (Im ρ - c)² e^{-2 lam (Im ρ - c)²}, a real; m ≥ 1 from `zetaSeam.one_le_mult`, whose
upstream proof (Zeta23/Statement/Seam.lean:50-58) is: ζ analytic at ρ ≠ 1, `analyticOrderAt ≠ 0`
because ζ ρ = 0, `analyticOrderAt_riemannZeta_ne_top`, so the toNat is ≥ 1. Then
δ² ≤ (Im ρ - c)² from δ ≤ |Im ρ - c| (δ ≥ 0) and e^{-2 lam d²} ≤ e^{-2 lam (Im ρ - c)²} from
(Im ρ - c)² ≤ d² and lam ≥ 0. In `gaussian_positivity_of_window` (lines 350-366) hwin is invoked
with `h₁win : |ρ₁.im - c| ≤ D` obtained as hd₁.trans hdD where `hdD : d ≤ D` is derived from
hgap (d² + 1/4 < D²) via `pow_le_pow_iff_left₀` with d ≥ 0 (from |.| ≤ d) and D ≥ 0. So
|ρ₁.im - c| ≤ d ≤ D is used exactly as required to put ρ₁ on the line by hwin.
`re_window_ge_term` then bounds the window tsum below by that single term because every window
summand has Re ≥ 0 under hwin (`Summable.le_tsum`). Correct.

## 5. Threshold arithmetic: PASS

`tail_le_near_of_threshold` (lines 302-344). With κ = D² - 1/4 - d² > 0 (hgap), B = constB c,
lam ≥ B e^{2(D² - 1/4)}/(2κδ²) gives B e^{2(D²-1/4)} ≤ lam · 2κδ². The exponent identity
e^{2(lam-1)(1/4 - D²)} = e^{2(D² - 1/4)} · e^{-2 lam κ} · e^{-2 lam d²} (hEsplit: 2(lam-1)(1/4-D²)
= 2(D²-1/4) - 2 lam (D² - 1/4 - d²) - 2 lam d², checked). The key step is
e^{-2 lam κ}(2 lam κ) ≤ 1, proved from 1 + 2 lam κ ≤ e^{2 lam κ} (`Real.add_one_le_exp`) and
`inv_mul_le_iff₀`: exactly e^{-t} t ≤ 1 for t = 2 lam κ. Then
e^{2(D²-1/4)} e^{-2 lam κ} B = e^{-2 lam κ}(B e^{2(D²-1/4)}) ≤ e^{-2 lam κ} · lam · 2κδ² =
(e^{-2 lam κ} · 2 lam κ) δ² ≤ δ²; multiply by e^{-2 lam d²}. I re-proved this abstract
inequality independently with the file's constants (`audit_threshold`, axiom-clean). The final
assembly uses Re(tail) ≥ -‖tail‖ (`Complex.abs_re_le_norm`) and `linarith`.

## 6. Load-bearing and non-vacuity: PASS

- `audit_re_term_neg_of_off_line`: for an OFF-line nontrivial zero at ordinate c, (term c lam ρ).re
  < 0 (via E6Bridge6 `gaussTest_axis_re_neg` and m ≥ 1), axiom-clean. So termwise nonnegativity
  fails exactly where hwin does not reach.
- hwin deleted: the on-line step `h₁line : ρ₁.re = 1/2` has no source;
  `Audit12_Probes.lean:31:4: error: exact? could not close the goal`.
- `audit_hyps_satisfiable`: under the all-on-line hypothesis, any nontrivial zero ρ and any
  0 < δ ≤ d give BOTH `WindowOnLine (Im ρ - d) D` and the near-zero hypothesis at that centre,
  axiom-clean; so the hypotheses are jointly satisfiable and the theorem is not vacuous by shape.
- `0 < lamThreshold c D d δ` for all arguments (from `one_le_lamThreshold`), elaborates.
- `WindowOnLine c D` by `aesop` after unfold: `79:2: warning: aesop: failed ... 77:40: error:
  unsolved goals`; not closed by automation.

## 7. Memo honesty: PASS

The memo's hookup section says the top rung
`AllZeros_h640000.all_nontrivial_zeros_up_to_height_640000_of_bands` concludes
`∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 640000 → ρ.re = 1/2` GIVEN one `BandHyp` binder per
1000-height segment plus the height-floor `hγ`. Verified against
telperion/examples/zeta_zero_localization/lean/AllZeros_h640000.lean: binders `hbands_1000 :
AllZeros_h1000.BandHyp` ... (lines 307 ff.), `hγ : ∀ ρ, riemannZeta ρ = 0 → 0 < ρ.im →
ρ.im ≤ 640000 → 55/16 ≤ |ρ.im|` (line 642), conclusion at line 643 verbatim as the memo states;
`BandHyp` (lines 284-286) is "every zero in the box [1/4000000, 3999999/4000000] × [bLo i, bHi i]
is on the line", as described. Module count 642 (`ls AllZeros_h*.lean | wc -l`), as the memo
says. The memo states plainly that the instantiation "is a registry-level composition, not a
Lean import" (different toolchains, v4.32 vs v4.33.0-rc2), that the ANDÚRIL node
`AND_ladder_h280000` exists (missions/anduril/nodes/AND_ladder_h280000.toml, present) and is
open until the BandHyp binders are discharged, and that "the 640000 rung has no registry node
yet". It also records the two ladder-side facts still needed (conjugation reflection for
negative c; real-axis exclusion for |c| < D) and that the lam ≥ 1 floor and the crude threshold
are limitations of the instrument. Disclaimers: memo lines 8-10 "Nothing here proves RH ... The
uncertified residual is the Wall"; file lines 52-56 "NOT proved: RH ... The uncertified residual
... IS the Wall." No overclaim found. One observation, not a defect: the file header's
"currently T = 640000" and the memo's "for c ≤ T - D" describe what the ladder WOULD supply
once its binders are discharged; the memo says so explicitly.

## Probe inventory

- Probes/Audit12_Axioms.lean: 36 axiom prints, 2 #check.
- Probes/Audit12_Probes.lean: 3 axiom-clean theorems (off-line negativity, joint satisfiability,
  threshold re-proof), 3 elaboration successes (threshold positive, window finiteness, both
  summabilities), 2 expected failures (hwin deleted; WindowOnLine by aesop).
- Probes/E6Bridge12_probe.lean is the author's own and was not relied on.
