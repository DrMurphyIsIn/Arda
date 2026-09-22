# Audit testimony: E6Bridge14, effective Gaussian dominance and the localisation instrument, 2026-09-21

AN EFFECTIVE DOMINANCE LEMMA AND A LOCALISATION INSTRUMENT WITH LOAD-BEARING LOCAL HYPOTHESES.
NOT A PROOF OF THE RIEMANN HYPOTHESIS. E6Bridge14 proves that an off-line zero which is maximal
in distance from the line within its ordinate window, with a local spacing floor, a window count
and a tail constant handed over as explicit parameters, forces a strictly negative Gaussian zero
sum for every width above an explicit threshold; and that Gaussian positivity on a band above
that threshold localises off-line zeros either below a distance floor or into the band's
margins. Both are unconditional inequalities about the actual zero set; nothing is concluded
about where the zeros are. conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge14.lean (448 lines, namespace
RvMBridge14, `import E6Bridge12` only) and memo WALL_EFFECTIVE_O2_2026-09-21.md. Probes:
Probes/Audit14_Axioms.lean, Probes/Audit14_Probes.lean. No git state changed; no other file
edited.

Overall verdict: PASS. No defect found. Every constant and inequality direction in the centre
term, the competitor bound, the tail bound and the threshold arithmetic re-derives correctly;
the two structural hypotheses (maximality, spacing floor) are used exactly where the paper
argument needs them and cannot be deleted; the numeric bracket is kernel-checked and matches
the hand value; the instrument's disjunction is the correct case split over a finite band with
correctly ranged hypotheses; nothing overclaims.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8847 jobs).` E6Bridge14 in defaultTargets (lakefile
line 9) and a lean_lib (line 129); guard carries 15 RvMBridge14 lines. Probes/Audit14_Axioms.lean
prints axioms for all 15 declarations: 15 of 15 read `[propext, Classical.choice, Quot.sound]`,
no sorryAx. Token grep for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|
partial|set_option`: only hit is line 42, the phrase "#print axioms" in the header comment. Only
the guard and the author's probe import E6Bridge14. `#check` of the two main theorems matches the
brief verbatim (effectiveThreshold y0 xmin N (constB ρ₀.im) D ≤ lam → Re zeroSide < 0; and the
band disjunction).

## 2. The centre c = Im ρ₀: PASS

`re_term_centre` (lines 165-183): for Im ρ = c, gammaOf ρ = c + (1/2 - Re ρ) I (via gammaOf_re/im),
so E6Bridge6's `gaussTest_axis` gives the real value -(y²) e^{2 lam y²} with y = 1/2 - Re ρ, and
Re term = m · (-(y²) e^{2 lam y²}). Re-derived: with x = 0, w = i y, w² = -y², e^{-2 lam w²} =
e^{2 lam y²}, product -y² e^{2 lam y²}, real. Hence `re_term_centre_nonpos`: ALL same-ordinate
zeros (ρ₀, its reflection 1 - conj ρ₀ which has the same ordinate, and any other zero at that
ordinate) contribute ≤ 0. In `re_window_sum_le` (lines 197-256) the pointwise bound U assigns
ρ₀ the value -(Y e^{2 lam Y}) + m Ecomp using m ≥ 1 (`zetaSeam.one_le_mult` through
`zeroMult_eq_mult`) and Y = (1/2 - Re ρ₀)² (`nlinarith [mul_le_mul_of_nonneg_right hm1 hYE]`);
every other same-ordinate zero gets ≤ 0 ≤ m Ecomp. The lower bound on ρ₀'s contribution is
then transported to y0 only through Y ≥ y0² (`hYy`) in the form -(Y E) ≤ -(y0² E) with E =
e^{2 lam Y} unchanged (`hmain`), i.e. exactly the monotonicity of y² e^{2 lam y²} in y² restricted
to the coefficient; correct.

## 3. The competitor bound: PASS

`norm_term_le_competitor` (lines 119-149): for a window zero with a different ordinate,
‖term‖ = m · wsq · e^{2 lam phi} (E6Bridge7 `norm_term`), wsq = x² + y² ≤ D² + 1/4 (x² ≤ D² from
|Im ρ - c| ≤ D; y² ≤ 1/4 from the strip), phi = y² - x² ≤ Y - xmin² using y² ≤ Y (`hY`) and
x² ≥ xmin² (`hx`, needs xmin ≥ 0), so ‖term‖ ≤ m (D² + 1/4) e^{2 lam (Y - xmin²)} with lam ≥ 0.
In `re_window_sum_le`, `hmax` is used ONLY to produce `hYρ : (1/2 - Re ρ)² ≤ Y` by squaring
|1/2 - Re ρ| ≤ |1/2 - Re ρ₀|, and `hsep` ONLY to produce `hx : xmin ≤ |Im ρ - Im ρ₀|` for ρ with
Im ρ ≠ c; neither is used anywhere else (grep of the file: hmax at lines 200, 245; hsep at 202,
247, and the instrument's hsep'). Nothing silently stronger. The memo's remark that the
competitor lemma would be false for negative xmin is right, and the theorem carries 0 < xmin.

## 4. Assembly and threshold arithmetic: PASS

Window: ≤ -Y E + (D² + 1/4) e^{2 lam (Y - xmin²)} Σ m ≤ -Y E + N (D² + 1/4) e^{2 lam (Y - xmin²)}
(`hcount` from hN). Tail: `tail_bound_window` (E6Bridge12) gives ‖tail‖ ≤ e^{2 (lam-1)(1/4 - D²)} B
and `henv`: the exponent is ≤ 0 since lam ≥ 1 and D ≥ 1 (1/4 - D² ≤ -3/4), so ≤ B; Re tail ≤ ‖tail‖
(`Complex.re_le_norm`). Threshold: `le_exp_of_log_le` turns log(max 1 Q)/(2a) ≤ lam into
Q ≤ max 1 Q = e^{log(max 1 Q)} ≤ e^{2 lam a}; the `max 1` makes the log of a value ≤ 1 (N = 0 or
B = 0, or small Q) harmless. First term with Q = 4N(D²+1/4)/y0², a = xmin²: N(D²+1/4) ≤ (y0²/4)
e^{2 lam xmin²}, hence the competitor ≤ (y0²/4) e^{2 lam (Y - xmin²)} e^{2 lam xmin²} = (y0²/4) E
(`hcomp`, `hF`). Second term with Q = 4B/y0², a = y0²: B ≤ (y0²/4) e^{2 lam y0²} ≤ (y0²/4) e^{2 lam Y}
= (y0²/4) E since y0² ≤ Y and lam > 0 (`htailB`). Total ≤ -Y E + (y0²/4) E + (y0²/4) E ≤ -y0² E +
(y0²/2) E = -(y0²/2) E < 0. I re-proved the closing step abstractly (`audit_closing`, axiom-clean).
`effectiveThreshold_mono_B`: B ≤ B' ⟹ 4B/y0² ≤ 4B'/y0² ⟹ max 1 · monotone ⟹ log monotone on the
positive values max 1 · ⟹ divide by 2y0² > 0; the `max 1` does not break monotonicity (it is
itself monotone) and is what keeps `Real.log_le_log` applicable. Probe A4 confirms
`le_exp_of_log_le` at Q = 1/2 and Q = -3.

## 5. Load-bearing: PASS

- hsep deleted: `re_window_sum_le` cannot be applied, the spacing argument is an unfillable
  hole (`Audit14_Probes.lean:121:48: error: don't know how to synthesize placeholder`).
- hmax deleted: likewise (`131:39: error: don't know how to synthesize placeholder`).
- Threshold unbounded as xmin → 0: `effectiveThreshold_unbounded_of_small_spacing` (lines 78-109)
  takes xmin = √(L/(2 max K 1)) with L = log(4N(D²+1/4)/y0²) > 0 (needs N ≥ 1, D ≥ 1, y0 ≤ 1/2 so
  the argument exceeds 1) and gets L/(2 xmin²) = max K 1 ≥ K; probe instantiates K = 10^9.
- Threshold hypothesis load-bearing: applying the theorem at lam = 1 with the memo's parameters
  fails (`173:66: error: linarith failed`, since the threshold is ≥ 297).
- hmax counter-scenario (in words, no Lean probe practical since it concerns hypothetical
  zeros): a zero ρ' at ordinate distance x' from c with y'² > Y + x'² has exponent y'² - x'² > Y,
  so its summand's modulus m'(x'² + y'²) e^{2 lam (y'² - x'²)} outgrows the main term
  Y e^{2 lam Y}, and its real part 2m'|w'|² e^{2 lam (y'²-x'²)} cos(2 arg w' - 4 lam x' y') is
  positive on a positive-density set of lam; no threshold of the stated form can beat it. That is
  exactly why E6Bridge7 uses a generic centre and a phase chosen after the configuration, and why
  the effective version asks the consumer for the maximal zero instead. The memo says this
  (section 3).

## 6. The numeric probe: PASS

Hand value: first term log(4·20·(4 + 1/4)/(1/100))/(2/25) = log 34000 / 0.08 = 10.434/0.08 =
130.43; second term log(4·1/(1/100))/(2/100) = 50 log 400 = 50 · 5.99146 = 299.573. Threshold =
299.573 ∈ [297, 300]. Python agrees to all printed digits. The author's
`threshold_example_le : effectiveThreshold (1/10) (1/5) 20 1 2 ≤ 300` and `threshold_example_ge :
297 ≤ ...` were re-elaborated inside my own probe file and print
`depends on axioms: [propext, Classical.choice, Quot.sound]` (kernel-checked, via
`Real.exp_one_gt_d9`/`lt_d9` powers). At this threshold the two controlled terms are
N(D²+1/4)e^{-2 lam xmin²} = 3.3e-9 ≤ y0²/4 = 0.0025 and B e^{-2 lam y0²} = 0.0025 = y0²/4 (the
second is tight, as the formula intends).

## 7. The instrument: PASS

`offline_zeros_small_or_margin` (lines 329-401). Logic re-derived: S = nontrivial zeros with
ordinate in [T₁ - D, T₂ + D] is finite (`band_finite` ⊆ `zetaSeam.finite_window (T₁-D-1) (T₂+D)`).
If S is empty, the first branch holds vacuously. Otherwise take ρ₀ maximising |1/2 - Re| over S
(`Finset.exists_max_image`). If |1/2 - Re ρ₀| < y0, every zero of S is below y0: first branch. If
≥ y0 and Im ρ₀ ∈ [T₁, T₂]: the D-window around Im ρ₀ lies inside [T₁ - D, T₂ + D], so window zeros
are in S and ρ₀ is window-maximal (`hmax`); `hsep'` is `hsep` at ρ = ρ₀ (which needs T₁ ≤ Im ρ₀ ≤
T₂, available); `hN` and `hB` are used at c = Im ρ₀ ∈ [T₁, T₂]; `effectiveThreshold_mono_B` lifts
the constB threshold to the Bmax threshold; `effective_gaussian_dominance` gives Re < 0 at lam =
threshold(Bmax), while `hpos` at that c and lam gives ≥ 0: contradiction. Otherwise Im ρ₀ ∉ [T₁, T₂]
but ∈ [T₁ - D, T₂ + D]: the margin branch with maximality over the widened band. Ranges: hN, hB,
hpos quantify over c ∈ [T₁, T₂] (the band); hsep over ρ with ordinate in the band and ρ' within D
of it, exactly the pairs the window step needs; the conclusion quantifies over the widened band.
I re-composed the contradiction step from the named lemmas (probe A5, elaborates).
`windowCount_le_Ncount` bounds the window count by Zeta23.Ncount (c - D - 1) (c + D), the
cumulative local count, as the memo says.

## 8. Overclaim: PASS

Grep over E6Bridge14.lean and the memo (prove(s/d) RH/Riemann, RH is/holds/proved, progress
toward, goal node proved, conjecture1_proved = True, crossing the wall, closes RH): zero hits.
Disclaimers: file lines 48-49 "conjecture1_proved = False: this is an unconditional inequality
about a Gaussian-weighted sum over the zeros of zeta, wherever they are."; memo line 5 same. The
memo states the disjunction "honestly" and that "the margin case is genuine"; section 5 says the
numeric constant for constB "is not pinned in this repository yet". No wording claims more.

## Probe inventory

- Probes/Audit14_Axioms.lean: 15 axiom prints, 2 #check, 1 #print.
- Probes/Audit14_Probes.lean: the author's probe text re-elaborated plus: axiom prints of the two
  bracket theorems (clean); `audit_closing` (clean); `le_exp_of_log_le` at Q = 1/2 and Q = -3;
  monotonicity in B, unbounded threshold at K = 10^9, instrument contradiction step re-composed
  (all elaborate); 3 expected failures (hsep deleted, hmax deleted, lam = 1).
- Python: threshold recomputation and the two controlled terms at the threshold.
