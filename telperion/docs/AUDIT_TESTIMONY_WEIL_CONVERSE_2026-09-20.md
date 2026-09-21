# Audit testimony: E6Bridge6, the converse half of Weil's criterion modulo O1/O2 (2026-09-20)

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge6.lean (603 lines, namespace
RvMBridge6, imports E6Bridge5) and memo telperion/docs/WEIL_CONVERSE_ATTACK_2026-09-20.md.
Probes written by the auditor: Probes/Audit6_Axioms.lean, Audit6_Obligations.lean,
Audit6_Reduction.lean, Audit6_GaussShape.lean. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. The file proves, kernel-checked and axiom-clean, that
Weil positivity on the E8 class implies Mathlib's RiemannHypothesis GIVEN two hypotheses
(GaussianTransfer, GaussianDominance) that are ordinary `def : Prop` statements about zeta's
zeros and Fourier analysis, mention RiemannHypothesis nowhere, are neither provable nor
refutable by automation, are each load-bearing, and whose intended discharges are classical and
concrete. RH is not proved and the file and memo say so. conjecture1_proved = False.

## 1. Kernel: PASS

`lake build` on the island: `Build completed successfully (8831 jobs).` E6Bridge6 is in
lakefile.toml defaultTargets (line 9) and declared as a lean_lib (line 63);
AxiomGuardRvMBridge.lean imports it (line 73) and carries 27 lines naming RvMBridge6.

Probes/Audit6_Axioms.lean prints axioms for all 33 declarations of the file (every
`theorem`/`lemma`/`def` line, extracted mechanically) plus the inputs Zeta23.zetaSeam,
Zeta23.WeilEF.zero_sum_inv_sq, Zeta23.zeta_reflect_zero, Zeta23.zeta_mult_reflect and
RvMBridge5.rh_implies_weil_positivity. Result, 38 of 38 lines:
`depends on axioms: [propext, Classical.choice, Quot.sound]`. No sorryAx.

Token grep on E6Bridge6.lean for `sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|
extern|partial|set_option`: only hit is line 17, the phrase "#print axioms" inside the header
comment. The obligations are `def GaussianTransfer : Prop` (line 300), `def GaussianDominance :
Prop` (line 314) and `def GaussianApprox : Prop` (line 553); none is an `axiom` or an instance.

## 2. Obligations honest: PASS (examined hardest; details per obligation)

`#print` of the three definitions (Audit6_Axioms output) shows their bodies verbatim. None
mentions `RiemannHypothesis`. GaussianDominance quantifies over `IsNontrivialZero ρ₀`,
`ρ₀.re ≠ 1/2`, and the value `(zeroSide (gaussTest c lam)).re`; GaussianTransfer and
GaussianApprox quantify over Weil tests, `hermitianTransform`, `gaussTest`, a strip bound and
`Tendsto`. All objects are the E8 registry vocabulary or Zeta23's `gammaOf`.

### GaussianDominance (O2)

(a) A statement about zeta's zeros only: "if some nontrivial zero is off the line then some
Gaussian-derivative weighted zero sum has negative real part." RH implies it in one line
(vacuously): Audit6_Obligations.lean `audit_O2_of_rh : RiemannHypothesis → GaussianDominance`,
axiom-clean, expected and documented. The reverse is NOT a one-liner: probe 5 (O2 alone implies
RH) fails at `Audit6_Obligations.lean:45:36: error: failed to prove positivity` because nothing
says the Gaussian zero sum is nonnegative without Weil positivity. Classically O2 is expected to
be an unconditional theorem (true whether or not RH holds), so it is strictly weaker than RH and
not an RH-equivalent smuggled in as a hypothesis.

(b) Not false for a trivial reason. The `∃ c lam` carries `0 < lam`, and
`summable_gauss_zeroSide c lam hlam` proves the summand family summable, so the tsum is not the
junk 0; probe 8 (`HasSum ... (zeroSide (gaussTest c lam))` from that summability) elaborates
clean. Under RH the antecedent is empty, so the statement is true; under not-RH it asserts a
negativity that the Weil/Bombieri localisation argument supplies. Refutation attempt probe 7
(`¬ GaussianDominance` by simp) fails: `Audit6_Obligations.lean:67:2: error: simp made no
progress`.

(c) Genuine sum: yes, by `summable_gauss_zeroSide` (norm bound `norm_gaussTest_mul_le` on the
strip |Im z| ≤ 1/2, which contains every `gammaOf ρ` for strip zeros via Zeta23
`abs_gammaOf_im_lt`, against the local-count majorant `summable_mult_div_one_add_normSq`
transported from Zeta23 `zero_sum_inv_sq zetaSeam`). Both are axiom-clean (section 1). The
`.re` in O2 loses nothing: `gauss_zeroSide_real` shows the value is real.

(d) No pathological discharge. Probe 4 (c arbitrary, lam = 1000, simp) fails:
`Audit6_Obligations.lean:35:78: error: unsolved goals`. Probe 2 (centre at Im ρ₀, lam = 1, simp
/ aesop) fails at lines 14 and 20. Probe 3 (pair split at centre Im ρ₀: pair term negative by
`gaussTest_axis_re_neg`, then positivity on the remainder) fails: `Audit6_Obligations.lean:32:2:
error: not a positivity goal`, i.e. the remainder tsum over the other zeros is unconstrained,
which is exactly the "nearby zero with larger |delta| can win" caveat in the docstring of
`gauss_zeroSide_pair_split` (E6Bridge6.lean:519-524). Large lam cannot help by itself: on-line
zeros contribute (x^2) e^{-2 lam x^2} ≥ 0 for every lam (Audit6_GaussShape.lean
`audit_gaussTest_real_axis_nonneg`, axiom-clean), so negativity must come from an off-line
zero dominating, which is the analytic content.

### GaussianTransfer (O1) and GaussianApprox (O1')

(a) O1 mentions zeros only through `zeroSide`; O1' mentions no zeros at all (test functions,
their Hermitian transforms on the strip, a uniform bound and pointwise convergence to
`gaussTest`). Neither mentions RH; neither is one-line equivalent to it: O1' is a Fourier
statement true regardless of where the zeros are. Automation fails: probe 6 with the constant
zero sequence fails at `Audit6_Obligations.lean:57:2` and `:60:33` (unsolved goals: the limit
must be `gaussTest c lam z`, not 0); refutation of O1 (probe 7) fails at line 71.

(b) Not trivially false. The target `gaussTest c lam` is genuinely a Hermitian transform shape:
Audit6_GaussShape.lean `audit_gaussTest_shape : gaussTest c lam z = h z * conj (h (conj z))`
with `h z = (z - c) exp(-lam (z - c)^2)`, axiom-clean. That h is the paper transform of
e^{-icu} times a Gaussian derivative (memo section 2; the Mathlib lemma it cites,
`integral_cexp_quadratic`, exists at Mathlib/Analysis/SpecialFunctions/Gaussian/
FourierTransform.lean:173). Truncation by a smooth cutoff gives Weil tests whose transforms
converge with a uniform strip bound; this is standard and RH-free. The Tendsto in O1 is to the
real part of a genuine sum (section 2(c)).

(c) `gaussianTransfer_of_approx : GaussianApprox → GaussianTransfer` is PROVED
(Tannery `tendsto_tsum_of_dominated_convergence` with the majorant m(ρ) C/(1+|gamma_ρ|^2)),
axiom-clean. So the live obligation is the zero-free O1'.

## 3. Reductions: PASS (every hypothesis load-bearing)

`#check` output: `weil_positivity_implies_rh_of : GaussianTransfer → GaussianDominance →
(∀ g, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re) → RiemannHypothesis`, and the primed form
with GaussianApprox in place of GaussianTransfer. Probes/Audit6_Reduction.lean:

- hpos deleted (author's proof text otherwise verbatim):
  `Audit6_Reduction.lean:15:4: error: failed to prove positivity/nonnegativity/nonzeroness`
  at the step `0 ≤ (weilForm (autocorr (g n))).re` that hpos supplied.
- hO2 deleted (centre Im ρ₀, lam 1, pair split, axis negativity, linarith):
  `Audit6_Reduction.lean:33:2: error: linarith failed to find a contradiction`; the goal state
  shows the pair term negative and the remainder tsum free, so positivity + transfer alone do
  not reach RH.
- hO1 deleted: `Audit6_Reduction.lean:43:8: error: Tactic rewrite failed` since
  `zeroSide (gaussTest c lam)` is not `weilForm (autocorr g)` for any Weil test g; positivity on
  the E8 class never reaches the Gaussian test without the transfer.
- aesop on (O1 ∧ O2 → RH): `Audit6_Reduction.lean:49:2: error: Tactic aesop failed, made no
  progress`.

The proof consumes hO2 (to get c, lam, hneg), hO1 (to get the approximants and hlim), hpos (for
hnn on each approximant), `weilForm_autocorr_eq_zeroSide` (to convert), `ge_of_tendsto'`
(limit of nonnegatives) and `linarith` (contradiction), then `rh_of_all_on_line` with the
strip lemma. Nothing else.

## 4. Mathematics: PASS, gaps between paper and Lean listed

Paper reduction (my own re-derivation):
1. For g Weil, autocorr g is Weil and the E8 formula gives weilForm (autocorr g) =
   Σ_ρ m(ρ) h(γ_ρ) conj(h(conj γ_ρ)), γ_ρ = (ρ - 1/2)/i. [Lean: weilKernel_autocorr,
   hasSum_weilForm_autocorr, weilForm_autocorr_eq_zeroSide.]
2. ρ ↦ 1 - conj ρ preserves nontrivial zeros and multiplicities, sends γ to conj γ, so the sum
   is real. [gammaOf_reflect, zeroMult_reflect on all of ℂ, zeroSide_conj via
   Equiv.tsum_eq + tsum_star, weilForm_autocorr_real.] Not on the path of the main theorem
   (it uses only `.re`), a supporting fact.
3. Positivity on the E8 class transfers to the Gaussian-derivative transform G_{c,lam} through
   approximants g_n: Re zeroSide(H_{g_n}) ≥ 0 for all n and → Re zeroSide(G), so
   Re zeroSide(G_{c,lam}) ≥ 0 for all c and lam > 0. [O1 as hypothesis; O1' → O1 proved by
   Tannery.]
4. An off-line zero forces some Re zeroSide(G_{c,lam}) < 0 (localisation at the argmax of
   y^2 - x^2 with generic centre, phase rotation in lam, tail by local count). [O2 as
   hypothesis; the file supplies the ingredients zeroSide_pair_split, gaussTest_axis,
   summable_gauss_zeroSide, gauss_zeroSide_pair_split but not the argmax/generic-centre/tail
   assembly.]
5. Contradiction; hence every strip zero is on the line; Mathlib's RH quantifies over zeros
   not trivial and not 1, which the functional equation puts in the strip. [strip_of_zero via
   riemannZeta_one_sub, Gamma_ne_zero, cos_eq_zero_iff, riemannZeta_ne_zero_of_one_le_re;
   rh_of_all_on_line.]

Gaps between the paper and the Lean text (none a defect):
- The Lean O2 does not tie c to ρ₀ and asks only for `.re < 0`; that is weaker than what the
  paper proof delivers (a specific centre near Im ρ₀ and a sequence lam_k), so any paper
  discharge fits the Lean statement.
- The Lean O1' requires the bound and convergence on the CLOSED strip |Im z| ≤ 1/2; zeros give
  |Im γ_ρ| < 1/2 strictly, so the closed strip is more than needed and harmless.
- Section G (pair split, axis value, summability) and section C (realness) are structure toward
  O2 and are not consumed by `weil_positivity_implies_rh_of`; the memo's ledger says so.
- I checked the paper O2 argument for soundness: Φ_c ≥ 0 needs |Im ρ - c| < 1/2 so only a
  finite window is involved (Zeta23 `ZeroConfig.finite_window`, `ZetaSeam.finite_window_holds`
  exist); ties between distinct ordinates occur at exactly one c each, so the bad set is finite;
  the maximiser has Φ_c = M > 0 hence is off the line; its pair term is 2 m |w|^2 e^{2 lam M}
  cos(2 arg w - 4 lam x y) with cos = -1 on the axis or along lam_k; the remainder is
  A e^{2 lam (M - eta)} + B for lam ≥ 1. The argument is correct on paper. The Lean
  formalisation of it is the memo's stated 400 to 700 lines and is NOT in the file.

## 5. Memo honesty: PASS

- Memo section 1: "proved MODULO two named analytic obligations ... no sorry anywhere; the
  obligations are `def : Prop` consumed only as hypotheses, never as instances or axioms."
  Verified (sections 1 and 3 above). "Every theorem in the file prints [propext,
  Classical.choice, Quot.sound]": verified 33/33.
- Grading: O2 is headed "the analytic heart" and O1' is "pure Fourier analysis"; section 4
  "Where the attack stopped" states precisely what was not started (argmax, generic centre,
  tail split, phase choice; Gaussian transform at complex argument, truncation-uniform
  integration by parts). Discharge plans are concrete: O2 steps (i) to (iv) naming
  `finite_window`, Finset argmax, `Summable.sum_add_tsum_compl` twice, monotonicity of
  e^{2 lam Φ}; O1' naming `integral_cexp_quadratic`, `ContDiffBump`, two integrations by parts,
  and what Zeta23 `norm_Hfn_le` does not give (uniformity in n). Both cited lemmas exist.
- No overclaim found. The file header's phrase that O2 "is far weaker than RH" is a judgment
  (O2 is implied by RH and is expected to be an unconditional theorem); it is accurate in that
  sense and the header immediately qualifies it. Section 5 of the memo says the integrator
  should add E6Bridge6 to defaultTargets and the guard; that has now been done.
- The memo's "Bombieri 2000, Thm 1" and "Weil 1952" citations were not checked against the
  papers; they are the standard references for this criterion.

## Probe inventory

- Probes/Audit6_Axioms.lean: 38 axiom prints, 3 #check/#print of the theorem types and
  obligation bodies.
- Probes/Audit6_Obligations.lean: 1 expected success (O2 from RH), 1 expected success (HasSum
  form of the Gaussian zero side), 9 expected failures (automation, pathological parameters,
  O2 alone → RH, refutations).
- Probes/Audit6_Reduction.lean: 4 expected failures (hpos / hO2 / hO1 deleted; aesop).
- Probes/Audit6_GaussShape.lean: 2 axiom-clean sanity theorems (gaussTest = h conj(h(conj z));
  real-axis nonnegativity).
- Probes/E6Bridge6_probe.lean is the author's own probe and was not relied on.
