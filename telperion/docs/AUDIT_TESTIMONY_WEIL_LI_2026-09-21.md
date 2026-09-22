# Audit testimony: E6Bridge15, B7 convergence half and the forward half of Li's criterion, 2026-09-21

THE CONVERGENCE HALF OF THE BOMBIERI-LAGARIAS EXPLICIT FORMULA AND THE FORWARD HALF OF LI'S
CRITERION; THE VALUE IDENTITY IS A NAMED OBLIGATION; NOT A PROOF OF THE RIEMANN HYPOTHESIS.
E6Bridge15 proves that the symmetric window sums of Li's kernel over the nontrivial zeros
converge to an absolutely convergent paired sum and are real; that under RH that limit has
nonnegative real part; and it states the rh node RH_bl_explicit_formula verbatim modulo one
`def : Prop`, `LiValue n`, the Bombieri-Lagarias value of the limit, which is not proved.
Nothing here bears on whether RH holds; Li's converse is neither on this island nor claimed.
conjecture1_proved = False.

Auditor: blind adversarial auditor (separate agent). Worktree /Users/peterwmurphy/arda-goal-weil,
island telperion/examples/rvm_bridge/lean, Lean v4.33.0-rc2, Zeta23 pinned at
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844. Artifact: E6Bridge15.lean (493 lines, namespace
RvMBridge15, `import E6Bridge6` only); memos WALL_WEIL_LI_DICTIONARY_2026-09-21.md and
B7_BL_EXPLICIT_FORMULA_DESIGN_2026-09-18.md. Probes: Probes/Audit15_Axioms.lean,
Probes/Audit15_Probes.lean. No git state changed; no other file edited.

Overall verdict: PASS. No defect found. The vocabulary is byte-identical to the registry; the
pairing, the real-part bound, the summable majorant and the Tannery passage are correct with
multiplicities matched under conjugation; the Tendsto is along atTop on ℝ as in the node; the Li
forward step is the on-line modulus identity; the obligation is honest and false at n = 0 exactly
as the node's 0 < n anticipates; nothing overclaims.

## 1. Kernel: PASS

`lake build`: `Build completed successfully (8851 jobs)` (a transient full-build failure was seen
once during the audit, from a newer module being edited concurrently; `lake build E6Bridge15`
alone succeeded at that moment with 3743 jobs, and the full build was green again on the next
run). E6Bridge15 in defaultTargets (lakefile line 9) and a lean_lib (line 139); guard carries 34
RvMBridge15 lines. Probes/Audit15_Axioms.lean prints axioms for all 41 declarations: 41 of 41
read `[propext, Classical.choice, Quot.sound]`, no sorryAx. Token grep for `sorry|admit|
native_decide|axiom|opaque|unsafe|implemented_by|extern|partial|set_option`: hits are the two
backticked `sorry` mentions in the header comment (lines 14, 38) and the words "partial fraction"
in comments (lines 34, 36, 439, 441); no code hit. No lemma claims the unpaired family summable
(grep for `Summable (liTerm` returns nothing).

## 2. Vocabulary: PASS

Python byte comparison of the `def` texts in `namespace BombieriLagarias` of
missions/rh/lean/Statements/RHDefs.lean against RvMBridge15.BombieriLagarias: `liKernel`,
`liZeroSum`, `archSide`, `zetaLogDerivReg`, `eta`, `finiteSide` all BYTE-IDENTICAL. The only
differences in the comment-stripped block are RHDefs's own `open Complex` line (E6Bridge15 opens
Complex at file level) and a header-comment fragment. The registry node
`bl_explicit_formula (n : ℕ) (hn : 0 < n) : Tendsto (BombieriLagarias.liZeroSum n) atTop
(𝓝 (BombieriLagarias.archSide n + BombieriLagarias.finiteSide n))` matches the file's
`bl_explicit_formula_of` (#check) with exactly one extra hypothesis, `LiValue n`.

## 3. The pairing: PASS

Window W_T = {0 < Re ρ < 1, |Im ρ| ≤ T}: `conj_mem_windowSet` (conj preserves Re and negates Im,
|·| absorbs the sign). Kernel: `liKernel_conj` from map_sub/map_one/map_pow/map_div₀. Multiplicity:
`zeroMult_conj` on all of ℂ: on a nontrivial zero both sides are `(analyticOrderAt ζ ·).toNat`
(`zeroMult_eq_of_strip`) and Zeta23 `analyticOrderAt_zeta_conj (hw : w ≠ 1)`
(ZetaReflect.lean:144-145) applies since Re ρ < 1; off the nontrivial zeros both sides vanish,
the zero condition moved across conj by Mathlib `riemannZeta_conj (s) : ζ (conj s) = conj (ζ s)`
(ZetaAsymp.lean:458), which has no hypothesis. So `liTerm_conj : liTerm n (conj ρ) = conj (liTerm
n ρ)`. finsum → tsum: `liZeroSum_eq_tsum_indicator` rewrites the finsum over W_T as the finite sum
over `windowSupport_finite` (⊆ `finite_zeros_window T` ⊆ Zeta23 `zetaSeam.finite_window (-T-1) T`)
and then as `tsum` of the indicator via `tsum_eq_sum`. Reindexing: `conjEquiv.tsum_eq` gives
Σ F = Σ F∘conj = Σ conj F, so 2 Σ F = Σ (F + conj F) = Σ 2·Re F (as complex,
`Complex.add_conj`), and cancelling 2 gives `liZeroSum_eq_tsum_paired`; `liZeroSum_im = 0` follows
by writing the paired indicator as a real coercion. Re-derived; correct, with multiplicities
matched termwise by `zeroMult_conj`.

## 4. The bound |Re K_n(ρ)| ≤ 2^n/|ρ|²: PASS

`liKernel_eq_sum`: K_n = -Σ_{m<n} C(n, m+1) (-1/ρ)^{m+1} (binomial theorem on (-1/ρ + 1)^n). For
m = 0 (j = 1): the real part is -n · Re(1/ρ) = -n Re ρ/|ρ|², and |·| ≤ n/|ρ|² because 0 < Re ρ < 1
(`h0`, `h1`); this is where pairing pays, since the unpaired term is ~ n/(iγ). For m ≥ 1 (j ≥ 2):
|Re| ≤ ‖(-1/ρ)^j‖ = |ρ|^{-j} ≤ |ρ|^{-2} using |ρ| ≥ 1 (`hρ`, `pow_le_pow_of_le_one`). Σ_j C(n,j) =
2^n - 1 ≤ 2^n (`sum_choose_succ_le`). Hence ≤ 2^n/|ρ|². Then `norm_liPaired_le_majorant`: for a
nontrivial zero with |Im ρ| ≥ 1, 2^n/|ρ|² ≤ (9/4) 2^n/(1 + |γ_ρ|²) because |ρ|² = Re² + Im² and
|γ_ρ|² = Im² + (1/2 - Re)² ≤ Im² + 1/4, so (1 + |γ|²) ≤ 5/4 + Im² ≤ (9/4) Im² ≤ (9/4)|ρ|² when
Im² ≥ 1; the |ρ| ≥ 1 hypothesis is supplied from |Im ρ| ≥ 1 via `Complex.abs_im_le_norm`. The
finitely many zeros with |Im ρ| < 1 are absorbed: `liBound` adds the indicator of the finite set
`finite_zeros_small` (⊆ `finite_zeros_window 1`) times ‖liPaired‖ to the local-count majorant, and
`summable_liBound` is `summable_of_ne_finset_zero` + E6Bridge6 `summable_mult_div_one_add_normSq`.
`norm_liPaired_le` covers the three cases (small ordinate, large ordinate, non-zero).

## 5. Tannery: PASS

`liZeroSum_tendsto`: after `liZeroSum_eq_tsum_paired`, `tendsto_tsum_of_dominated_convergence
(summable_liBound n)` with pointwise limits (for a strip point, the indicator equals liPaired once
T ≥ |Im ρ|, `eventually_atTop`; off the strip both are 0) and domination
`norm_indicator_le_norm_self` then `norm_liPaired_le`. The filter is `atTop` on ℝ: `#check
liZeroSum : ℕ → ℝ → ℂ` and `liZeroSum_tendsto : Tendsto (liZeroSum n) Filter.atTop (nhds
(liLimit n))`, the same as the node's `Tendsto (liZeroSum n) atTop (𝓝 ...)` (probe 5 consumes the
node's shape with `(atTop : Filter ℝ)` explicitly).

## 6. Li forward: PASS

`norm_one_sub_inv_of_on_line`: 1 - 1/ρ = (ρ - 1)/ρ and, with Re ρ = 1/2, |ρ - 1|² = (Re - 1)² +
Im² = 1/4 + Im² = |ρ|²; my own `audit_on_line_modulus : Re ρ = 1/2 → normSq (ρ - 1) = normSq ρ`
is axiom-clean. Then Re K_n = 1 - Re(w^n) ≥ 1 - ‖w‖^n = 0 with ‖w‖ = 1 (`Complex.re_le_norm`),
times m ≥ 0; non-zeros give liPaired = 0 (`liPaired_eq_zero_of_not_nontrivial`). So
`rh_implies_liZeroSum_re_nonneg` (every window) and `rh_implies_liLimit_re_nonneg` (the limit) by
`Complex.re_tsum` + `tsum_nonneg`. RH enters only through `RH_implies_on_line`.

## 7. Obligation honesty: PASS

`LiValue (n) : Prop := liLimit n = archSide n + finiteSide n` (#print), consumed only by
`bl_explicit_formula_of`. `liLimit n` is a genuine absolutely convergent sum (`summable_liPaired`),
so the identity is between honest numbers. At n = 0: liLimit 0 = Σ' m · Re(1 - 1) = 0;
archSide 0 = 1 - 0 + (empty sum) = 1; finiteSide 0 = -(empty sum) = 0; so LiValue 0 is 0 = 1,
false. My own `audit_liValue_zero_false : ¬ LiValue 0` is axiom-clean, confirming the node's
0 < n is load-bearing. Automation neither proves nor refutes LiValue 1 (`Audit15_Probes.lean:55:50`
and `:56:52: simp made no progress`); the node without LiValue does not follow from the
convergence half (`52:2: error: Type mismatch`); the unpaired family cannot be shown summable
(`47:2: exact? could not close the goal`). The memo is explicit that the value half needs the
global Hadamard/xi'/xi partial fraction with its constant, which Zeta23 lacks (its
`zeta_logDeriv_partial_fraction` is Landau's local form), and the B7 design memo's "symmetric
order is necessary" (section 2.1) is what the pairing realises.

## 8. Overclaim: PASS

Grep over E6Bridge15.lean and the dictionary memo (prove(s/d) RH/Riemann, RH is/holds/proved,
progress toward, goal node proved, conjecture1_proved = True, Li's criterion proved, converse
proved): the only hits are the two disclaimer sentences, file line 47 "conjecture1_proved =
False. Nothing here says anything about whether RH holds." and memo line 14 "Nothing here bears
on whether RH holds; the converse of Li's criterion is not on this island and is not claimed."
The memo's "Deliverable (B) status" states plainly that the Li-Gaussian equivalence through RH is
not claimed. No wording says more.

## Probe inventory

- Probes/Audit15_Axioms.lean: 41 axiom prints, 3 #check, 1 #print.
- Probes/Audit15_Probes.lean: `audit_liValue_zero_false`, `audit_on_line_modulus` (axiom-clean);
  conjugation-closure, kernel-conj, zeroMult_conj, j = 1 real part, node-shape consumption with
  `(atTop : Filter ℝ)` (all elaborate); 4 expected failures (unpaired summable; node without
  LiValue; LiValue 1 and its negation by simp).
- Python: byte comparison of the six mirrored definitions.
- Probes/E6Bridge15_probe.lean and E6Bridge15_obligation_probe.lean are the author's own and were
  not relied on.
