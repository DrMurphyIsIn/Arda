# Route C (de Bruijn-Newman) synthesis, 2026-09-23

Snapshot: worktree `arda-routec-syn`, HEAD `b524f7e7d` ("grant(rh): RH_dbn_debruijn_real_zeros -> PROVED").
Island: `telperion/examples/dbn/lean/` (21 modules, 6140 lines, Lean `v4.34.0-rc1`, Mathlib `de5ce8a9`
via the pinned `LiCriterion` dependency `nicholasbulka/li-criterion-rh-equivalence-lean@35df682f`).
Sources: the Route C inventory and frontier reports of 2026-09-23, committed verbatim at
`telperion/docs/research/route_c_2026-09-23/{INVENTORY,FRONTIER}_REPORT.md`. Figures that rest only on
those reports (not on a repo artifact or a published source) remain marked "unanchored estimate" below. File:line anchors below were checked against this HEAD in
review. The build and axiom-guard figures in §3 were re-run at this HEAD on 2026-09-23.

---

## 0. Status

```
+-----------------------------------------------------------------------------------+
| conjecture1_proved = False.                                                       |
| Route C does NOT prove RH. It rewrites RH as "every zero of H_0 is real"          |
| (classically Λ <= 0) and proves only the known half, de Bruijn's t >= 1/2.        |
+-----------------------------------------------------------------------------------+
```

**Four registry nodes are proved.** Each `.toml` records `status="proved"`, `closure_clean=true` and
`via="direct"`, and each has two blind audits. Statements are in
`telperion/missions/rh/lean/Statements/*.lean`.

| Node | Roadmap id | Artifact | depends_on | Granted |
|---|---|---|---|---|
| `RH_dbn_H0_eq_xi` | C2 | `DBNXi.lean:41` `dbn_H0_eq_xi` | `[]` | 2026-09-22 (`8c94ac446`) |
| `RH_dbn_H0_zero_strip` | (new, C3 base) | `DBNStrip.lean:499` `dbn_H0_zero_strip` | `[]` | 2026-09-22 (`8c94ac446`) |
| `RH_dbn_rh_iff_H0_real_zeros` | C4 | `DBNRealZerosIffFinal.lean:33` | `RH_dbn_H0_eq_xi` | 2026-09-22 (`8c94ac446`) |
| `RH_dbn_debruijn_real_zeros` | C3 | `DBNHadamardApprox.lean:97` | `RH_dbn_H0_zero_strip` | 2026-09-23 (`b524f7e7d`) |

**What Route C establishes, all hypothesis-free, each closure within `[propext, Classical.choice, Quot.sound]`:**

1. `H_0(z) = (1/8) ξ(1/2 + iz/2)` for every complex z (C2).
2. Every zero of H_0 satisfies `(Im z)^2 <= 1` (strip).
3. RH (strip form, over Mathlib's `riemannZeta`) is equivalent to "every zero of H_0 is real" (C4).
   This is an equivalence and proves neither side.
4. For every `t >= 1/2`, every zero of H_t is real (C3, de Bruijn 1950). The island also proves the
   stronger quantitative form `H_zero_im_sq_le`: for all `t >= 0`, zeros of H_t satisfy
   `Im^2 <= max(1 - 2t, 0)` (`DBNHadamardApprox.lean:83`).
5. Along the way, an even-case Hadamard factorisation for entire functions of order < 2
   (`DBNHadamard.lean:321`) and a zero-free Hurwitz theorem (`DBNHurwitz.lean:36, :116`).
   HADAMARD_PLAN §2 (`HADAMARD_PLAN_2026-09-23.md:29-31`) records no Hadamard/Weierstrass
   factorisation in Mathlib at the pin or on master (checked 2026-09-23). The C3 design memo §3.1
   ("Absent", `DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md:289-292`) records no Hurwitz
   theorem, Rouché or argument principle; that was a grep of the pinned `de5ce8a9` copy only
   (pin only; master unchecked).

**What Route C does NOT establish.**

- Λ is not defined anywhere on the island. This is deliberate, to avoid the sInf trap
  (`DBN_FOUNDATIONS_C2C4_2026-09-17.md` §5; `DBNDefs.lean` header :12-14). So no theorem says
  "Λ <= 1/2". The proved form is the sInf-free one, verbatim from
  `Statements/RH_dbn_debruijn_real_zeros.lean:5`:
  `∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0`.
- The up-set property (real zeros at t0 implies real zeros for all t >= t0) is not built. Neither is
  a lower bound for Λ (Newman / Rodgers-Tao / Dobner).
- No bound below 1/2, effective or ineffective, is formalized.
- **Λ <= 0 is RH.** It is the program's wall (roadmap C10, `RH_ROUTES_ROADMAP_2026-09-16.md:225`),
  and nothing here moves it.

---

## 1. The route in one page

**Objects** (`DBNDefs.lean`):

- `Φ(u) = Σ_n (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})` is the Polymath15 kernel (`:211`), a
  `tsum` over `ℕ+`. The theta moments (`thetaMoment`, `:40`) feed the C2 kernel g. Φ is even
  (`Φ_neg`, `:261`) and decays double-exponentially (`abs_Φ_le`, `:300`).
- `H t z := ∫_{Ioi 0} e^{tu²} Φ(u) cos(zu) du` (`:413`). It is entire in z
  (`hasDerivAt_H`/`differentiable_H`, `:520, :566`), even (`H_neg`, `:442`) and real on the real axis
  (`H_ofReal_im`, `:460`).
- Classically, `Λ := inf{t : H_t has only real zeros}`. That definition is **not** in the kernel.

**The two chains.** They share only `DBNDefs`: C3 does not import `DBNXi`.

- **C2 -> C4.** C2 identifies H_0 with ξ at `s = 1/2 + iz/2`. The map sends Im z = 0 exactly to
  Re s = 1/2 (`xiArg_re`, `DBNRealZerosIff.lean:54`). Upstream
  `LiCriterion.xi_zeros_are_nontrivial_zeros` says ξ vanishes exactly at the nontrivial zeta zeros
  (`DBNRealZerosIff.lean:80`). Together these give RH <=> H_0 has only real zeros.
- **Strip -> C3.** The ξ strip gives `Im^2 <= 1` at t = 0, and it is proved *without* C2, from a
  half-plane identity with ζ on Re s > 1. De Bruijn's heat flow then contracts `Im^2` at rate 2 per
  unit t, so `Im^2 <= max(1 − 2t, 0)`, and at t >= 1/2 all zeros are real.

**Registry node DAG:**

```
  RH_dbn_H0_eq_xi (C2) ----------------> RH_dbn_rh_iff_H0_real_zeros (C4)
     H_0 = ξ(1/2+iz/2)/8                    RH  <=>  (H_0 z = 0 -> Im z = 0)

  RH_dbn_H0_zero_strip ----------------> RH_dbn_debruijn_real_zeros (C3)
     H_0 z = 0 -> Im^2 <= 1                 t >= 1/2 -> (H_t z = 0 -> Im z = 0)

  [not registered]  C10 wall:  forall t >= 0, H_t z = 0 -> Im z = 0   (= Λ <= 0 = RH)
```

The roadmap had C3 depending on C2 and C4 depending on C2 and C3
(`RH_ROUTES_ROADMAP_2026-09-16.md:218-219`). The registry differs in two ways, with different
histories:

- C3 edges. The C3 design memo §6 items 1-2
  (`DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md:388-398`) recommend dropping the C3 -> C2 edge
  and adding `RH_dbn_H0_zero_strip` as C3's dependency. Commit `d806cb1a3` (2026-09-22) made that
  change: `depends_on` went from `["RH_dbn_H0_eq_xi"]` to `["RH_dbn_H0_zero_strip"]`.
- C4 edges. C4 has never depended on C3 in the registry. Its `depends_on` has been
  `["RH_dbn_H0_eq_xi"]` since registration in `a39bf8b93` (2026-09-17). The memo does not
  address this edge.

**Lean module DAG** (`A -> B` means B imports A; Mathlib omitted):

```
C2 / C4 chain
  DBNDefs -> DBNXiRiemann ----+
  DBNDefs -> DBNGKernel ------+--> DBNXiCos --+
             DBNGKernel ---------> DBNXiIBP --+--> DBNXi                      [C2 anchor]
  DBNDefs -> DBNRealZerosIff --+
  DBNXi -----------------------+--> DBNRealZerosIffFinal                     [C4 anchor]

C3 chain (does not import DBNXi)
  DBNDefs -> DBNStrip                                                        [strip anchor]
  {DBNDefs, DBNStep, DBNHurwitz} -> DBNHeatApprox -> DBNDeBruijnReduction
  {DBNStep, DBNHadamardCount, DBNHadamardProduct,
   DBNHadamardMean, DBNHadamardLinear} -> DBNHadamard
  {DBNHadamard, DBNDeBruijnReduction, DBNStrip} -> DBNHadamardApprox         [C3 anchor]

Other: DBNStep -> DBNStepControls; AxiomGuardDBN imports all 20 modules.
Mathlib-only: DBNStep, DBNHurwitz, DBNHadamard{Count,Product,Mean,Linear}.
```

---

## 2. How each node was proved

### C2: `dbn_H0_eq_xi` (`DBNXi.lean:41-51`, 1234 lines across modules A-E)

The assembly is a single `linear_combination` over five modules.

- **A. Riemann's symmetric integral** (`DBNXiRiemann.lean`).
  - `weakFEPair_Λ₀_eq` (`:156`) holds for any `WeakFEPair`. It takes Mathlib's Mellin convergence
    of `f_modif` (via `isStrongFEPair_toStrongFEPair`) and splits it into `Ioi 1` and `Ioo 0 1`
    pieces. The `Ioo 0 1` piece is inverted at the Mellin level (`mellin_comp_inv`,
    `mellin_cpow_smul`) using the functional equation.
  - `completedRiemannZeta₀_eq_integral_psi` (`:245`) then gives
    `Λ₀ s = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{(1−s)/2−1})` for every s. Here ψ is `psi` (`:48`) and
    `evenKernel_zero_eq_thetaMoment` is at `:100`.
- **B. Substitution** (`DBNXiCos.lean`).
  - `integral_Ioi_one_eq_integral_exp_four_mul` (`:76`) substitutes `x = e^{4u}` through
    `integral_image_eq_integral_abs_deriv_smul`.
  - `completedRiemannZeta₀_half_add_eq` (`:127`): `Λ₀(1/2 + iz/2) = 8 ∫_0^∞ g(u) cos(zu) du`.
- **C. Kernel calculus** (`DBNGKernel.lean`, 65 theorem/lemma declarations by grep).
  - `g = e^u (θ₀ − 1)/2` (`:135`), with closed-form g′ and g″ (`:138, :143`). These come from the
    termwise `hasDerivAt_thetaMoment`, so no C2 module (A-E) interchanges a tsum with an integral.
    (DBNStrip does: see L1c below.)
  - `g''_sub_g_eq`: g″ − g = 8Φ (`:214`).
  - `g'_zero`: g′(0) = −1/2 (`:221`), from the twice-differentiated theta functional equation.
- **D. Two integrations by parts** (`DBNXiIBP.lean`). These use
  `integral_Ioi_mul_deriv_eq_deriv_mul`. `integral_g_cos_eq` (`:81`) gives
  `(z²+1) ∫ g cos = 1/2 − 8 H_0(z)`.
- **E. Assembly.** At `s = 1/2 + iz/2`, `s(s−1) = −(z²+1)/4`, so `ξ = −(z²+1)J + 1/2 = 8 H_0`.
  The corollary `H_zero_I` (`DBNXi.lean:55`) gives H(0, i) = 1/16.

### Strip: `dbn_H0_zero_strip` (`DBNStrip.lean:499`, C2-free)

The import closure is {DBNDefs, Mathlib, Lc Basic} (strip A2 import walk).

- **L1a.** Evenness of Φ folds H_0 into `(1/2) ∫_ℝ Φ e^{izu}` (`H_zero_eq_half_integral`, `:210`).
- **L1b.** A termwise whole-line Gamma integral, `integral_cexp_mul_exp_neg_exp` (`:71`) and
  `integral_expTerm` (`:293`), valid for Im z < −1.
- **L1c.** Tonelli gives the bound `O(n^{(Im z − 1)/2})` (`summable_integral_norm_expTerm`, `:381`).
  Then the Fubini-Tonelli interchange `hasSum_integral_of_summable_integral_norm` (`:419`) gives
  `H_0 = (1/16) s(s−1) π^{−s/2} Γ(s/2) ζ(s)` on Im z < −1, i.e. Re s > 1 (`H_zero_eq_of_im_lt`,
  `:448`).
- **L1d.** No factor vanishes there (`riemannZeta_ne_zero_of_one_lt_re`, Γ ≠ 0). `H_neg` reflects
  this to Im z > 1 (`H0_zero_strip` `:482`, `H0_ne_zero` `:489`).

### C4: `dbn_rh_iff_H0_real_zeros` (`DBNRealZerosIff.lean:54-138`, `DBNRealZerosIffFinal.lean:26-36`)

- The coordinate lemmas `xiArg_re`, `xiArg_re_eq_half_iff`, `xiArg_surj` and `xiArgInv_im` are at
  `:54-70`, with inverse `s ↦ −2i(s − 1/2)`.
- `riemannXi_eq_zero_iff_strip_zero` is at `:80`. The conditional bridge
  `dbn_rh_iff_H0_real_zeros_of_H0_eq_xi (hC2)` is at `:116`.
- `Final` discharges `H0EqXi` with `H0EqXi_holds` (`:26`, from `dbn_H0_eq_xi`).

### C3: `dbn_debruijn_real_zeros` (`DBNHadamardApprox.lean:97`; 3,695 lines across the 12 C3 modules, strip and Controls included)

- **Discrete heat step** (`DBNStep.lean`, Mathlib-only).
  - `shiftAvg δ f z = (f(z+iδ) + f(z−iδ))/2` (`:51`).
  - `EvenHadamardData` (`:119`) packages `f = c z^{2m} ∏(1 − z²τ_k²)`.
  - `shiftAvg_zero_im_sq_le` (`:401`) takes f real on the real axis, with even Hadamard data and
    zeros in `Im^2 <= Δ2`. Its conclusion is that zeros of `T_δ f` satisfy
    `Im^2 <= max(Δ2 − δ², 0)`. The mechanism: each factor `‖1 − z²τ²‖·‖1 − z²τ̄²‖` is strictly
    larger at `w + iδ` than at `w − iδ` when `y² + δ² > Δ2`, so the two shifts cannot cancel.
  - The iterate `zero_im_sq_le_of_shiftAvg_iterate` (`:459`) gives `max(Δ2 − Nδ², 0)`, generically
    in the family F.
  - Controls (`DBNStepControls.lean`): `step_bound_attained` (`:72`, the bound is sharp on 1+z²) and
    `step_needs_reality` (`:132`, the bound fails for z²−2i, so reality is load-bearing).
- **Heat approximants** (`DBNHeatApprox.lean`).
  - `Gδ δ N z := ∫ cosh(δu)^N Φ(u) cos(zu)` (`:123`) and `G t N := Gδ(√(2t/N)) N` (`:127`).
    Multiplication by cosh(δu) on the kernel side is `T_δ` on the function side, so
    `Gδ_succ`/`Gδ_eq_iterate` (`:187, :202`) give `G t N = T_δ^N H_0` with `Nδ² = 2t`.
  - Growth of order <= 3/2: `norm_Gδ_le_exp_rpow_norm` (`:355`).
  - Convergence: `tendstoUniformlyOn_G` on horizontal strips (`:485`) and
    `tendstoLocallyUniformly_G` (`:494`).
  - Nonvanishing at 0: `Φ_pos` (`:551`) gives `Gδ_zero_re_pos` (`:590`) and `H_zero_ne_zero` (`:583`).
- **Hurwitz** (`DBNHurwitz.lean`, Mathlib-only). `hurwitz_ne_zero` (`:36`) is proved by maximum
  modulus. `hurwitz_ne_zero_of_entire` is at `:116`.
- **Reduction** (`DBNDeBruijnReduction.lean`). The two obligations are stated as Props,
  `H0ZeroFreeOffStrip` (`:41`) and `ApproxHadamard` (`:45`), with the conditional conclusions at
  `:57, :94, :107`.
- **Hadamard factorisation (PR #608)**, genus 0 in the variable z². Capstone
  `evenHadamardData_of_order_lt_two` (`DBNHadamard.lean:321`): if f is entire, even, not
  identically 0, and satisfies `‖f z‖ ≤ A e^{B‖z‖^ρ}` with `1 ≤ A`, `0 ≤ B` and `0 < ρ < 2`
  (`DBNHadamard.lean:321-324`), then `Nonempty (EvenHadamardData f)`. Five files, 1589 lines:
  - **Count** (`DBNHadamardCount.lean`): `zeroCount` (`:58`). `summable_zero_multiplicity_rpow`
    (`:220`) shows `Σ ord_s(f) ‖s‖^{−p} < ∞` for p > ρ, under the same `1 ≤ A`, `0 ≤ B`, `0 < ρ`
    hypotheses (`:220-222`), via Jensen plus dyadic summation.
  - **Product** (`DBNHadamardProduct.lean`): `evenProduct τ z := ∏'(1 − z²τ_k²)` (`:117`). It is
    entire (`:121, :125`), with growth `norm_evenProduct_le` (`:196`), zero set
    `evenProduct_eq_zero_iff` (`:235`) and orders `analyticOrderNatAt_evenProduct` (`:330`).
  - **Mean** (`DBNHadamardMean.lean`): `exists_exp_eq_of_ne_zero` (`:37`) says a zero-free entire
    function is `exp ∘ H`. `circleAverage_abs_re_le` (`:121`) is Jensen in the mean. It replaced the
    memo's minimum-modulus lemma, so no exceptional circles are needed.
  - **Linear** (`DBNHadamardLinear.lean`): `eq_linear_of_circleAverage_abs_re_le` (`:152`). If the
    circle average of |Re H| grows with exponent < 2, then H is affine (via Poisson,
    Borel-Carathéodory and Cauchy). Evenness then removes the linear term.
  - **Assembly** (`DBNHadamard.lean`): representative-zero indexing `IsRep`/`RepZero`/`ZeroIdx`/
    `repSeq` (`:114-173`).
- **Closure** (`DBNHadamardApprox.lean`).
  - `norm_Gδ_le_growth` (`:30`) supplies the order-3/2 bound, which feeds
    `approxHadamard : ApproxHadamard` (`:70`).
  - `H0ZeroFreeOffStrip_holds` (`:77`) comes from the strip.
  - Locally uniform convergence plus Hurwitz on the open set {Im² > max(1−2t, 0)} give
    `H_zero_im_sq_le` (`:83`).
  - At t >= 1/2 this forces Im z = 0: `H_ne_zero_of_half_le` (`:88`) and `dbn_debruijn_real_zeros`
    (`:97`).

---

## 3. Verification record

**Audits.** There are two blind audits per node, eight files in all:
`telperion/docs/AUDIT_TESTIMONY_RH_dbn_<node>_<date>_{A1,A2}.md`. Every one records `pass: true`,
`axioms_clean: true` and `statement_byte_identical: true` (whitespace-normalised).

| Node | Audit | Key independent checks |
|---|---|---|
| H0_eq_xi | A1 | mpmath at 30 digits, with Λ₀ computed two ways: (M) Mathlib's Mellin form and (C) Γζ + 1/s + 1/(1−s). Points z = i, 2+i, 10−0.7i, 3.5+0.25i, 28.2694. Absolute difference ≤ 5.3e-28 for (M) and ≤ 4.8e-32 for (C) (:158-164). H_0(i) − 1/16 = 0 to 30 digits. Vocabulary mirror: the RHDefs `DBN` block contains DBNDefs :40-41, :211-214, :408-409 and :413 verbatim (:70-79). |
| H0_eq_xi | A2 | mpmath at 25 digits: differences 0, 3.2e-28 and 1.8e-27 at i, 0.7+0.4i and 5−1.2i (:144-146). The identity riemannXi = s(s−1)Λ/2 holds to 7e-27 (:152). The gate rejects a mutation weakening the conclusion with `∨ True` (:66-67). |
| H0_zero_strip | A1 | Half-plane identity at −2i, 3−1.5i and −7.25−3.1i, with relative differences 0, 7.7e-32 and 2.2e-31 (:142-144). Both theorems are root-namespace (:50). |
| H0_zero_strip | A2 | Absolute differences 0, 4.6e-33 and 1.5e-32. Φ(u) − Φ(−u) ≈ 1e-41 (:90). The import closure is {DBNDefs, Mathlib, `Lc.LiCriterion.Basic`} (:46-47, :135), so it includes LiCriterion's Basic module. The constant walk (:67-70, :138-139) found no C2 constant and no LiCriterion constant. The hardened gate rejected two mutations. |
| rh_iff | A1, A2 | No numerics. A1 checks the convention against Titchmarsh's Φ_T and the algebra s(s−1) = −(z²+1)/4 (A1 :61-69). A2 checks `pp.fullNames` elaboration: `riemannZeta` is Mathlib's and `H` is `DBN.H`, so there is no shadowing (A2 :66-68). A2 also derives the strip form from Mathlib's `RiemannHypothesis`, one direction only (:136, :181). |
| debruijn | A1 | mpmath at dps 40 (:57-66). H_0 = ξ/8 to 12 digits at 4 points. Winding number for H_{1/2} is 0 on both off-axis boxes, with minimum \|H\| on the boundary 8.7e-10. Controls: a planted zero gives winding 1, and a thin axis box gives 3 at both t = 0 and t = 1/2. H_0 zeros equal 2γ_k (k = 1..3) to 1e-36. |
| debruijn | A2 | 1536-node Gauss-Legendre quadrature (:59-73). ξ/8 relative error ≤ 1e-35. H_0 zeros in [0, 62] equal 2γ_1..2γ_4 to 7e-34. H_{1/2} real zeros at 27.980, 41.668, 49.728 and 60.379. Winding 0 on [0,60]×[0.1,1], [0,60]×[−1,−0.1] and [0,60]×[0.02,3]. Controls give 1, 3 and 3. |

The numerics are evidence about the statements, not part of the proof. The proof is the kernel check.

**Axioms and build** (re-run in review at this HEAD on 2026-09-23; re-runnable):

- `leanlock.sh lake build --no-build` reports "All targets up-to-date (8759 jobs)".
- `lake env lean AxiomGuardDBN.lean` prints 325 `#print axioms` lines. Every one is exactly
  `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` and no "does not depend".
- The guard covers 321 distinct top-level theorem/lemma names, with 0 missing and no `private`
  declarations.
- A grep for `sorry|admit|axiom|opaque|native_decide|implemented_by|extern|unsafe` as declarations
  or tactics finds nothing, so the island has no `sorry`.
- None of the four registry theorems carries a hypothesis. Every named Prop obligation on the island
  is discharged: `H0EqXi` (`Final:26`), `H0ZeroFreeOffStrip` (`DBNHadamardApprox:77`) and
  `ApproxHadamard` (`:70`).

**Gate pre-flights** (in the audits):

- `V._normalized_statement`, `V.statement_matches` and `V.artifact_incompleteness_markers` all
  return `[]` over each import closure.
- `telperion.cli mission verify rh` reports `verify [rh]: OK`.
- `telperion/scripts/guard_anchors.py --island dbn`, run under python3.12, reports that all 4 proved
  anchors print within the 3 axioms.

**CI.** Job `dbn-compiles` (`.github/workflows/telperion-lean-e2e.yml:2465-2525`) runs four checks:

1. a no-`sorry` grep
2. `lake build`
3. the axiom guard, with a floor of >= 30 lines, a `sorryAx` check and a 3-axiom subset check
4. `guard_anchors.py --island dbn`

The job is in main's `required_status_checks`. However, `enforce_admins.enabled = false`, so admins
can bypass it.

**Trust boundary.**

1. **Registry vs island definitions.** Registry `DBN.H` is a textual copy
   (`Statements/RHDefs.lean:97-116`), not a shared import. The link is the statement gate plus the
   auditors' line-for-line mirror check.
2. **Upstream code.** `LiCriterion.riemannXi` and `xi_zeros_are_nontrivial_zeros` come from the
   pinned external repo. Their axioms are inside the 3-axiom closure, but the code is not
   Arda-audited, beyond the rh_iff audits re-deriving the ξ normalisation.
3. **Lean kernel and Mathlib `de5ce8a9`.**

---

## 4. Reusable assets and upstream candidates

**For further Route C work:**

- **The quantitative contraction** `H_zero_im_sq_le` (`DBNHadamardApprox.lean:83`). It is stronger
  than the registry node, but its base strip is hardcoded to Δ2 = 1 through `H0ZeroFreeOffStrip`
  (`DBNDeBruijnReduction.lean:41, :94`).
- **The generic step and iterate** (`DBNStep.lean:401, :459`), generic in F and Δ2. Together with
  `evenHadamardData_of_order_lt_two` for any even entire function of order < 2, these are the direct
  route to the parametric de Bruijn theorem and the up-set property (M1 below).
- **Approximants and convergence:** `Gδ_eq_iterate`, `tendstoLocallyUniformly_G`, `Φ_pos`,
  `H_zero_ne_zero` (every t), `H_conj` (`DBNStrip.lean:232`), `differentiable_H` and `hasDerivAt_H`.
- **Bridges between the ζ side and the H side:** `H_zero_eq_of_im_lt` (`DBNStrip.lean:448`) and
  `dbn_H0_eq_xi`.
- **`DBNStepControls.lean`**, a template for kernel-checked positive and negative controls.

**Mathlib candidates.** These modules import only Mathlib: Count, Product, Mean, Linear, Hurwitz and
Step. None of them imports Φ, H or ζ, so they are the cleanest candidates.

| Candidate | Anchor | Gap in Mathlib (as recorded) |
|---|---|---|
| Even / order-< 2 Hadamard factorisation | `DBNHadamard.lean:321` plus Count/Product/Mean/Linear | HADAMARD_PLAN §2: no Hadamard/Weierstrass factorisation at the pin or on master as of 09-23 |
| Convergence exponent of zeros | `DBNHadamardCount.lean:220` | part of the above |
| Borel-Carathéodory in the mean (mean \|Re H\| of exponent < 2 forces H affine) | `DBNHadamardLinear.lean:152` | part of the above |
| Jensen in the mean | `DBNHadamardMean.lean:121` | part of the above |
| Hurwitz, zero-free form | `DBNHurwitz.lean:36` | C3 memo §3.1 "Absent" (`DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md:289-292`): no Hurwitz, Rouché or argument principle. Pin `de5ce8a9` only; master unchecked |
| Riemann's symmetric integral for any `WeakFEPair` | `DBNXiRiemann.lean:156, :245` | not recorded as missing; needs a check against master |
| Whole-line Gamma integral; `x = e^{4u}` substitution | `DBNStrip.lean:71`; `DBNXiCos.lean:76` | small lemmas; needs a check against master |

There is an overlap to resolve first. The `examples/borel_caratheodory` island has
`borel_caratheodory_value` and `borel_caratheodory_deriv_family`
(`examples/borel_caratheodory/lean/BorelCaratheodory.lean:236, :309`), while
`DBNHadamardLinear` uses Mathlib's Borel-Carathéodory (header :9-10). One version should be chosen
before anything goes upstream.

---

## 5. The frontier

### 5.1 Λ-bound history

Citations were verified via Crossref and arXiv full text in the (uncommitted) frontier report, and
re-checked in review against Crossref and arXiv:1904.12438, arXiv:2004.09765 and arXiv:2005.05142.

| Bound | Authors | Year | Method |
|---|---|---|---|
| Λ ≤ 1/2 | de Bruijn, Duke Math. J. 17(3) 197-226 | 1950 | Heat-flow strip contraction (P15 Thm 3.2, citing de Bruijn Thm 13) plus the ξ strip. **Formalized here in sInf-free form** (`dbn_debruijn_real_zeros`); Λ itself is not defined on the island. |
| −∞ < Λ ≤ 1/2; conjectures Λ ≥ 0 | Newman, Proc. AMS 61(2) 245-251 | 1976 | Existence of the threshold constant |
| Λ ≥ −50 | Csordas, Norfolk, Varga, Numer. Math. 52 | 1988 | (Rodgers-Tao Table 1) |
| Λ ≥ −5 | te Riele, Numer. Math. 58 | 1991 | (RT Table 1) |
| Λ ≥ −0.0991 | Csordas, Ruttan, Varga, Numer. Algorithms 1 | 1991 | Laguerre inequalities |
| Λ ≥ −0.385 | Norfolk, Ruttan, Varga | 1992 | (RT Table 1) |
| Λ ≥ −5.895e-9 | Csordas, Odlyzko, Smith, Varga, ETNA 1 | 1993 | Lehmer pairs, CSV repulsion |
| Λ ≥ −4.379e-6 | Csordas, Smith, Varga, Constr. Approx. 10 | 1994 | Lehmer pairs, CSV repulsion |
| Λ ≥ −2.63e-9 | Odlyzko, Numer. Algorithms 25 | 2000 | Lehmer pairs, CSV repulsion |
| Λ < 1/2 | Ki, Kim, Lee, Adv. Math. 222(1) 281-306 | 2009 | Large-x asymptotics of H_t at fixed t > 0. Ineffective. The paper is paywalled and its strictness step was not read. |
| Λ ≥ −1.15e-11 | Saouter, Gourdon, Demichel, Math. Comp. 80 2281-2287 | 2011 | Lehmer pairs, CSV repulsion |
| Λ ≤ 0.22 | D.H.J. Polymath, Res. Math. Sci. 6(3) art. 31 (arXiv:1904.12438) | 2019 | Thm 1.2 barrier criterion with t0 = y0 = 0.2 and X ≈ 6·10^10. Hypothesis (i) is RH to 3.06·10^10 from Platt, Math. Comp. 86 (2017). |
| Λ ≥ 0 | Rodgers, Tao, Forum Math. Pi 8 e6 | 2020 | Assume Λ < 0: zero dynamics force local equilibrium, which contradicts Montgomery pair correlation |
| Λ ≥ 0 (second proof) | Dobner, Acta Arith. 201 29-62 | 2021 | Dirichlet-series approximation of ξ_t for t < 0; uses no zeta-zero input |
| Λ ≤ 0.2 | Platt, Trudgian, Bull. LMS 53(3) 792-797 (arXiv:2004.09765 §3.4, Cor. 2) | 2021 | RH to 3·10^12 fed into P15 Table 1 row 2 (t0 = 0.186, y0 = 0.16733) |

The table is ordered by year. For lower bounds, publication order and the size of the bound do not
agree.

Excluded as anchors: the 2026 unreviewed claims (Gomila Λ ≤ 0.1787854; Gordon Λ < 0.158), from
`RH_ROUTES_ROADMAP_2026-09-16.md:198-202`, which were not re-checked. Since Rodgers-Tao, RH <=> Λ = 0,
so the upper side has no slack.

**P15's criterion.** Two statements, quoted from arXiv:1904.12438 (math transcribed to plain
text; z = x + iy).

*Theorem 1.2 (Upper bound criterion), p.2.* "Suppose that t0, X > 0 and 0 < y0 ≤ 1 obey the
following hypotheses:

- (i) (Numerical verification of RH at initial time 0) There are no zeroes ζ(σ + iT) = 0 with
  (1+y0)/2 ≤ σ ≤ 1 and 0 ≤ T ≤ X/2.
- (ii) (Asymptotic zero-free region at final time t0) There are no zeroes H_{t0}(x + iy) = 0 with
  x ≥ X + √(1 − y0²) and y0 ≤ y ≤ √(1 − 2t0).
- (iii) (Barrier at intermediate times) There are no zeroes H_t(x + iy) = 0 with
  X ≤ x ≤ X + √(1 − y0²), √(y0² + 2(t0 − t)) ≤ y ≤ √(1 − 2t), and 0 ≤ t ≤ t0.

Then Λ ≤ t0 + (1/2) y0²."

*Proposition 3.3 (Zero-free region criterion), p.15.* "Suppose that t0, X > 0 and 0 < y0 ≤ 1
obey the following hypotheses:

- (i) There are no zeroes H_0(x + iy) = 0 with 0 ≤ x ≤ X and √(y0² + 2t0) ≤ y ≤ 1.
- (ii) There are no zeroes H_{t0}(x + iy) = 0 with x ≥ X + √(1 − y0²) and y0 ≤ y ≤ √(1 − 2t0).
- (iii) There are no zeroes H_t(x + iy) = 0 with X ≤ x ≤ X + √(1 − y0²),
  √(y0² + 2(t0 − t)) ≤ y ≤ √(1 − 2t), and 0 ≤ t ≤ t0.

Then there are no zeroes H_{t0}(x + iy) = 0 with x ∈ ℝ and y ≥ y0."

Thm 1.2 follows from Prop 3.3 plus Thm 3.2 (de Bruijn), with Thm 1.2(i) implying Prop 3.3(i)
through H_0 = ξ/8 (p.16). Separately, P15 (p.3) notes that "in practice" the barrier region is
replaced numerically by the larger region X ≤ x ≤ X + 1, y0 ≤ y ≤ 1, 0 ≤ t ≤ t0. That is a
practical enlargement, not the theorem's (iii).

The engine is Thm 1.3, an effective A + B − C approximation valid for 0 < t ≤ 1/2, 0 ≤ y ≤ 1,
x ≥ 200.

P15 §10 predicts Λ ≤ O(1/log T) from RH verified to height T. Table 1 reaches 0.10 at X ≈ 9·10^21.

### 5.2 Ranked next milestones (frontier report §5, uncommitted; costs are estimates, not measurements)

Every Size and Compute figure in this table is an **unanchored estimate** from the uncommitted
frontier report, except where a repo anchor is given. The calibration is the C3 closure of this
island: 3,695 lines over 12 modules, including DBNStrip (501) and DBNStepControls (155). Its
design memo estimated about 4,500 lines, range 3,500-6,000
(`DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md:344`), which also includes L1 (the strip,
~950 lines). So the actual came in under the estimate.

| Rank | Milestone | Size | Compute | Value / honest caveat |
|---|---|---|---|---|
| 1 | **M1** Parametric de Bruijn (Thm 3.2 / de Bruijn Thm 13), the up-set property, and the sInf-free C10 clause | 500-1,000 lines (unanchored estimate) | none | Highest. Gives C10 an sInf-free registry statement (M1c; crux doc `:72`) but proves nothing toward it. Every Λ ≤ c derived from P15 consumes the parametric de Bruijn step, since Thm 1.2 closes with Thm 3.2 (P15 p.2, p.16). Method: reweight the approximants by e^{t0 u²} (`DBNHeatApprox.lean:119-127`), re-prove order < 2 growth, reuse `DBNStep.lean:459` and Hurwitz. |
| 2 | **M0** Numeric scoping, no Lean. Run the P15 public code (km-git-acc/dbn_upper_bound) for the smallest certifiable t0 + y0²/2 at X = 55/8 (hypothesis-free) and at X ≈ 1.28·10^6 (Arb-conditional) | none | days of CPU (unanchored estimate) | High. Fixes the numeral for M6, or shows none below 1/2 is reachable at X = 55/8. The roadmap's C8 projection "G1 ~0.36" (`RH_ROUTES_ROADMAP:223`) is a single-anchor extrapolation. |
| 3 | **M4** P15 criterion as a conditional kernel theorem, with (i)-(iii) as named Props | 2.5k-5k lines (unanchored estimate) | none | High. Turns every future bound into finite obligations. Needs Prop 3.1 zero dynamics (motion of simple zeros, repeated zeros, minimal time, Rouché). |
| 4 | **M5** Effective H_t approximation (P15 Thm 1.3; roadmap C6/C7) | 10k-20k lines (unanchored estimate) | none | Enabling, and the long pole. Shares Γ/Stirling/EM infrastructure with the ANDURIL RS remainder (Hankel representation plus saddle bound, 5,000-11,000 lines per `ANDURIL_ARB_DISCHARGE_2026-09-23.md:51`). |
| 5 | **M6** Hypothesis-free Λ ≤ c0 < 1/2, kernel-checked | M1+M4+M5; P15-scale about 13k-26k (unanchored estimate) | minutes to hours, pending M0 (unanchored estimate) | First kernel-checked explicit c0 < 1/2 in this repo (priority unverified: no literature check was done, and Gordon's manuscript has a partial Lean audit, `RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md:40`). Effective, unconditional c0 < 1/2 already exist on paper (0.22 from P15 + Platt 2017; 0.2 from Platt-Trudgian 2021). Whether any c0 < 1/2 is certifiable at X = 55/8 is itself open (§7.3). Hypothesis (i) at X = 55/8 needs no zeta zero with (1+y0)/2 ≤ σ ≤ 1 and 0 ≤ T ≤ 55/16 (closed). The registry node `AND_height_floor_kernel` covers only 0 < Im ρ < 55/16. The island theorem `HeightFloor.im_gt_of_zero` (`examples/zeta_reflection/lean/HeightFloor.lean:76`, strict `55/16 < ρ.im`) also covers T = 55/16. T = 0 (real zeros with σ ∈ [(1+y0)/2, 1)) is covered by neither, because `zeta_ne_zero_low_right` (`:43`) assumes `0 < s.im`. Taking X < 55/8 removes the T = 55/16 endpoint even at registry level; the T = 0 case needs its own argument either way. On the H_0 side, T = 0 is x = 0, which P15 (p.15) rules out from (4) and Φ > 0; the dbn island has `Φ_pos` (`DBNHeatApprox.lean:551`), but this document cites no H_t(iy) ≠ 0 lemma for general y. Toolchain seam: `HeightFloor.lean` builds on Lean v4.32.0 (`zeta_reflection/lean/lean-toolchain`), and the dbn island is on v4.34.0-rc1. This is the same cross-pin problem raised against Rodgers-Tao below. P15 routes (i) through Prop 3.3(i), which is in H_0 form, so M6 also needs the ζ-to-H_0 bridge (`RH_dbn_H0_eq_xi`, plus the coordinate map of `RH_dbn_rh_iff_H0_real_zeros`). (ii)/(iii) need a small-x rigorous H_t evaluator. |
| 6 | **M7** Arb-conditional Λ ≤ c on the 640k ladder (X ≈ 1.28·10^6) | incremental on M6 (unanchored estimate) | ladder | Medium. Hypothesis-carrying; will not beat 0.2. |
| 7 | **M8** Reproduce 0.22 / 0.2 | with M5 | barrier about 145 core-days naive (unanchored estimate) | Record-rigor artifact, not RH progress. (i) must be carried as a Platt / Platt-Trudgian hypothesis. Kernel-only zero verification is rated INFEASIBLE already at 10^9 (Riemann-Siegel, pure kernel, about 200-300 core-years, `ANDURIL_ARB_DISCHARGE_2026-09-23.md:264`), far below 3·10^10. For scale, the same memo projects 10^6 at about 11 weeks by EM order ≤ 13 (`:262`), or 3-4 hours by Riemann-Siegel once the unbuilt bricks exist (`:263`). |
| 8 | **M9** Dobner, Λ ≥ 0 | 8k-15k lines (unanchored estimate) | none | Track only. Would also give Λ > −∞, which makes Λ definable. Zero value for RH. |

**Not recommended:**

- A standalone ineffective Ki-Kim-Lee proof: 6k-12k lines (unanchored estimate) and no numeral,
  so it fails the "effective constants compose" test.
- A C5 Lehmer-pair Λ ≥ −ε bound, which Rodgers-Tao supersedes.
- Rodgers-Tao itself, at 20k-40k lines (unanchored estimate). It needs pair correlation, and Zeta23 (RvM, explicit
  formula) sits on a different toolchain pin (`v4.33.0-rc2`).

Also not useful: the effective de la Vallée Poussin region with `dlvpRateC ≈ 7.3e-6`
(`li_positivity/lean/DlvpZetaRateEffective.lean:28, :282`). Fed into P15(i) at T ≈ 10^6, it yields
only c > 0.4999989.

### 5.3 Where Route C sits on the wall map

| Roadmap id | State |
|---|---|
| C2, C3, C4 | **Done** (this document) |
| C1 (Lehmer instrument), C5 (CSV), C9 (Rodgers-Tao) | Open, lower-bound side. The roadmap says "Track, don't staff" for C9 only (`RH_ROUTES_ROADMAP_2026-09-16.md:224`). Not staffing C1 and C5 is this document's own recommendation. |
| C6 / C7 (evaluator, P15 estimates) | Open; = M5 / M4 |
| C8 (certified Λ ≤ c) | Open; = M6 / M7 |
| C10 (Λ ≤ 0) | **rh-hard-wall** (`RH_ROUTES_ROADMAP:225`): exp(C/ε) height per rung, P(route proves RH) ≈ 0 (`:230`). |

No M-item approaches C10. Every Λ ≤ c with c > 0 is strictly weaker than RH. Upper-bound rungs are an
F4 instance factory, on the wrong side of the quantifier (`WALL_BACKLOG_MAP_2026-09-18.md:30`).

**The wall map is stale on Route C.**

- `WALL_BACKLOG_MAP_2026-09-18.md:48-50` lists the three original dbn nodes as draft. Rows :48-49
  (`RH_dbn_H0_eq_xi`, `RH_dbn_debruijn_real_zeros`) say BLOCKED-ON with no readback. Row :50
  (`RH_dbn_rh_iff_H0_real_zeros`) instead reads "CORRECTED 2026-09-22", filed F4, blocked on C2
  alone.
- `:274-277` says "Route C currently has *zero* workable nodes".
- All of these predate the 09-22 and 09-23 grants.
- Class mismatch: the wall map files the de Bruijn node as **F2** (effective constants, :49),
  while this document files Λ ≤ c rungs as F4 (above). Both can hold: `t ≥ 1/2` is a single
  effective numeral (F2 content), while a ladder of Λ ≤ c rungs is an instance factory (F4). The
  wall map update should state which class each future Λ ≤ c node takes.

---

## 6. Lessons and footguns

1. **Name clashes across parallel lanes on one island.** The strip lane and the C2 lane both defined
   `ofReal_exp_cpow`. Merge `27b62c097` renamed DBNStrip's copy to `ofReal_exp_cpow_comm`. That
   merge and `1264ddd3d` (cl/c3) each needed a "structural island resolution": lakefile `lib`
   entries and AxiomGuard blocks. Lesson: lanes that share an island should build the union of both
   before merging, or use per-lane name prefixes for helper lemmas.
2. **Resolver and gate footguns.**
   - Registry theorems are root-namespace. On the island they must be declared after `end DBN`
     (strip A1 :50). Otherwise `guard_anchors.resolve_theorem` (`scripts/guard_anchors.py:187`)
     resolves a different fully-qualified name.
   - The same resolver raises on a `private` artifact and on ambiguous matches.
   - The registry `DBN.H` is a textual copy (`RHDefs.lean:97-116`). Drift is caught only by the
     statement gate plus the auditors' vocabulary mirror (H0_eq_xi A1 :70-79). That check works
     because every name is fully qualified, so differing `open` lines cannot change resolution.
   - The `pp.fullNames` probe (rh_iff A2 :66-68) is the check that rules out shadowing of
     `riemannZeta` / `H`.
   - `statement_matches` is a whitespace-collapsed containment test followed by a proof-body check.
     Mutation controls (for example `∨ True`, H0_eq_xi A2 :66-67) should stay part of every audit.
   - The system `python3` lacks `tomllib`, so `guard_anchors.py` needs python3.12.
3. **Design estimates vs actual line counts.**

   | Design memo | Estimated | Actual | Notes |
   |---|---|---|---|
   | C2 total (A-E) | 1000-1550 | 1234 | Module C overran: 250-400 estimated, 684 actual (65 theorem/lemma declarations). Module D came in at 88 against 200-300. |
   | C3 total | about 4500 (3500-6000) | 3695 (3540 without Controls) | L1 strip 501 vs ~950. L2 757 vs ~1300. L3 Hadamard 1589 in 5 files vs ~1950 in one. L4 480 vs ~500. L5-L6 213 vs ~400. |

   Overall the estimates were conservative. The overrun was in kernel calculus, not in the headline
   analytic step.
4. **Design pivots that paid off.**
   - C3 dropped the Laguerre-Pólya / Pólya-factorisation plan (`DBN_FOUNDATIONS` memo) in favour of
     heat approximants, the step lemma, Hadamard and Hurwitz.
   - L3d replaced minimum modulus with Jensen in the mean.
   - L2d replaced Fourier uniqueness with `Φ_pos`.
   - L2c replaced closed-ball convergence with strips.
   - C2 applied the substitution before integrating by parts, and moved A(iv) to the Mellin level.
   - In the C2 modules A-E, the "no tsum/integral interchange" discipline held. The strip does
     interchange, by Fubini-Tonelli (`DBNStrip.lean:419`).
5. **Keep proof-irrelevant prose honest after landing.** These items are stale as of this HEAD and
   were not fixed:
   - the CI comment "32 `#print axioms` anchors … 2026-09-22" (`telperion-lean-e2e.yml:2501`), with
     a floor of 30, against 325 actual;
   - `AxiomGuardDBN.lean:19-21` ("a registry STATEMENT, not an island theorem");
   - `DBNStep.lean:5` ("NOT on this island yet");
   - `DBNDeBruijnReduction.lean:7` ("Neither is proved"), and `:16`, which says "order 1" where the
     proved bound is 3/2 (`DBNHeatApprox.lean:355`);
   - the `lakefile.toml` comment for `DBNDeBruijnReduction` (`examples/dbn/lean/lakefile.toml:107`),
     which calls both inputs "(NOT proved)";
   - the `RH_dbn_H0_zero_strip.toml` title, which says "no theta FE". The strip consumes the theta
     functional equation through `Φ_neg` (`DBNDefs.lean:260-270`, via `thetaMoment_fe_deriv1/2`),
     and `DBNStrip`'s own docstring (`:494-497`) names `Φ_neg` as its functional-equation input.
6. **Citation hygiene.**
   - A web summary invented a Platt-Trudgian "Theorem 1: Λ ≤ 0.2" and "4×10^12 flops". Their
     Theorem 1 is RH to 3,000,175,332,800, and the Λ ≤ 0.2 result is Corollary 2 in §3.4.
   - `RH_ROADMAP_CLAIMS_VERIFICATION_2026-09-17.md:29` is right that the abstract omits Λ, but the
     body states it.
   - The grant commit `b524f7e7d` says 1e-34 for the H_0-zero check. The testimonies say 1e-36
     (debruijn A1 :66) and 7e-34 (A2 :64, the maximum), so the commit understates the larger one.
   - The crux doc lives at `arda-crux2/telperion/docs/RH_CRUX_RESEARCH_2026-09-22.md`, not in this
     worktree.
   - Crux "salvage" items (`:239, :257, :865`: local de Bruijn lemma, edge band) remain unrefereed.
7. **Dependency surgery.** The C2-free strip made C3 independent of C2. Import closures should be
   audited per node, as strip A2 did, rather than inherited from the roadmap's dependency column.

---

## 7. Open items and proposed registry ops

### 7.1 Housekeeping (no new math)

- Raise the `dbn-compiles` axiom-guard floor from 30 to 325 and update the comment at
  `telperion-lean-e2e.yml:2501`.
- Fix the stale comments, lakefile comment and toml title listed in §6.5.
- Update `WALL_BACKLOG_MAP` rows `:48-50` and the paragraph at `:274-277` to show four proved dbn
  nodes, with C10 as the remaining wall on this route.
- Note in the wall map that `dbn-compiles` is required, but `enforce_admins` is false.
- Decide the Borel-Carathéodory overlap (§4) before any upstream PR.

### 7.2 Draft nodes (proposed, NOT registered; statement sketches only)

All would use `DBN.H` from `RHDefs`. Slugs are suggestions.

**`RH_dbn_debruijn_parametric`** (M1a; lemma; depends_on `RH_dbn_debruijn_real_zeros`, reusing its
machinery):

```lean
theorem dbn_debruijn_parametric :
    ∀ t0 Y : ℝ, (∀ z : ℂ, DBN.H t0 z = 0 → z.im ^ 2 ≤ Y) →
    ∀ t : ℝ, t0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im ^ 2 ≤ max (Y - 2 * (t - t0)) 0
```

Whether to require `0 ≤ t0` is a design choice. Allowing `t0 < 0` is what Newman-side uses need, and
it requires the order-< 2 growth of H_{t0} for negative t0.

**`RH_dbn_real_zeros_upset`** (M1b; lemma; the Y = 0 corollary of the above):

```lean
theorem dbn_real_zeros_upset :
    ∀ t0 t : ℝ, t0 ≤ t → (∀ z : ℂ, DBN.H t0 z = 0 → z.im = 0) →
    ∀ z : ℂ, DBN.H t z = 0 → z.im = 0
```

**`RH_dbn_rh_iff_real_zeros_nonneg_t`** (M1c; milestone; depends_on `RH_dbn_rh_iff_H0_real_zeros`
and `RH_dbn_real_zeros_upset`). This is the sInf-free statement of C10 as an equivalence. It is
workable, F4-class, and proves neither side:

```lean
theorem dbn_rh_iff_real_zeros_nonneg_t :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2) ↔
    ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0
```

The right-hand side alone could be registered as a wall node (`rh-hard-wall`, never staffed), so that
C10 has a registry anchor (crux `:72`).

**`RH_dbn_p15_criterion`** (M4; milestone). The P15 conditions become named Props
`P15ZeroFreeRect X y0 t0`, `P15Canopy X y0 t0` and `P15Barrier X y0 t0` (the barrier region
depends on y0), transcribed verbatim from P15 Prop 3.3 (H_0 form, §5.1). The theorem:

```lean
theorem dbn_p15_criterion (X t0 y0 : ℝ) (hX : 0 < X) (ht0 : 0 < t0)
    (hy0 : 0 < y0) (hy1 : y0 ≤ 1) :
    P15ZeroFreeRect X y0 t0 → P15Canopy X y0 t0 → P15Barrier X y0 t0 →
    ∀ t : ℝ, t0 + y0 ^ 2 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0
```

The side conditions (t0, X > 0 and 0 < y0 ≤ 1, P15 p.2 and p.15) must be copied from the paper,
not paraphrased. The hypotheses are Prop 3.3's, while the conclusion is Thm 1.2's: Prop 3.3
concludes only "no zeroes of H_{t0} with y ≥ y0", and de Bruijn's Thm 3.2 closes the gap (P15
p.16). That is why this node depends on `RH_dbn_debruijn_parametric`.

**`RH_dbn_effective_Ht_approx`** (M5; infrastructure). This is P15 Thm 1.3, an A + B − C
approximation with explicit E1-E3 bounds for 0 < t ≤ 1/2, 0 ≤ y ≤ 1, x ≥ 200. It should probably
split into sub-nodes along P15 §§4-6, and share Γ/Stirling/EM with the ANDURIL RS remainder.

**`RH_dbn_lambda_le_c0`** (M6; milestone; depends on M4, M5, `AND_height_floor_kernel`,
`RH_dbn_H0_eq_xi` and `RH_dbn_rh_iff_H0_real_zeros`). The last two carry Thm 1.2(i) (ζ form)
into Prop 3.3(i) (H_0 form). `AND_height_floor_kernel` alone does not supply Thm 1.2(i) at
X = 55/8: it leaves open T = 0 and, at registry level, T = 55/16 (see M6 in §5.2). Its artifact is
on Lean v4.32.0, and the dbn island is on v4.34.0-rc1, so a cross-pin port is also needed. Here
c0 is an explicit rational below 1/2, to be fixed by M0, if one exists at this X (§7.3):

```lean
theorem dbn_lambda_le_c0 : ∀ t : ℝ, (c0 : ℝ) ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0
```

**`RH_dbn_newman_dobner`** (M9; track only):

```lean
theorem dbn_newman : ∀ t : ℝ, t < 0 → ∃ z : ℂ, DBN.H t z = 0 ∧ z.im ≠ 0
```

**M0** is a scoping task, not a node. Its deliverable is a certified-margin table (c0, X, t0, y0,
mesh counts, N) at X = 55/8 and X ≈ 1.28·10^6.

### 7.3 Open questions

- The best c0 reachable at X = 55/8 or X ≈ 1.28·10^6 is not known. M0 answers this.
- A discrete barrier variant built on `shiftAvg` has been suggested as an alternative to P15
  Prop 3.1 dynamics. It is speculative and unverified.
- Ki-Kim-Lee's exact strictness argument was not read. The sup of |Im| over zeros of H_0 may equal 1,
  and if so the open strip alone does not give strictness.

conjecture1_proved = False.
