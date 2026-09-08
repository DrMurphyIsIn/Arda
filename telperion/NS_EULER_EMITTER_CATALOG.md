# NS/Euler emitter-mining catalog

Certificate-mining pass over OpenAI's finite-time-blowup formalization
[`github.com/openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler)
(Lean 4.34.0-rc2 + Mathlib; two papers, "Finite time blowup for Navier–Stokes"
and "Finite time blowup for the Euler equation"; Clay alternatives **(C)**, **(D)**
and a compactly-supported Euler singularity).

Same discipline as the zeta-23 / Palomar passes
(`[[reference-palomar-zeta23-telperion]]`): we distill only the **generator-shaped,
self-contained ℝ/ℤ/ℕ-arithmetic atoms** the kernel can discharge cheaply
(`linarith` / `nlinarith` / `positivity` / `norm_num`). The heavy PDE machinery
(Fréchet derivatives, `MeasureTheory`, ODE flows, matrix determinants) is a
**prelude/library**, NOT an emitter — the same scoping correction the Hermitian
matrix core got.

**Honesty seam throughout:** every emitted theorem certifies an *arithmetic
implication*; the analytic facts (that a correction of the stated order exists,
that a PDE estimate holds, that √d is irrational) enter as **hypotheses**.
`conjecture1_proved = False`. Nothing here is a proof of blowup — it is the
reusable arithmetic spine of one.

The proof surface is enormous — **579 `NavierStokes/*.lean` + ~500 `Euler/*.lean`
files, ~400k lines** — and dominated by exactly the arithmetic-certificate
machinery emitters shadow: **3910 `linarith`, 1785 `positivity`, 1394 `nlinarith`,
822 `bound`, 152 `nlinarith [sq_nonneg …]`, 1128 `|·| ≤ …·…` perturbation bounds**.
The atoms below recur across that surface.

---

## Built this pass (TDD-green, wired, CI-pending Lean)

| Kind | Module | Source file | Shape |
|------|--------|-------------|-------|
| `affine_ledger` | `emit_ns_ledger.py` | `NavierStokes/ExponentLedger.lean` | affine gain/increment bookkeeping over a parameter box |
| `quadratic_irrational` | `emit_quadratic_irrational.py` | `NavierStokes/DiophantineGraph.lean` | ℤ[√d] conjugate-norm lower bound `1 ≤ \|p+√d q\|\|p−√d q\|` |
| `gevrey_majorant` | `emit_gevrey_majorant.py` | `Euler/EulerProof.lean` (Apache-2.0 port) | the Gevrey-2 factorial-majorant calculus `R^(n+d)((n+d)!)²`: shift / convolution-3 / geometric gain / triangular-recurrence closure; modes `calculus` / `budget` / `polynomial_radius`, exact rational budget certification |

### `affine_ledger` — the exponent ledger (flagship)

`ExponentLedger.lean` (manuscript Prop 10.3) assigns real exponents — **affine in
a scale parameter σ and a fixed accuracy κ** — to each analytic estimate, then
checks ~40 times that a per-stage **gain** dominates the per-stage **increment**,
over the region `{σ ≥ 1/5, 0 ≤ κ ≤ 1e-5}`. Every fact is `linarith` / `ring` /
`min`-lemma shaped.

Two claim modes shipped:
* **`margin`** — `threshold ≤ (or <) affine_form` on a box; `by linarith`.
* **`min_lower`** — `threshold < (or ≤) min(f₁,…,f_m)` (the gain-dominates step);
  `simp only [lt_min_iff]; exact ⟨by linarith, …⟩`.

Certification is **exact and LP-free**: an affine form over a box attains its
extremum at a vertex, so the worst-corner rational is computed in closed form
(coeff > 0 → use the lower bound, coeff < 0 → the upper bound). A missing bound
in the binding direction ⟹ unbounded below ⟹ **REFUSED** (negative control).
Positive controls in the tests are the literal `wave_at_least_seven_tenths`
(tight at σ=1/5) and `signed_bar_gain_exceeds_seventeen_hundredths` facts.

Mirrors the BG `affine_param_endpoint` emitter but multi-parameter with `min`-of-list.

### `quadratic_irrational` — ℤ[√d] separation (novel to Telperion)

`DiophantineGraph.lean` needs the graph directions `(1, 1−√2)`, `(√2−1, 1)` to be
uniformly badly-approximated by the integer lattice (else small divisors in the
correction scheme are uncontrolled). The classical trick: for integers `(p,q)`
not both zero the conjugate product `(p+√d q)(p−√d q) = p² − d q²` is a **nonzero
integer**, so `|p+√d q|·|p−√d q| ≥ 1`.

Two theorems per instance:
* **`_id`** — the real identity `(p+√d q)(p−√d q) = p² − d q²`; `nlinarith [Real.sq_sqrt]`.
* **`_norm_lower`** — `p² − d q² ≠ 0 → 1 ≤ |p+√d q|·|p−√d q|`; `Int.one_le_abs`
  on the integer norm + the identity + `abs_mul`.

Honesty seam: the non-vanishing `p²−dq² ≠ 0` is a **hypothesis** — that is where
irrationality/square-freeness of `d` enters analytically. Perfect-square `d` is
**REFUSED** (√d rational → norm vanishes for nonzero (p,q) → separation vacuous);
`d ≤ 0` refused. Complements the existing `padic` valuation emitter (this is the
Archimedean/`ℤ[√d]` badly-approximable analogue).

---

## Round-1 recursive sweep harvest (2026-09-08, workflow `wf_0fd1cfd4-8f2`)

A 20-miner multi-agent sweep (12 deep clusters over the 84 densest files, 7
mid-band scan clusters, 50-file tail sample; 257 files classified, 111
emitter-bearing) synthesized **46 raw shape reports into 20 canonical new
emitter candidates** — 12 high-generality, 8 medium. Ranked highlights (full
signatures + tactics in the workflow synthesis, task `wbj0o68zh`):

**High generality (12):**
1. **`gevrey_factorial_majorant`** — the single largest gap: the Gevrey-2
   majorant calculus `R^(n+d)·((n+d)!)²` (shift / radius-inflation / binomial
   split / convolution-with-`Σ1/C(n,k)≤3` / recurrence-closure), found
   independently by **6 miners**; the arithmetic engine of the entire Euler
   corpus. No existing kind touches `Nat.choose`/`Nat.factorial`.
2. **`coefficient_mass_eval`** — `|p.eval x| ≤ ‖p‖₁·T^deg` + nested-envelope
   reification (3 miners).
3. **`multilinear_product_perturbation`** — Leibniz telescoping
   `|f(pert)−f(nom)| ≤ ε·p(M)` with auto-generated ring identity (5 miners);
   generalizes the catalogued affine PerturbationTriangleBound.
4. **`perturbed_quadratic_cone`** — abs-perturbation ledger + SOS vertex margin
   ⟹ strict quadratic cone cap (the NS blowup cone-exclusion arithmetic).
5. **`rpow_exponent_budget`** — prefactor·decay^N ≤ k^target with all
   bookkeeping at the exponent level via linarith.
6. **`rpow_comparability_enclosure`** — `q/2≤Q≤2q ⟹ Q^e ≤ 2^|e|·q^e` (both
   exponent signs unified).
7. **`monomial_budget_ladder`** — one master smallness budget ⟹ a family of
   monomial rung bounds (6+ instances per Euler packet file).
8. **`ratio_recurrence_telescope`** — multiplicative telescoping of ratio
   recursions into factorial/geometric/index normal forms (the product
   counterpart of the additive `telescope`).
9. **`finite_prefix_absorption`** — eventually-bounded ⟹ globally bounded with
   an explicit prefix-sum constant witness.
10. **`two_row_solve_bound`** — 2×2/3×3 solution-entry bounds from row scale +
    ratio gap (pure scalar, no Matrix).
11. **`sqrt_root_elimination`** — "below the lower root ⟺ discriminant
    inequality" symbolic radical elimination; directly reusable on the BG
    price-interval and RH boundary-curve fronts.
12. **`twopoint_moment_feasibility`** — constructs a rational 2-point measure
    with prescribed mean/variance under affine support constraints — a rank-2
    pseudo-expectation witness, relevant to the SoS 3-XOR front.

**Medium (8):** `scale_invariant_quotient_cancel`, `sqrt_comparability_envelope`,
`positive_quadratic_denominator_bound`, `low_order_plus_geometric_tail`,
`simplex_second_moment`, `reciprocal_square_convolution` (the antidiagonal
convolution ≤ 8× companion of TelescopingReciprocalSquare), `poly_exp_absorption`,
`eventual_scaling_threshold`.

Dropped as covered/thin: ConvexCombinationAbsBound, ScaleCancelDiscriminant,
reciprocal_comparison_propagate, cone_margin_of_dichotomy, and 4 shapes folded
into the canonicals above. `reciprocal_box_tolerance_extraction` → noted as a
`le_div_iff₀` option flag on `affine_ledger`, not a new kind.

Round-1 completeness: ~10% of files read but heavy shape convergence
(saturation evidence: the Gevrey engine consumed by the largest unsampled
families). Blind spots (SmoothTimeField*/CylinderDirichlet*/WholeSpaceGaussian*/
SmoothFlow* + unread family members) were swept in **round 2**
(`wf_2b47e971-164`, full coverage of all remaining files). ComparatorChallenges/
gap closed by hand: both files are the Clay problem-statement mirrors with
intentional `sorry` placeholders — statements only, no emitters.

## Catalogued round-0 (high-value, not yet built)

| Shape | Source file | Atom | Discharge | Notes |
|-------|-------------|------|-----------|-------|
| **PerturbedSignCertificate** | `GrowingMode.lean` (`upper_edge_factor_negative`, `cone_boundary_derivative_negative`) | `\|e_ij\| ≤ ε` + spectral gap `ε(1+r)² < 2λr` ⟹ a signed bilinear form `< 0` | `nlinarith` off `abs_le` bounds | The invariant-cone "barrier drift is inward" atom. Generic: bounded perturbations + a gap ⟹ definite sign. ★★ |
| **ConeAmplitudeBound** | `GrowingMode.lean` (`original_coordinate_bounds`) | `\|q\| ≤ r·p`, `0 ≤ r ≤ 1/2` ⟹ `(1−r)p ≤ p+q ≤ (1+r)p` and rel-error `≤ 4\|h\|r` | `nlinarith` | Two-sided amplitude bound from a cone. Possibly a case of the existing `cone` emitter; check before building. ★★ |
| **TelescopingReciprocalSquare** | `AxisWeightEstimates.lean` (`reciprocal_square_telescope`, `sum_squareDecay_le_two`) | `1/x² ≤ 2/x − 2/(x+1)`; `Σ_{k<n} 1/(k+1)² ≤ 2`; shift-comparability `d(n) ≤ 4 d(n+1)` | `field_simp` + `nlinarith`; `Nat`-induction | Classic convergent-p-series tail via telescoping. Overlaps the existing `telescope` / `fwd_telescope` emitters — fold in as a specialized instance. ★★ |
| **PerturbationTriangleBound** | `GrowingMode.lean` (`relative_error_of_cone`) | `\|(λ−D+e₁₁)p + e₁₂q − (λ−D₀)p\| ≤ (δ+ε(1+r))p` | `abs_add_le` + `abs_mul` + `nlinarith` | Generic magnitude bound for a perturbed linear form. ★ |
| **SeparatedIntervalPartition** | `TerminalCompensation.lean` (`lower`/`upper`/`intervals_separated`) | equispaced sub-intervals of `[l,r]` are ordered & pairwise-separated (`i<j ⟹ uᵢ < lⱼ`) | `fin_cases` / `nlinarith` | Feeds the moment-matrix `hsep` hypothesis. ★ |
| **HolderYoungExponentConjugacy** | `R3ConvolutionYoung.lean` (`young_split`, `power_one_mul`, `half_power_mul_self`) | rpow exponent-sum identities `a^p·a^q = a^{p+q}`, conjugacy `1/p+1/q = 1+1/r` | `rpow_add` + `norm_num` | The exponent bookkeeping behind the Young/Hölder pairs `L²∗L¹→L²`, `L^{6/5}∗L^{3/2}→L²`. Foldable into `affine_ledger`/`rational_identity`. ★ |

`★` = value/generality estimate for a future build pass.

---

## Preludes — NOT emitters (scoping discipline)

These are matrix/analysis libraries: the kernel cannot be handed a concrete
determinant / rank / ODE-flow cheaply, so they are ported as **prelude libraries**
(exactly like the Hermitian `rank_trace_ineq` / Sylvester / von Neumann core), not
as generator-shaped emitters.

* `PowerMomentMatrix.lean` — generalized-power evaluation-matrix nonsingularity via
  finite **Rolle induction** (a Wronskian/Chebyshev-system argument). Analysis.
* `FiveRowRank.lean` — rank/linear-dependence counting (shadowed scalar-ly by the
  existing `rank_trace_scalar`).
* `GrowingMode.lean` ODE half — `scalar_envelope_comparison`, `positive_invariant_cone`
  (Grönwall via `MonotoneOn` + `HasDerivAt`, backwards-uniqueness). Analysis; only
  its algebraic *sign* atoms (above) are emitter-shaped.
* `AxisymmetricResidual.lean` — `fderiv` / scalar-Laplacian identities. Analysis.
* `R3ConvolutionYoung.lean` bulk — `lintegral`/Hölder/`MemLp`. Analysis; only the
  rpow exponent identities are emitter-shaped.

---

## Skills (mining infrastructure)

Both extend the existing source-mining subsystem
(`source_mining.py` + adapters, PR #328) — build once that lands on main.

1. **OpenAI-formalization source adapter** (`lead_type = LEAD_FORMALIZED`). Watch
   `openai/NavierStokesAndEuler` (and DeepMind `formal-conjectures`, from which the
   Comparator challenge statements were adapted) for new commits/files. These are
   *already Lean-verified* → **port leads**, not formalize-first leads, exactly like
   the `mathlib4` / `compfiles` GitHub adapter. Config stub:
   ```
   {"kind": "github", "repo": "openai/NavierStokesAndEuler",
    "paths": ["NavierStokes/", "Euler/"], "lead_type": "LEAD_FORMALIZED",
    "shape_hints": ["affine_ledger", "quadratic_irrational", "telescope",
                    "perturbed_sign", "cone_amplitude"]}
   ```

2. **Comparator-challenge ingest.** The repo ships `ComparatorChallenges/*.json`
   verified with `leanprover/comparator` + `nanoda_bin` + `landrun` — the **same
   toolchain** as zeta-23 and Telperion's comparator integration
   (`[[reference_comparator_integration]]`, `comparator.py`). A skill that, given a
   formalization repo with `ComparatorChallenges/`, runs the comparator check and
   registers the top-level statement as a verified lead. Reuses `comparator.py`
   wholesale; no new trust surface.

Palomar/arXiv already surface such repos; this pass shows the *distillation* step
they feed.

---

## Relationship to existing emitters

- `affine_ledger` vs **`affine_param_endpoint`** (BG SCLStep): the latter collapses a
  *single* affine-in-one-parameter gap `A + μB ≥ 0` on `[lo,hi]` to two endpoint
  checks via a fixed algebraic identity, for *opaque function-valued* `A,B`.
  `affine_ledger` is *multi-parameter* over a box, with `margin` and `min`-of-list
  modes for *concrete rational* exponent bookkeeping (`linarith` + `lt_min_iff`).
  Complementary, non-overlapping.
- `quadratic_irrational` vs **`padic`**: `padic` is the non-Archimedean valuation
  atom; this is the Archimedean ℤ[√d] badly-approximable analogue. No overlap.

## Provenance

- Base: `origin/main` @ `f047227`, worktree `~/arda-ns-emitters`, branch
  `feat/navier-stokes-emitters`.
- Built: `emit_ns_ledger.py`, `emit_quadratic_irrational.py` (+ tests); wired into
  `certify._SPECIAL_KINDS` / `_SPECIAL_DISPATCH` (length-3, `emitter_for`-resolvable),
  `emitter_sensitivity.REGISTRY` (both STRUCTURALLY_NONVACUOUS — the parameters are
  the statement, no separately-supplied corruptible cofactor; cf.
  `AffineParamEndpointEmitter` / `AlgebraicBracketEmitter`), and `__init__`.
- Tests green: `test_emit_ns_ledger.py` (11), `test_emit_quadratic_irrational.py`
  (10); registry-completeness gate green (`emitter_for` round-trips both kinds).
- **Kernel-verified locally** (2026-09-08): the emitted Lean for all three shapes
  (ledger margin, ledger min-lower, ℤ[√2] id + norm-lower — 5 theorems) compiled
  clean against Mathlib v4.32.0 via the `proof/formalization` R3Cert project
  (`lake build`, zero warnings after the `linter.unusedVariables` suppression for
  statement-fidelity box hypotheses).
- One pre-existing gate miss on `origin/main` (`EndpointGeomCapEmitter` unclassified)
  is untouched here — it is classified on the not-yet-merged Hermitian PR #326.
- Lean kernel is the arbiter (CI `lake build`). `conjecture1_proved = False`.
