# Telperion emitter roadmap — RH zero-free-region + cross-cutting candidates (2026-09-02)

A second installment of the emitter roadmap (companion to
`EMITTER_ROADMAP_2026-08-21.md`, which covered the BG and P=NP campaigns), derived
from a review of the **Riemann-zeta zero-free-region** formalization
(`examples/zero_free_bridge`, `examples/borel_caratheodory`) cross-referenced
against the **BG** corpus (`examples/bg_*`, `examples/{h_floors,r47_cells,
r7_starofhubs,gauge_lift,lorentzian,…}`). Each item is a recurring
certificate-shaped effort island — currently hand-proven — that a reusable emitter
would crystallize into kernel-checked Lean.

Same selection principle as the prior doc: prefer emitters whose emitted Lean uses
the deterministic, search-free tactics that reliably compile (`ring` / `positivity`
/ `linarith` / `nlinarith` / `norm_num` / `field_simp` / `linear_combination`);
exact-arithmetic (sympy-only) beats cvxpy-gated. `conjecture1_proved = False`
throughout — this is classical-analysis / extremal-combinatorics formalization, not
progress on RH or BG.

## Documentation sync landed alongside this doc
The README "Certificate shapes" table was **out of date**: nine shipped emitters
were missing. Added in the same change — `PolyaZerosEmitter`, `FwdTelescopeEmitter`,
`RationalIdentityEmitter`, `FiniteDecideEmitter`, `ZeroFreeCosineEmitter`,
`DirichletReprEmitter`, `DominatedIntegrabilityEmitter`, `PreconnectedCoverEmitter`,
`ZeroFreeRegionEmitter`. The table is again a faithful list of what is built.

## Cross-cutting theme
Per the standing cross-pollination order (a shape usable by **both** RH and BG gets
built once, reused twice), the two highest-leverage candidates are shared:
**box/corner positivity** (BG's most-copied assembly = RH's zero-free-region
box-positivity, the shared endgame) and **algebraic-number bracketing** (BG's `√2`
crux = RH's `√` cosine-functional atoms). Build these first.

---

## Cross-cutting candidates (RH + BG) — build first

| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| X1 | **BilinearCornerBox** | `0 ≤ Σ_S c_S ∏_{i∈S} x_i` (multilinear, `d` box-vars) on `∏[lᵢ,uᵢ]` from the `2^d` **corner** evaluations only, via sign-of-partial-slope case analysis | BG `h_floors:bilinear_corner_nonneg`/`hfloor_*_cell`, `r47_cells:tel_dA0_cell`, `r7_starofhubs`, `g34_twohub` (the single most-copied hand assembly in the BG corpus); RH box-positivity for the zero-free region (shared endgame) | reusable `bilinear_corner_nonneg` lemma (nested `rcases le_total` on each slope sign + `nlinarith [mul_nonneg …]`), per-corner `positivity`, `_bilinear` identity by `field_simp; ring` | S–M | sympy |
| X2 | **AlgebraicBracket** | rational two-sided enclosure `lo ≤ α ≤ hi` for an algebraic `α` (root of a rational polynomial in the interval) via sign-of-`P` at the endpoints; the `√a` specialization first | BG `√2` crux (`e2_two_rhoB_gt`, `1 ≤ √2 ≤ 17/12`, the old `SqrtBracketCertificate`); RH `√` atoms in the Mossinghoff–Trudgian cosine functional (`ZeroFreeBridge` `(√a₁−√a₀)²`) | `√`: `Real.le_sqrt`/`Real.sqrt_le_sqrt` + `Real.sq_sqrt` + `norm_num` on `lo²≤a`, `a≤hi²`; general: `Polynomial.eval` endpoint signs + IVT + `nlinarith` | S (√) / M (general) | sympy |

`emit_bracket` (`IntervalBracketEmitter`) is **`exp`-only** — X2 is the distinct
algebraic-number companion. Neither X1 nor X2 is covered by `HandelmanEmitter`
(needs a found multiplier, variable-explosion on cross-terms) or `LatticeBoxEmitter`
(integer lattice, monotone axis-tails). X1 is the ready-to-ship bilinear
specialization of the prior roadmap's **P3 (PolytopeMaxMonotone)**.

## RH / complex-analysis frontier

| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| A1 | **HalfPlaneDisk** (Borel–Carathéodory / Möbius–Schwarz) | `Re w ≤ B ⟹ ‖w/(2B−w)‖ ≤ 1` (half-plane→disk), the inversion `g = 2Bw/(1+w)` (`1+w ≠ 0`), and the reverse bound `‖w‖ ≤ t < 1 ⟹ ‖g‖ ≤ 2Bt/(1−t)`; certified core is the Positivstellensatz identity `‖2B−w‖² − ‖w‖² = 4·(B − Re w)·B ≥ 0` | `BorelCaratheodory.lean`: `norm_div_two_mul_sub_le_one`, `moebius_inv`, `norm_g_le_of_norm_w_le` (already sorry-free — this crystallizes the certified positivity core). **Unlocks the `ζ'/ζ` dVP frontier** | `Complex.normSq_apply` expand + `nlinarith [mul_nonneg hB (sub_nonneg…), sq_nonneg w.im]` (PSD core); `div_le_one`, `field_simp; ring` (inversion), `norm_sub_norm_le` + `div_le_div_iff₀` (reverse) | M | sympy |
| A2 | **LogDerivRegionCore** (dVP crux) | from the 3-4-1 log-derivative positivity `0 ≤ 3P(σ)+4P(σ+it)+P(σ+2it)` + polar bounds (`P(σ)≤1/(σ−1)+A`, `P(σ+it)≤AL−k/(σ−β)`, `P(σ+2it)≤AL`), the linear gap `4k/(σ−β) ≤ 3/(σ−1)+3A+5AL` and the cleared region inequality `δ(1−δB) ≤ (1−β)(3+δB)` | `ZeroFreeRegion.lean:dlvp_core_estimate`, `dlvp_region_gap`; boundary edge `ZeroFreeBridge:zeta_boundary_contradiction` (same certificate at the pole) | `linarith`/`nlinarith` from the four hypotheses + `field_simp; ring` denominator clearing (analytic `P`-bounds taken as hypotheses) | S–M | sympy |
| A3 | **MagnitudeSplitBound** | `‖F‖ ≤ α+β+γ` for a three-term representation `F = A + B − C` (finite partial sum + boundary + tail) given per-piece bounds `‖A‖≤α, ‖B‖≤β, ‖C‖≤γ` — the triangle-inequality assembly of a near-line growth bound | `ZetaLogBound.lean:zeta_log_bound` (`h1:=norm_sub_le …`, `h2:=norm_add_le …`, `linarith`); the per-piece `norm_partial_sum_le`/`norm_cpow_one_sub_le_one`/`norm_tail_term_le` are hypotheses | `norm_sub_le` + `norm_add_le` fan-out + `linarith` | S | sympy |
| A4 | **CauchyDerivBound** | `‖deriv f z₀‖ ≤ M/R` from `‖f‖ ≤ M` on `sphere z₀ R` (holomorphic disk), plus the `ρ'=(R−r)/2` closed-form constant `4(R+r)/(R−r)²` | `ZeroFreeElementary:zeta_deriv_bound`; `BorelCaratheodory:borel_caratheodory_deriv(_family)` | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (fixed skeleton) + the constant by `field_simp; ring` | M | sympy |
| A5 | **DiskCoordBounds** | from `z ∈ closedBall w ρ`, the finite linear coordinate facts `Re z ≥ a`, `‖z−1‖ ≥ b`, `‖z‖ ≤ c` (⟹ domain membership + a localized magnitude bound) — a Farkas/linear-arithmetic certificate in `(Re z, Im z)` | `ZeroFreeElementary:zeta_sphere_bound`, `zeta_strip_2t_bound` (the disk→`div_le_iff₀`→`nlinarith` shape, replicated across all four ζ magnitude lemmas) | `Complex.abs_re_le_norm`/`abs_im_le_norm` + `abs_le` + `linarith`; magnitude via `div_le_iff₀` + `nlinarith` | S–M | sympy |

## Finite / combinatorial (BG)

| # | Emitter | Shape | Needed at | Lean | Diff | Exact? |
|---|---|---|---|---|---|---|
| C1 | **FiniteArgmaxMargin** | a designated winner strictly beats each of a finite list of rational competitors `v_i=p_i/q_i`, emitted as **cross-multiplied integer** strict inequalities `p_j·q_w < p_w·q_j` (no ℚ division) + a nonvacuity/value-load check | `bg_extremality:bgext_n{5,7,9,11}_beats_runnerup` (near-star = argmax of Φ¹¹, +margin), `matching_free_energy:compext_*`, `rigidity:*_lt_one` | `norm_num` per competitor | S | ℤ/exact |

Distinct from `CaseDispatchAssemblyEmitter` (`interval_cases` over a bounded
parameter): C1 enforces the cross-multiplication discipline and refuses a
non-strict margin.

## Fold-ins (sub-modes of existing emitters, not standalone)

- **DiscreteConcavity** → new mode of `LogConcaveSinglePointEmitter`: integer argmax
  from rational **enclosures** via a second-difference sign `F(k−1)+F(k+1) < 2F(k)`
  when only numeric enclosures (not a symbolic ratio) are available
  (`bg_caterpillar_concavity`). `emit_logconcave`/`emit_unimodal` need a symbolic
  monotone ratio, which is absent here.
- **HodgeRiemann** → new input mode of `PSDFormEmitter`: a Lorentzian-signature
  (indefinite-`H`) reverse-Cauchy–Schwarz `(vᵀHw)²−(vᵀHv)(wᵀHw) ≥ 0` as a
  completing-the-square Gram on the relevant subspace (`examples/lorentzian`).

## Not re-proposed (correctly subsumed by existing emitters)
- Geometric-tail cap `Σ_{k≥K} rᵏ ≤ rᴷ/(1−r)` (BG `uniform_tail`, the d=6
  `MdGeometricTail`) → `MonotoneRatioTailEmitter` (`r<1` **is** the nonincreasing-tail
  hypothesis).
- Exact factorization ties `621/64=27·23`, `64·243·23=621·576`, `2¹²=4096`
  (`benchmark_factor`, `rigidity`, `tax_growth`) → `ExactFactEmitter`/`IdentityEmitter`.
- The 23-divisibility strictness gate → `PadicValuationEmitter` (prior roadmap B3).
- Convex-hinge Jensen floor (`hinge_floor`) → already the shipped `telperion.hinge`.

## Suggested build order
1. **X1 BilinearCornerBox** — the most-copied hand assembly in the BG corpus, pure
   `ring`/`positivity`/`nlinarith`, and cross-cutting to RH box-positivity. Top pick.
2. **X2 AlgebraicBracket** (`√` specialization) — small, closes named BG (`√2`) and
   RH (`√`) atoms; high reuse.
3. **A1 HalfPlaneDisk** — the Borel–Carathéodory core; its `4B(B−Re w) ≥ 0` positivity
   is pure algebra, and it unlocks the entire dVP `ζ'/ζ` frontier (the drafted
   `BorelCaratheodory.lean` is already green, so this crystallizes a proven core).
4. **A2 LogDerivRegionCore** — mechanizes the analytic-inputs→region step with pure
   linear/polynomial arithmetic (inputs as hypotheses); LOW risk.
5. **C1 FiniteArgmaxMargin**, **A3 MagnitudeSplitBound**, then **A4/A5** and the
   fold-ins as their consuming proofs demand.

Every item above discharges a recurring, currently-hand-proven step in the RH or BG
proof state; none duplicates a shipped emitter (checked against the refreshed README
shape table). The kernel (cloud CI `lake build`) remains the sole gate — a wrong
certificate is a compile error, never a false theorem.
