# Design: Kernel-Verified RH-in-a-Box — Stage 2 (total count) + Stage 3 (localization)

**Date:** 2026-09-06
**Status:** Design (pre-plan)
**Branch:** `rh/zeta-box-localization` (worktree `/Users/peterwmurphy/telperion-zeroloc`, off `origin/main`)
**Predecessor:** `2026-09-06-zeta-zero-localization-design.md` (Stage 0 + Stage 1, MERGED as PR #265). This spec builds Stages 2-3, which that spec scoped and gated.
**Honesty flag:** `conjecture1_proved = False`. This *verifies* RH inside a specific finite box (all nontrivial zeros there are simple and on the critical line); it does **not** prove RH.

---

## 1. Motivation and framing

Stage 1 delivered a kernel-verified **lower bound** on the number of nontrivial zeros of `Λ = completedRiemannZeta` **on** the critical line in an interval (sign changes of the real function `t -> Λ(1/2+it)` + IVT). That says "at least N zeros are on the line" but is silent about zeros **off** the line.

The argument principle closes the gap: the **total** number of zeros of Λ inside a contour (with multiplicity) equals the winding number of Λ's boundary image around 0, a topological invariant computable from Λ's values on the boundary. If the *total* count in a box B equals the *on-line* count in B, then **every** zero of Λ in B is on the line and simple — RH verified in B (Turing's method, now kernel-checkable).

Since PR #265, `origin/main` has kernel-verified the **entire box argument principle** as reusable atoms:
- `RectWinding.rect_winding_unit` / `rect_winding_shifted` — the winding-**nonzero** primitive `∮_∂rect (z-ρ)⁻¹ = 2πi` for ρ strictly inside a rectangle (segment/log-branch/monodromy proof, sorry-free).
- `BoxResidueSum.box_residue_sum_*` — `Bd(Σ_ρ m(ρ)/(z-ρ)) = 2πi·Σ m` given the per-pole winding as a hypothesis (Finset linearity over the four sides).
- `RectArgumentPrinciple` — `∮_∂rect E = 0` for E holomorphic on the box (`integral_boundary_rect_eq_zero_of_differentiableOn`).
- `DlvpBlaschkeSplitExpand.logDeriv_eq_herglotz_add_entire` — for a generic analytic f on `ball 0 R`, `logDeriv f z = Σ_ρ (divisor f (ball 0 R) ρ)/(z-ρ) + E(z)` via Mathlib's `MeromorphicOn.divisor`.

So the contour machinery is done. What remains is (2A) a numeric primitive to read a concrete integer winding count off Stage-0 boundary enclosures, (2B) the Λ-specific local Blaschke split over a strip box (the analytic core), (2C) their composition into the box argument principle, and (3) the localization capstone.

**Object choice:** Λ (`completedRiemannZeta`), consistent with Stage 0/1 (Λ's zeros are exactly the nontrivial ζ zeros; Λ is real on Re=1/2; Λ is holomorphic away from s=0,1).

**Box choice:** a rational box `B = [σ0, σ1] x [T0, T1]` with `0 < σ0 < σ1 < 1` and `T0 > 0`. Then Λ is holomorphic on a neighborhood of `cl(B)` (poles at 0,1 excluded), and the on-line segment `{1/2} x [T0, T1]` (with `σ0 < 1/2 < σ1`) is strictly interior. Corners are rationals so all emitted literals are exact.

## 2. Trust boundary

Identical to Stage 1, extended to the boundary contour:
- The **Stage-0 enclosures** — rational boxes containing Λ at the line sample points (Stage 1) and at a fine sample around `∂B` (Stage 2A), each certified by Arb ball arithmetic — are a **documented non-kernel input**, carried into every emitted theorem as **hypotheses**. The kernel never re-derives them.
- What the **kernel proves**: the discrete-winding identity (2A), the local Blaschke split (2B — **derived**, not assumed), the box argument-principle identity (2C), and the localization implication (Stage 3).
- `conjecture1_proved = False`. The multi-week analytic risk is isolated in 2B and gated by an explicit feasibility probe.

## 3. Staged architecture

```
Stage 2  TOTAL count in box B
  2A winding numerics   enclosures of Λ on ∂B (none ∋ 0, arg-step < π)  ->  (2πi)⁻¹∮_∂B Λ'/Λ = N   [NEW emitter]
  2B local Blaschke     Λ'/Λ = Σ_{ρ∈B} (divisor Λ ρ)/(z-ρ) + E, E holo on cl(B)   [ANALYTIC CORE, probe-gated]
  2C box arg-principle  2B + box_residue_sum + rect_winding_shifted + rect_argument_principle
                        ->  (2πi)⁻¹∮_∂B Λ'/Λ = Σ_{ρ∈B} divisor Λ ρ  = total count (with multiplicity)
  =>  total zeros of Λ in B = N
  |
Stage 3  RH-IN-A-BOX    Stage-1 (>= N_line distinct on-line) + Stage-2 (= N total) + N_line = N
                        ->  every zero of Λ in B is simple and on Re s = 1/2
```

## 4. Stage 2A — discrete winding certificate (NEW first-class emitter, kind `winding_count`)

The 2D analogue of Stage-1's `sign_change_count`.

**Input:** the box `B`, and an ordered cycle of sample points `p_0, p_1, ..., p_{k}=p_0` traversing `∂B` counter-clockwise, each with a certified **complex** rational box `W_i in C` containing `Λ(p_i)` (Stage 0's `enclose_lambda`), such that **no `W_i` contains 0**.

**Certificate condition (rational, checkable):** for each consecutive pair `(W_i, W_{i+1})`, the two boxes lie in a common open half-plane through the origin — a sufficient rational condition that the argument of `Λ` changes by `< π` from `p_i` to `p_{i+1}` (no box straddles the branch cut relative to the previous). Concretely: there is an axis (one of a small fixed rational set of directions) with both boxes strictly on one side, OR the dot-product / cross-product sign test on the box corners bounds the subtended angle below π. The discrete argument increments then sum to `2π·N` for a unique integer `N` = the winding number.

**Emitted theorem (shape):** `(2πi)⁻¹ · Bd(Λ'/Λ) = N`, equivalently the telescoped boundary log-sum equals `2πi·N`, with the enclosure facts (`Λ(p_i) ∈ W_i`, `0 ∉ W_i`, the per-step half-plane witnesses) as hypotheses. **Proof:** Λ nonzero on ∂B (from `0 ∉ W_i` + continuity/enclosure), `Λ'/Λ = (log∘Λ)'` on each segment via `HasDerivAt.clog_real` / the principal branch, FTC-2 collapses each segment to `log Λ(end) - log Λ(start)`, and the per-step `< π` witnesses fix the branch so the four-segment sum telescopes to `2πi·N`. This reuses the exact machinery `RectWinding.lean` already uses for its monodromy jumps — that file is the proof template.

**Negative control:** a fabricated cycle where some `W_i` straddles 0 (Λ could vanish on the contour) is REFUSED at certification; a cycle whose per-step angle test fails (arg jump `>= π`, winding ambiguous) is REFUSED.

**Toy validation:** run `winding_count` on a polynomial with known zeros (e.g. `z^2` inside a box around 0 -> N=2, a zero-free box -> N=0) before any Λ work.

## 5. Stage 2B — local Blaschke split over the box (ANALYTIC CORE, feasibility-gated)

**Goal (Lean):** `Λ'/Λ z = Σ_{ρ ∈ Zeros(Λ) ∩ B} (divisor Λ ρ)/(z - ρ) + E z` for `z` in a neighborhood of `cl(B)` away from the zeros, with **E holomorphic on `cl(B)`**.

**Why this is not from scratch:** the repo already proves `logDeriv_eq_herglotz_add_entire` for a generic analytic f on `ball 0 R` using `MeromorphicOn.divisor`. The remaining work is (i) re-region/re-center from a disk at 0 to a region matching the strip box (the `logDeriv_shift_center` gap the Stage-2 probe named), and (ii) establish `E` holomorphic on `cl(B)` — which is *local*: E = `Λ'/Λ` minus the principal parts at the finitely many zeros in B; since Λ is holomorphic and non-vanishing except at those zeros on a neighborhood of `cl(B)` (pole at 1 and trivial zeros excluded by `T0 > 0`, `σ1 < 1`), the difference is holomorphic there.

**FEASIBILITY PROBE FIRST (task 1 of the plan, own GO/NO-GO):** determine whether Mathlib's `MeromorphicOn`/`divisor` API yields "logDeriv minus its divisor principal parts is holomorphic on a compact region" directly (a `MeromorphicOn.divisor` + `MeromorphicNFAt` decomposition), or whether we re-center the in-repo disk split. Attempt the reduction on a **toy meromorphic function** (a rational function with known poles) before any Λ-specific step. Output: a findings doc naming the exact Mathlib lemmas, the concrete re-centering/holomorphicity path, and a revised effort estimate.

**If GO:** build the split as above and prove E holomorphic on `cl(B)` (`DifferentiableOn`, the hypothesis `rect_argument_principle` consumes).
**If NO-GO:** record the obstruction; fall back to carrying the split as a documented non-kernel hypothesis (Stage 2 then has the same trust boundary as Stage 1) and flag Stage 2B's kernel derivation as a Mathlib-capability milestone. The capstone still stands (with the split as a hypothesis) but the honesty ceiling is lower.

## 6. Stage 2C — box argument principle for Λ (composition)

Chain the merged atoms:
1. **2B split** gives `Λ'/Λ = Σ_{ρ∈B} (divisor Λ ρ)/(z-ρ) + E` on `∂B`.
2. `Bd` (four-segment boundary integral) is linear, so `Bd(Λ'/Λ) = Bd(Σ divisor/(z-ρ)) + Bd(E)`.
3. `rect_argument_principle` (E holomorphic on `cl(B)`) gives `Bd(E) = 0`.
4. `box_residue_sum` gives `Bd(Σ divisor/(z-ρ)) = 2πi·Σ divisor`, with each pole's `hwind` hypothesis discharged by `rect_winding_shifted` (ρ strictly inside B).
5. Therefore `(2πi)⁻¹ Bd(Λ'/Λ) = Σ_{ρ∈B} divisor Λ ρ` = **total zero count in B** (with multiplicity).

Combined with **2A** (`(2πi)⁻¹ Bd(Λ'/Λ) = N`): `Σ_{ρ∈B} divisor Λ ρ = N`, a concrete integer determined by the boundary enclosures.

**Box/atom alignment:** the emitters parameterize corners; the certificate lines up `box_residue_sum`'s and `rect_winding_shifted`'s box with `B` and with 2A's contour so the four segment integrals are literally the same terms.

## 7. Stage 3 — RH-in-a-box localization capstone

Inputs: Stage 1's `>= N_line` **distinct on-line** zeros of Λ in the segment `{1/2} x [T0,T1] ⊂ B` (sign changes), and Stage 2's `= N` **total** zeros in B (with multiplicity).

**Argument:** each on-line sign-change zero is a distinct zero of Λ in B, contributing `>= 1` to the total count, so `N_line <= N` always. If the certificate exhibits `N_line = N`, then the `N_line` distinct simple on-line zeros exhaust the total multiplicity-N zero count, so **every** zero of Λ in B is one of them — simple and on Re s = 1/2.

**Emitted theorem (shape):** `∀ ρ, ρ ∈ B -> Λ ρ = 0 -> ρ.re = 1/2` (and each such zero simple), with Stage-1 and Stage-2 conclusions as the load-bearing hypotheses, plus the `statement_match` gate. Instantiated **end-to-end** on a concrete box over the `[10,35]` segment where Stage 1 already certified 5 on-line zeros: the capstone requires the winding count `N = 5` there, giving a kernel-verified "RH holds in this box."

## 8. Components and files

New emitters (first-class pattern: dataclass + `certify_<kind>_point` refusal + `emit_body` + `<kind>_family` + `certify.py` `_SPECIAL_KINDS`/`_SPECIAL_DISPATCH` + `__init__` export + `emitter_sensitivity.py` stance + example + kernel Lean + CI job):
- `src/telperion/emit_winding_count.py` (kind `winding_count`) — Stage 2A.
- `src/telperion/emit_box_localization.py` (kind `box_localization`) — Stage 3 capstone (may also host the 2C composition helper).

Stage 0 extension:
- `src/telperion/arb_enclosure.py` — a boundary-cycle sampler `enclose_lambda_boundary(box, n_per_side, prec)` returning the ordered `W_i` enclosures around `∂B` (reusing `enclose_lambda`).

Lean:
- `examples/zeta_zero_localization/lean/BlaschkeBox.lean` (Stage 2B: the local split + E holomorphic; probe-gated).
- Emitted `WindingCount.lean`, `BoxLocalization.lean`.
- Reuse Stage-1 `LambdaLineReal.lean` and `XiLineZeros.lean`; import the merged `dvp_geom_atoms` atoms (`RectWinding`, `BoxResidueSum`, `RectArgumentPrinciple`).

Driver + CI:
- `examples/zeta_zero_localization/generate.py` — extend to emit the winding count and the capstone for a concrete box; `--check` drift gate.
- CI job(s) in `.github/workflows/telperion-lean-e2e.yml` (warm `lake exe cache get` then `lake build`).

## 9. Testing

- **2A winding:** toy polynomial known-zero counts (`z^2` -> 2, zero-free -> 0) before Λ; negative controls (box straddling 0 refused; arg-jump `>= π` refused); emitted Lean builds sorry-free, clean axioms.
- **2B split:** toy rational function (known poles) reproduces the split + E-holomorphicity in the probe; if GO, the Λ split builds sorry-free; if NO-GO, the hypothesis-carrying fallback is explicit.
- **2C identity:** on a small box, `Σ divisor = N` matches the toy/known count; drift-checked via `generate.py --check`.
- **Stage 3 capstone:** end-to-end on the `[10,35]` box — `N_line = 5` (Stage 1) meets `N = 5` (Stage 2) -> localization theorem builds sorry-free with clean axioms; negative control: a box with a fabricated off-line zero enclosure (making `N > N_line`) must **fail** to produce the localization conclusion.
- **SoC-safe Lean:** local iteration permitted (operator-confirmed 2026-09-04); always `lake exe cache get` before `lake build`; never a cold Mathlib compile. CI mirrors this.

## 10. Scope

**In scope:** Stages 2A, 2C, 3 (buildable from merged atoms) and Stage 2B **behind its feasibility probe**; end-to-end capstone on one concrete box over `[10,35]`.
**Gated:** Stage 2B's kernel derivation of the Λ split — if the probe returns NO-GO, fall back to the hypothesis-carrying capstone and defer the derivation.
**Out of scope:** any claim toward proving RH; an effective/uniform result over all heights; boxes spanning the pole at s=1 or the trivial zeros; multiplicity > 1 on-line zeros (Stage 1 counts distinct simple sign-change zeros; a tangential even-order on-line zero would show as `N > N_line` and correctly block the localization conclusion rather than be mis-certified).

## 11. Honest ceiling

Every artifact carries `conjecture1_proved = False`. The strongest end-state (Stage 3) is a kernel-verified statement that **all nontrivial zeros of ζ in one specific finite box are simple and on the critical line** — RH verified in that box, not proven in general. The Arb value enclosures are non-kernel input; the Blaschke split is kernel-derived iff the 2B probe is GO, otherwise a documented hypothesis.
