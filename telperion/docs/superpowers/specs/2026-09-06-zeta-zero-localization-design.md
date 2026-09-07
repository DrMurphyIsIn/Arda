# Design: Kernel-Verified Localization of the Nontrivial Zeros of ζ (argument-principle route)

**Date:** 2026-09-06
**Status:** Design (pre-plan)
**Branch:** `rh/zeta-zero-localization` (worktree `/Users/peterwmurphy/telperion-zeroloc`, off `origin/main`)
**Honesty flag:** `conjecture1_proved = False`. This *verifies* RH region-by-region for finitely many zeros; it does **not** prove RH.

---

## 1. Motivation and framing

The recurring idea — *remap ζ onto a different geometry/topology and find the nontrivial zeros there* — has a faithful, now-certificate-shaped realization: the **argument principle**. The number of zeros of ξ inside a contour equals the **winding number** of ξ's boundary image around 0 — a topological invariant (the degree of a map S¹→S¹). "Finding the zeros" becomes a topological count computed from ξ's values on a boundary, cross-checked against the *real* sign-changes of ξ on the critical line.

This session shipped the enabling pieces, now on `main`:
- `emit_jensen_zero_count` — kernel-verified upper bound on zeros of an analytic f in a disk (`AnalyticOnNhd.sum_divisor_le`); already applied to ζ (`zeta_zero_count_unconditional`, O(log|γ|)).
- `arb_enclosure` — rigorous rational enclosure of transcendental constants (Arb ball arithmetic; **currently real part only** — see Stage 0).
- `emit_box_robust` — kernel proof of `∀ c in box, P(c) ≥ 0` (used here for sign certificates).
- `statement_match` — kernel-enforced statement-match gate.
- On the Lean side, `main` has the Herglotz split (`logDeriv ξ = Σ_ρ m(ρ)/(s−ρ) + entire`), Blaschke factorization, `completedRiemannZeta` (Mathlib), and `zeta_log_bound`.

**Trust boundary (as in all our RH/Arb work):** Arb ball arithmetic certifies ξ's enclosures numerically; the *membership* of the true ξ value in each rational box is a documented **non-kernel input** (like inputs R/B and the Jensen coefficient boxes). The kernel verifies the *implications* (sign-change ⟹ zero; winding ⟹ count; counts-match ⟹ on-line).

## 2. Staged architecture

```
Stage 0  complex enclosure        acb -> (Re box, Im box) rational; xi / completed-zeta on a contour
   |
Stage 1  ON-LINE zero count       xi(1/2+it) real; sign changes -> ">= N zeros on the critical line in [a,b]"   [FIRST DELIVERABLE]
   |
Stage 2  TOTAL count via winding  argument principle: boundary-image winds N times -> N zeros in box            [CRUX, feasibility-gated]
   |
Stage 3  localization             Stage1 line-count == Stage2 total-count -> all zeros in box simple + on line  [payoff: RH-in-a-box]
```

Stage 0 + Stage 1 are the buildable first deliverable and stand alone. Stages 2–3 are scoped here but **gated on an explicit feasibility probe** of the Stage-2 kernel lemma before committing.

## 3. Stage 0 — complex enclosure (foundation)

**Files:** extend `src/telperion/arb_enclosure.py`; tests `tests/test_arb_complex.py`.

- `enclose_acb(spec_or_callable, prec_bits) -> tuple[tuple[Fraction,Fraction], tuple[Fraction,Fraction]]` — returns rigorous outward-rounded rational boxes for **both** real and imaginary parts of an `acb` value (reuse the exact-dyadic `mid ± rad` extraction; apply to `.real` and `.imag`).
- `enclose_xi(s_re, s_im, prec_bits)` — enclose the completed ζ / Riemann ξ at s = s_re + i·s_im (build ξ from `acb` ζ, Γ, π; or use flint's completed-zeta if available). Returns a complex rational box.
- Cross-checked against an mpmath oracle (`mpmath.zeta`, `mpmath.siegelz`/ξ) at real and complex points; width shrinks with precision; outward rounding verified (box contains the oracle).
- **Non-kernel-input** documented, `conjecture1_proved = False`.

## 4. Stage 1 — on-line zero count by real sign changes (FIRST DELIVERABLE)

**Files:** `src/telperion/emit_xi_line_zeros.py` (new first-class emitter, kind `xi_line_zeros`); Lean prelude `examples/zeta_zero_localization/lean/XiLineReal.lean` + emitted `XiLineZeros.lean`; tests.

### 4.1 The ξ-real-on-the-line fact (Lean prelude)
Establish `xi_real_on_critical_line : ∀ t : ℝ, (completedRiemannZeta (1/2 + t*I)).im = 0` (equivalently ξ(½+it) ∈ ℝ), from Mathlib's functional equation `completedRiemannZeta (1-s) = completedRiemannZeta s` + Schwarz reflection (`conj (Λ s) = Λ (conj s)`), evaluated at s = ½+it. If a direct Mathlib path is awkward, fall back to the Hardy Z-function form. This is the one genuine analytic sub-lemma of Stage 1.

### 4.2 The certificate
- Input: an interval [a,b] and sample points a = t₀ < t₁ < … < t_k = b with, for each i, a certified **real** rational box `[lo_i, hi_i] ∋ ξ(½+it_i)` (Stage 0).
- A sign change (hi_i < 0 and lo_{i+1} > 0, or vice-versa) between consecutive samples ⟹ by IVT a zero of the real continuous function t ↦ ξ(½+it) in (t_i, t_{i+1}).
- Emitted theorem: `xi has at least N zeros on the critical line in [a,b]`, stated as the existence of N distinct t values in [a,b] with ξ(½+it)=0, or as a lower bound on the cardinality of the zero set. Proof: `xi_real_on_critical_line` + `intermediate_value_Icc` per sign-change interval + disjointness.
- The sign facts (`hi_i < 0`, `lo_{i+1} > 0`) are rational inequalities discharged by `norm_num`; where a sign must hold over a box the `box_robust` machinery applies. Each emitted theorem carries the `statement_match` gate.

**Deliverable:** *the first kernel-verified count of Riemann-ξ zeros on the critical line in an interval* — literally "finding the nontrivial zeros," honestly framed (a lower bound via odd-order sign changes; `conjecture1_proved = False`).

## 5. Stage 2 — total count via the argument principle (CRUX, feasibility-gated)

**Feasibility probe FIRST** (a scoped spike, its own go/no-go): can the kernel lemma
> ξ analytic on B, ξ ≠ 0 on ∂B, and the finite sequence of boundary enclosures winds N times around 0  ⟹  ξ has exactly N zeros (with multiplicity) in B
be assembled from Mathlib's argument-principle / `ValueDistribution.LogCounting` / `Complex.circleIntegral` machinery? Read the two Mathlib files, attempt the reduction on a toy analytic function (e.g. a polynomial with known zeros) before any ζ-specific work.

If GO:
- `enclose ξ on ∂B` (Stage 0) as a finite sequence of complex boxes, none containing 0.
- A **discrete winding certificate**: consecutive boxes constrain the argument change to < π (checkable rational condition), so the total argument change / 2π = N (integer) is determined by the finite data.
- Emitted theorem: `ξ has exactly N zeros (with multiplicity) in box B`, chaining the winding certificate into the argument-principle kernel lemma.

If NO-GO: record the obstruction; Stage 1 remains the standing deliverable, and Stage 2 is deferred to a Mathlib-capability milestone.

## 6. Stage 3 — localization (RH-in-a-box)

If Stage 1 gives `≥ N_line` zeros on the line in [a,b] and Stage 2 gives `= N_total` total zeros in the box B ⊇ line-segment, and `N_line = N_total`, then every zero of ξ in B is simple and on the critical line. Emitted theorem: `all zeros of ξ in B lie on Re s = 1/2` — a kernel-verified RH-holds-in-B certificate (Turing's method, kernel-checkable). Honest ceiling: finitely many zeros; not a proof of RH.

## 7. Data flow

```
box B (or line interval [a,b]) + precision
   |  Stage 0: enclose_xi on sample points / boundary  -> complex/real rational boxes (non-kernel input)
   v
Stage 1: sign changes on the line  ->  ">= N_line zeros on Re=1/2 in [a,b]"   (IVT + xi_real_on_line + box_robust)
Stage 2: winding of boundary image ->  "= N_total zeros in B"                 (argument-principle kernel lemma)  [gated]
   |
   v  if N_line == N_total
Stage 3: "all zeros of xi in B are on Re=1/2"  (+ statement_match gate)
   |
   v  lake build (kernel) -> sorry-free, axioms {propext, Classical.choice, Quot.sound}
```

## 8. Testing

- **Stage 0:** complex enclosure contains an mpmath oracle at real AND complex points (ξ, ζ); width shrinks with precision; outward rounding; python-flint-absent guard. Negative control: a deliberately-wrong box fails containment.
- **Stage 1:** on a KNOWN interval (e.g. the first few zeros near t≈14.13, 21.02, 25.01), the sign-change count matches the known number of zeros; the emitted Lean builds sorry-free with clean axioms; a no-sign-change interval yields N=0; the `xi_real_on_line` prelude is sorry-free. Negative control: fabricated non-alternating boxes emit no zeros.
- **Stage 2 (if GO):** the winding certificate reproduces the known zero count on a toy polynomial and on a small ζ box; the argument-principle kernel lemma builds sorry-free.
- **CI + SoC-safe Lean:** `lake exe cache get` before `lake build`; new Lean in an isolated example target; per-example CI job (`pip install ... python-flint mpmath`, `generate.py --check`, cache get, build). `python-flint` pinned for reproducible enclosure literals.

## 9. Scope

**In scope now:** Stage 0 + Stage 1 (complex enclosure + the kernel-verified on-line zero count), plus the Stage-2 feasibility probe.
**Gated / deferred:** Stage 2 total-count winding certificate and Stage 3 localization — built only if the Stage-2 probe returns GO.
**Out of scope:** any claim toward proving RH; an effective/uniform result over all heights; the Vinogradov–Korobov / Weil-positivity frontier.

## 10. Honest ceiling

Every artifact carries `conjecture1_proved = False`. The strongest achievable end-state (Stage 3) is a kernel-verified statement that **all nontrivial zeros in a specific finite box lie on the critical line** — RH verified in that box, not proven in general. The coefficient/value enclosures are Arb-certified non-kernel input, documented as such.

## 11. Location & first-class-emitter conventions

Built off `origin/main` in the isolated worktree; new emitters follow the first-class pattern (dataclass + `certify_<kind>_point` refusal + `emit_body` + `<kind>_family` + `certify.py` registration + `__init__` export + example + kernel Lean + CI job); Lean examples are isolated `lean_lib` targets. Land via PR against `main`.
