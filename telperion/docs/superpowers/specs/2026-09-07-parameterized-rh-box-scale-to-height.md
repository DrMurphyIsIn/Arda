# Design: Parameterized RH-in-a-Box + Scale-to-Height-T

**Date:** 2026-09-07
**Status:** Design (pre-plan)
**Branch:** `rh/parameterized-box-scale` (worktree `/Users/peterwmurphy/telperion-zeroloc`, off `origin/main`)
**Predecessor:** `2026-09-06-zeta-box-localization-stage23-design.md` (RH-in-a-box for the fixed box `[2/5,3/5]x[10,35]`, MERGED as PR #285).
**Honesty flag:** `conjecture1_proved = False`. This extends the *verified range* of RH (Turing's method, kernel-checked) to arbitrary finite boxes and larger heights. **No finite box or height is a proof of RH.**

---

## 1. Motivation

PR #285 kernel-verified that all nontrivial zeros of the Riemann zeta function in the specific box `[2/5,3/5]x[10,35]` lie on the critical line, but the box corners are hard-coded and three of the capstone Lean files are hand-written with literal corners (`2/5`, `3/5`, `ball cB 13`, the `506.5>169` s=1-exclusion). This spec (a) turns the box into a parameter so any finite rational box is certifiable on demand, and (b) scales the certified height to `[2/5,3/5]x[0,T]` for T well beyond 35 — the same range-extension analytic number theorists perform, now as a kernel-checked artifact.

The winding number stays **Arb-carried non-kernel input** (the Task-9 ceiling from PR #285: Mathlib has no zeta argument principle, so the discrete-winding integer is certified by Arb, not re-proved in-kernel over ~30k segments). Consequently the Lean side grows only with the on-line zero count `~N(T)`, not with the boundary segment count.

## 2. Trust boundary and honest ceiling (unchanged from PR #285)

Documented **non-kernel input** (Arb ball arithmetic), carried as Lean theorem hypotheses: the winding integer `N`, edge non-vanishing on the box boundary, and the value enclosures behind the on-line sign changes. The **kernel proves the implication** `(winding = N) & (N_line distinct on-line zeros) & (N_line = N) & (region valid) => all zeros in the box on Re=1/2`. `conjecture1_proved = False`. The strongest end-state is "RH verified in box B / up to height T", never RH itself; the infinite limit is exactly the open problem (see predecessor spec).

## 3. Generic-corner core (the refactor)

Replace the three hand-written files (`BoxArgPrinciple.lean`, `BlaschkeBox.lean`, `BoxLocalization.lean`) with **one reusable Lean theorem** `rh_in_box_of_certificate`, quantified over the box corners and a Blaschke ball:

```
theorem rh_in_box_of_certificate
    (sigma0 sigma1 T0 T1 : Q)            -- rational box corners
    (c : C) (R : R)                       -- Blaschke ball
    -- box validity (per-box norm_num):
    (hbox : 0 < sigma0 and sigma0 < 1/2 and 1/2 < sigma1 and sigma1 < 1 and 0 <= T0 and T0 < T1)
    -- region conditions (per-box norm_num): box strictly inside ball, pole excluded
    (hball : boxB sigma0 sigma1 T0 T1 subset Metric.ball c R)
    (hs1  : (1 : C) notin Metric.ball c R)
    -- Arb-certified non-kernel data (per-box hypotheses):
    (N : Nat)
    (hwind : Bd_{partial B}(logDeriv riemannZeta) = 2*pi*I*N)      -- winding (Arb integer)
    (honline : exists distinct z_1 < ... < z_{N_line} in [T0,T1], zeta(1/2 + z_k * I) = 0)  -- Stage-1
    (hnz : zeta nonvanishing on partial B)                        -- edge non-vanishing (Arb)
    (hcount : N_line = N) :
    forall rho, rho in boxB sigma0 sigma1 T0 T1 -> riemannZeta rho = 0 -> rho.re = 1/2
```

The proof is the *same* PR #285 chain, generalized: the box argument principle (`box_residue_sum` + `rect_winding` + `rect_argument_principle` over the parameterized corners) gives `Bd = 2*pi*i*sum divisor`; `MeromorphicOn.extract_zeros_poles` over `ball c R` (with `hs1`, `hball`) gives the Blaschke split `logDeriv zeta = sum divisor/(z-rho) + E` with `E = logDeriv g` holomorphic on the box; combined with `hwind` and `hcount` and the counting-exhaustion argument yields the conclusion. The concrete `norm_num` facts that were literal-specific (s=1 exclusion, ball-contains-box) are now the hypotheses `hs1`/`hball`, discharged at each instantiation. **The merged capstone becomes one instantiation of this theorem** (regression test).

**Design note (Blaschke ball for a tall box):** for `[sigma0,sigma1]x[T0,T1]` pick `c = (sigma0+sigma1)/2 + i*(T0+T1)/2` and `R = dist(c, corner) + margin` so the box is *strictly* inside. The ball meets the real axis only near `Re=(sigma0+sigma1)/2`, so the pole at `s=1` and the trivial zeros stay outside (verified per-box by `norm_num`); `extract_zeros_poles` then sees exactly the nontrivial zeros in the ball. For `T0=0` the margin keeps the bottom corners strictly interior.

## 4. Per-box data pipeline (Python)

`generate.py` gains:
- `--box sigma0,sigma1,T0,T1` — certify an arbitrary rational box.
- `--height T` — shortcut for the family `[2/5,3/5]x[0,T]`.

For a requested box the driver: (1) computes the winding `N` via `enclose_zeta_segments` (Arb, adaptive segments; refuses if a segment straddles 0 or a step lacks a half-plane witness); (2) runs the on-line sign-change sweep over `[T0,T1]` at spacing below the zero gap `~2*pi/log(T1)` to extract the `N_line` distinct zeros; (3) computes edge-non-vanishing enclosures on the four sides; (4) chooses `(c,R)` with margin; (5) emits a **small per-box Lean file** that *instantiates* `rh_in_box_of_certificate` with the concrete corners and `(c,R)` (geometric hypotheses discharged by `norm_num`) and the Arb data (winding `N`, the emitted sign-change on-line zeros, edge non-vanishing) as the documented non-kernel hypotheses. It asserts `N_line == N` and REFUSES to emit if `N_line != N` (a fabricated/under-resolved box) or the box is invalid (contains `s=1`).

The already-emitting families extend to arbitrary corners: `xi_line_zeros` (the on-line chain, already sweeps `--a/--b`), `winding_count` (already boxed). `box_localization` becomes the instantiation emitter for the generic theorem.

## 5. Scale-to-height-T + milestone + probe

- **Milestone (guaranteed):** `--height 100` -> `[2/5,3/5]x[0,100]`, ~29 on-line zeros. The emitted `XiLineZeros` chain + capstone exhaustion over ~29 zeros builds comfortably.
- **Probe (best-effort):** push `--height 1000` (~649 zeros) and beyond; report the achieved ceiling. The binding constraint is the emitted Lean theorem size (the `~N(T)`-zero strictly-increasing chain + the exhaustion `Finset`), NOT the boundary segment count (winding is Arb-carried). Stop where `lake build` time/size becomes impractical and record the ceiling honestly.
- **Cost model:** Arb work grows `~T log T` (sign-change samples + adaptive winding segments), run in Python (minutes). Lean work grows `~N(T) ~ (T/2pi) log(T/2pi)`.
- **On-line resolution:** sign-change spacing must be finer than the min zero gap in `[0,T]` so every zero is bracketed and `N_line = N(T)` (the numerically-verified equality holds far past T=1000). If a sample interval fails to resolve two close zeros, the driver refines adaptively; if `N_line < N` persists it REFUSES (honest: the box is not fully resolved) rather than emit a false localization.

## 6. Components and files

- **New Lean:** `examples/zeta_zero_localization/lean/RHInBox.lean` — the generic `rh_in_box_of_certificate` (absorbing/​generalizing the logic of `BoxArgPrinciple`/`BlaschkeBox`/`BoxLocalization`). The three predecessor files remain (the merged milestone) but the generic theorem is the reusable core; the merged `[10,35]` result is re-expressed as an instantiation (regression).
- **Emitters:** extend `emit_box_localization.py` to emit the *instantiation* of `rh_in_box_of_certificate` for arbitrary corners + Arb data; extend `emit_winding_count.py` / `emit_xi_line_zeros.py` corner-parameterization where still literal.
- **Driver:** `generate.py` `--box` / `--height` modes + the per-box emit + refusals.
- **Enclosures:** reuse `arb_enclosure.enclose_zeta_segments`, `enclose_lambda` (sign changes); add a thin `--height` boundary/​sweep helper if needed.
- **Docs/CI:** update `ZETA_ZERO_LOCALIZATION_STATUS.md`, `README.md`, `CHANGELOG.md` (parameterized + T=100 milestone + achieved ceiling); add/extend a CI job that builds the generic theorem + the T=100 instantiation (warm `lake exe cache get`).

## 7. Testing

- **Generic theorem:** regression-instantiate on the original `[2/5,3/5]x[10,35]` box (must reproduce the merged capstone, sorry-free, clean axioms) AND on `[2/5,3/5]x[0,100]`.
- **Negative controls:** `N_line < N` (a fabricated off-line zero making the total exceed the on-line count) is REFUSED at certification; an invalid box (contains `s=1`, or `sigma`-range excluding `1/2`) is REFUSED.
- **Drift:** `generate.py --check` byte-stable for each emitted box (original + T=100).
- **Axioms:** every emitted/instantiated theorem sorry-free, axioms `{propext, Classical.choice, Quot.sound}`.
- **SoC-safe Lean:** local builds OK (operator-confirmed); ALWAYS `lake exe cache get` before `lake build`; never a cold Mathlib compile. CI mirrors.
- **Optional-dep hygiene:** all new flint/lake-dependent tests carry the `requires_flint` / `requires_lake` skip guards (per the PR #285 CI fix) so the lightweight `unit` job stays green on the new tests.

## 8. Scope

**In scope:** the generic-corner theorem; the `--box`/`--height` driver + per-box instantiation emit; the T=100 milestone; a best-effort probe of higher T with an honestly-reported ceiling; regression on the original box.
**Out of scope:** any claim toward proving RH; the infinite limit (structurally the open problem — see predecessor spec S.1); an in-kernel discrete-winding proof over the segments (the Task-9 ceiling stands — winding remains Arb-carried); boxes crossing `Re=1` (the pole) or the trivial zeros; even-order / unresolved on-line zeros (the driver REFUSES rather than mis-certify).

## 9. Honest ceiling

Every artifact carries `conjecture1_proved = False`. The end-state is a kernel-verified "RH holds in box B" / "RH holds up to height T" for arbitrary finite B / finite T — extending the verified range, not proving RH. The winding integer, edge non-vanishing, and value enclosures are Arb-certified non-kernel input; the kernel proves the generic implication.
