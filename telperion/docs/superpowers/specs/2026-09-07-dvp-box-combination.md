# Design: dVP + Box-Localization = All Nontrivial Zeros up to Height T on the Critical Line

**Date:** 2026-09-07
**Status:** Design (pre-plan)
**Branch:** `rh/dvp-box-combination` (worktree `/Users/peterwmurphy/telperion-zeroloc`, off `origin/main`)
**Predecessors (all merged):** PR #285 (RH-in-a-box fixed box), PR #312 (parameterized RH-in-a-box + T=100 milestone), PR #316 (EFFECTIVE dVP rate `dlvp_zeta_region_rate_effective`, explicit `dlvpRateC`).
**Honesty flag:** `conjecture1_proved = False`. This is the COMPLETE finite Turing statement -- all nontrivial zeros up to a finite height T lie on Re=1/2 -- kernel-verified. It is NOT a proof of RH.

---

## 1. Motivation

PR #312 kernel-certifies "all nontrivial zeros in a sigma-BAND `[sigma0,sigma1]x[0,T]` lie on Re=1/2." The honest gap: it says nothing about zeros OUTSIDE the band. PR #316 closes exactly that gap unconditionally and effectively: `dlvp_zeta_region_rate_effective` proves every zero `beta+i*gamma` (with `3/4 <= beta < 1`, `|gamma| >= 55/16`, multiplicity `k`) satisfies `beta <= 1 - dlvpRateC/log|gamma|` with `dlvpRateC` an EXPLICIT closed-form positive constant (`dlvpRateC_pos` proved, CI-axiom-guarded). Because `dlvpRateC` is effective, the outer-band edge is now a computable number, so a concrete box can be placed to capture every zero. Combining the two tracks + the functional equation yields the COMPLETE statement: all nontrivial zeros up to height T lie on the critical line -- concretely, kernel-checked.

Earlier (non-effective-c) analysis suggested only a reduction theorem was reachable; PR #316 lifts that barrier. This spec targets the concrete certificate, with a Task-1 feasibility probe guarding the one implementation risk (extreme-precision box edge near the pole).

## 2. Trust boundary and honest ceiling

- **Kernel, no Arb input:** the dVP confinement (`dlvp_zeta_region_rate_effective`, #316), the functional equation (Mathlib `completedRiemannZeta`), the multiplicity bridge (Section 5), and the final union argument.
- **Documented NON-KERNEL Arb input (theorem hypotheses):** the box winding integer N, edge non-vanishing on the box boundary, and the value enclosures behind the on-line sign changes -- exactly the PR #285/#312 trust boundary.
- The kernel proves the implication `(box winding = on-line count) & (dVP+FE confinement) => all zeros up to T on Re=1/2`.
- `conjecture1_proved = False`. Strongest end-state: RH holds for all nontrivial zeros up to a specific finite height T (the complete Turing statement), NOT RH. The infinite limit remains the open problem (dVP's frontier `1 - c/log|gamma| -> 1` never reaches 1/2).

## 3. The combination theorem

`all_nontrivial_zeros_up_to_height_on_line` (name TBD), for a concrete rational `a` and height `T`:

```
GIVEN
  - the Arb bundle for the box B = [a, 1-a] x [0, T] (winding = 2*pi*i*N, edge non-vanishing,
    integrability) and the on-line Finset T_on of N_line zeros with N_line = N  -- i.e. the
    hypotheses of RHInBox.rh_in_box_of_certificate instantiated at box B;
  - the effective-rate check `a <= dlvpRateC / Real.log T`  (a concrete inequality, discharged by
    norm_num against the explicit dlvpRateC and a rational lower bound on log T);
CONCLUDE
  forall rho, riemannZeta rho = 0 -> 0 < rho.im -> rho.im <= T -> rho.re = 1/2.
```

Proof:
1. **Confinement.** For any nontrivial zero `rho = beta + i*gamma` with `0 < gamma <= T`:
   - `beta in (0,1)` (critical strip: Mathlib `riemannZeta_ne_zero_of_one_le_re` gives no zeros with `Re >= 1`; the functional equation gives none with `Re <= 0`).
   - Multiplicity `k := divisor riemannZeta (ball (2+i*gamma) (11/8)) rho >= 1` from `riemannZeta rho = 0` (Section 5 bridge).
   - RIGHT edge: if `beta >= 3/4`, `dlvp_zeta_region_rate_effective` gives `beta <= 1 - dlvpRateC/log|gamma| <= 1 - dlvpRateC/log T <= 1 - a`. (`|gamma| >= 55/16` holds: the first nontrivial zero is at `gamma ~ 14.13`; below `55/16 ~ 3.44` there are no nontrivial zeros, so `0 < gamma <= T` with a zero implies `gamma >= 14 > 55/16`.) If `beta < 3/4 <= 1 - a` (since `a` is tiny), the bound `beta <= 1-a` holds trivially. Either way `beta <= 1 - a`.
   - LEFT edge: apply the functional-equation symmetry (`beta -> 1-beta`) to get `beta >= a`.
   - Hence `a <= beta <= 1 - a`: `rho in B`.
2. **Localization.** `RHInBox.rh_in_box_of_certificate` (PR #312, on main) applied to the box `B` with the supplied Arb bundle: every zero in `B` has `Re = 1/2`.
3. Combine: every nontrivial zero up to height T is in `B` (step 1) and on the line (step 2).

The regression (concrete instantiation) is the T=100 certificate (Section 6).

## 4. Feasibility probe (Task 1, GATES the concrete build)

`dlvpRateC / log 100 ~ 1.6e-6`, so a valid `a` is tiny (e.g. `a = 1/10^6`), and the box `[1e-6, 1-1e-6]` reaches `Re ~ 1 - 1e-6`, very close to the pole `s = 1`. Risks to confirm BEFORE the full build:
- **Blaschke-ball pole exclusion:** the driver's `choose_ball` picks `R^2` as the exact-rational midpoint between the farthest box corner and `s=1`; the exclusion window is `~a/T` (tiny but nonzero). Confirm the emitted `norm_num`/`nlinarith` geometry discharges at `a ~ 1e-6`.
- **Arb winding over the wide box:** `zeta` on the `Re ~ 1e-6` edge grows like `|t|^{1/2}` (functional equation) -- polynomial, not the Gamma-exponential problem, but confirm `enclose_zeta_segments` + the half-plane witnesses certify `N = 29` over `[1e-6, 1-1e-6]x[0,100]` at a feasible segment count and precision.
- **Effective-rate `norm_num`:** confirm `a <= dlvpRateC / log 100` is dischargeable -- needs a rational LOWER bound on `dlvpRateC` (unfold its closed form: `1/(112*16*dlvpRateK)` with `dlvpRateK` from `pi, log(23/22), log(15/(2-pi^2/6))`) and a rational UPPER bound on `log 100` (e.g. `log 100 < 47/10`). This is a real arithmetic step -- the probe verifies it is tractable.

If the probe is GO: proceed to the concrete T=100 build. If NO-GO (extreme precision breaks Arb or norm_num): fall back to the reduction-theorem framing (the combination stated with `a <= dlvpRateC/log T` as a hypothesis rather than a discharged concrete instance) -- still a real kernel result, honestly flagged.

## 5. The multiplicity bridge (kernel)

`dlvp_zeta_region_rate_effective` takes `divisor riemannZeta (ball (2+i*gamma) (11/8)) rho = k` with `1 <= k` as a hypothesis. For a self-contained "no off-line zero" argument, derive `k >= 1` from `riemannZeta rho = 0`:
- `riemannZeta` is analytic at `rho` (`rho != 1`; `differentiableAt_riemannZeta`) and not identically zero, so `analyticOrderAt riemannZeta rho >= 1` when `riemannZeta rho = 0` (Mathlib `AnalyticAt.analyticOrderAt_pos_iff` / `analyticOrderNatAt`).
- `divisor riemannZeta (ball ...) rho = analyticOrderAt` at a zero inside the ball (via `MeromorphicOn.divisor` on the analytic-in-ball function), giving `k >= 1`.
This is a short order-machinery lemma. If a Mathlib gap blocks it after real effort, carry `k >= 1` as a documented hypothesis (honest, small residual) rather than fake it.

## 6. Concrete T=100 certificate + range

- Instantiate the combination theorem at `a = 1/10^6` (or the largest tractable rational `<= dlvpRateC/log 100`), `T = 100`: `RHInBox_all_zeros_h100` -- **all nontrivial zeros with `0 < Im <= 100` lie on Re=1/2**, kernel-checked, `#print axioms` = `{propext, Classical.choice, Quot.sound}`. The box winding + on-line count = 29 (the full classical count to height 100).
- Reuse the PR #312 `--box`/`--height` driver for the wide box's Arb data + emitted instantiation; the driver already picks the Blaschke ball and refuses invalid boxes.
- **Range:** T=100 is the guaranteed target. Higher T is bounded by the same O(N^2) distinctness cost (PR #312 probe) AND the wider Arb winding; a brief probe reports the achieved ceiling. No finite T is a proof of RH.

## 7. CI axiom-guarded tier (elevation)

Add an axiom-guard job (mirroring `AxiomGuardDlvp.lean`/`AxiomGuardRH` on main): a `lake env lean` scratch that runs `#print axioms` on the RH-in-box family -- `RHInBox.rh_in_box_of_certificate`, `rh_in_box_10_35`, the T=100 milestone theorem, the new combination theorem, and `RHInBox_all_zeros_h100` -- and FAILS on `sorryAx` (or any axiom outside `{propext, Classical.choice, Quot.sound}`). This earns the "CI-axiom-guarded tier" phrase for the RH-in-box results (the existing `zeta-...-compiles` job builds + drift-checks but does not axiom-guard). Negative control: an injected `sorry` fails the guard.

## 8. Components and files

- **New Lean:** `examples/zeta_zero_localization/lean/ZetaZeroConfinement.lean` (the dVP+FE confinement + multiplicity bridge -> "every nontrivial zero up to T is in [a,1-a]"); `examples/zeta_zero_localization/lean/AllZerosUpToHeight.lean` (the combination theorem `all_nontrivial_zeros_up_to_height_on_line` + the T=100 instantiation). Imports the on-main `DlvpZetaRateEffective` (dVP), `RHInBox` (box localization), and Mathlib (functional equation).
- **Driver reuse:** `examples/zeta_zero_localization/generate.py --box 1/1000000,999999/1000000,0,100` (or a `--all-zeros-up-to T` convenience) emits the wide-box Arb bundle feeding the combination.
- **CI:** an `axiom-guard-rh-in-box` job (Section 7) + extend the zeta CI to build the new targets.
- **Docs:** `ZETA_ZERO_LOCALIZATION_STATUS.md`, `README.md`, `CHANGELOG.md` -- headline "all nontrivial zeros up to height 100 on Re=1/2"; the non-effective-c caveat REMOVED; the multiplicity-bridge status noted; `conjecture1_proved = False`.

## 9. Testing

- **Confinement:** the dVP+FE+multiplicity confinement lemma builds sorry-free, clean axioms; a nontrivial-zero-in-box unit check.
- **Combination theorem:** builds sorry-free, clean axioms; NON-CIRCULAR (the "on line" conclusion is derived from the box winding + confinement, not assumed); the `a <= dlvpRateC/log T` hypothesis is discharged concretely at T=100 (Task 1 confirms tractable).
- **T=100 certificate:** builds sorry-free, clean axioms; the winding N and on-line count both equal 29; drift-clean `generate.py --check`.
- **Axiom guard:** the new CI job fails on an injected `sorry` (negative control) and passes on the real proofs.
- **Optional-dep hygiene:** new flint/lake tests carry `@requires_flint`/`@requires_lake`.
- **SoC-safe Lean:** local builds OK; ALWAYS `lake exe cache get` before `lake build`; never a cold Mathlib compile.

## 10. Scope

**In scope:** the confinement lemma + multiplicity bridge; the combination theorem; the concrete T=100 "all zeros up to height 100 on the line" certificate (Task-1-probe-gated); the CI axiom-guard elevation; a brief higher-T probe.
**Gated:** the concrete T=100 build is gated on the Task-1 feasibility probe (extreme-precision box edge); NO-GO falls back to the reduction-theorem framing (combination with `a <= dlvpRateC/log T` as a hypothesis).
**Out of scope:** any claim toward proving RH; the infinite limit (dVP frontier never reaches 1/2); an effective result uniform in T beyond what the O(N^2) Lean cost allows; strengthening dVP to Vinogradov-Korobov.

## 11. Honest ceiling

Every artifact carries `conjecture1_proved = False`. The end-state is a kernel-verified statement that ALL nontrivial zeros of zeta up to a specific finite height T lie on the critical line -- the complete Turing verification, now with the outer bands closed by the EFFECTIVE dVP region rather than left as a documented gap. It extends the verified range; it is not a proof of RH. The winding integer, edge non-vanishing, and value enclosures remain Arb-certified non-kernel input; the dVP region, functional equation, and multiplicity bridge are kernel.
