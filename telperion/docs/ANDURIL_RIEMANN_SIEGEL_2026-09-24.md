# ANDÚRIL: Riemann–Siegel with an explicit C0 remainder, kernel-checked (2026-09-24)

This note covers the first load-bearing Riemann–Siegel bricks on the `zeta_reflection` island. The Euler–Maclaurin kernel ladder stalls at about 10^4, because the EM sum length grows linearly with height. Riemann–Siegel needs only about sqrt(t/2π) terms. That's the route that gets the ladder to 10^5 and beyond. Nothing here is about RH itself. It is finite-height zero-verification infrastructure, and `conjecture1_proved = False`.

## What's proved (all axiom-clean: `[propext, Classical.choice, Quot.sound]`)

**B2: Riemann's integral representation** (`RSInt.riemann_siegel_integral`, `RS_B2.lean`). For every complex `s` that is not an odd positive integer, and for `c₁ ∈ (N, N+1)`, `c₂ ∈ (M, M+1)`:

    riemannZeta s = Σ_{n≤N} n^(-s) + χ(s) Σ_{m≤M} m^(s-1) − lineUp c₁ (rsG·x^(-s)) + χ(s)·lineDn c₂ (rsH·x^(s-1))

This is stated about Mathlib's `riemannZeta` itself. The route avoids both the residue theorem and Hankel contours. It uses Mathlib's rectangle Cauchy theorem on strips, then crosses each pole with `dslope` and the kernel's difference equation. After that come the Mordell closed form, a Mellin/Fubini step against the Gamma integral, the Bose series, and the identity theorem to leave Re s > 2.

**C0: Riemann's Ψ** (`RSInt.rsJ_C0`, `RS_C0.lean`). The saddle-point integral evaluates to Gabcke's first coefficient: `2 Re(e^{-iπ/8} J(p)) = cos(2π(p² − p − 1/16)) / cos(2πp)`.

**B3: the remainder bound** (`RSInt.rs_remainder_C0`, `RS_B3Bound.lean`). For `t ≥ 10000`, `0 < p`, `cos 2πp ≠ 0`, and any phase `φ` within `1/t` of the Stirling theta main term:

    |2 Re(e^{iφ} R(t)) − (−1)^(N+1) (t/2π)^(−1/4) Ψ(p)| ≤ 2 t^(−3/4)

with `N = ⌊√(t/2π)⌋` and `p = √(t/2π) − N`. The constant 2 is deliberately loose. An independent mpmath check over 40 heights in [10000, 11450] measured the worst C0-corrected remainder at 0.104·t^(−3/4), a margin of about 20× (the lane first estimated 0.02). Gabcke's 0.127 is not claimed. `rsJ_C0` also assumes 0 < p < 1 and cos 2πp ≠ 0, explicitly in its statement.

**Bridge** (`RSInt.rs_Z_C0`, `RS_Bridge.lean`). The phase hypothesis is discharged with no extra assumption, using the already-proved theta branch (`RSDesignTheta`) and the polar form of Γℝ. The result is the Riemann–Siegel formula for Hardy's Z, expressed through Mathlib's `completedRiemannZeta`: the main sum plus the C0 correction approximates `Re Λ(1/2+it)/|Γℝ|` to within `2 t^(−3/4)` for `t ≥ 10000`.

## Size and checks

- **B2:** 2,967 lines over six modules: Strip, Kernel, Mellin, Fold, Entire, B2.
- **B3:** 1,730 lines: C0, B3, B3Bound, Bridge.
- **Guards:** 186 + 47 `#print axioms` directives (`RS_AxiomGuard`, `RS_AxiomGuardB3`), all standard.
- **Other checks:** no `sorryAx`, no forbidden tokens.
- **Independent rebuild:** I rebuilt everything on a main-based branch (8678 jobs), with the same axiom output.
- **CI:** both guards are wired into the required `zeta-reflection-compiles` job. It has floors of 186 and 47, and the four headline theorems are listed as registry theorems.

## What's left before a 10^5 kernel ladder

1. **B4:** an in-kernel evaluator for the RS main sum and Ψ. It needs interval enclosures of `n^(-1/2)`, `t log n mod 2π`, `cos`, and `(t/2π)^(-1/4)`, with `|cos 2πp|` bounded below. It reuses the island's Arb4/DIntv kernels. Estimate: 1–2k lines.
2. **B5:** a band sign certificate, `|Z_main| > 2 t^(-3/4)` plus the IVT, glued to the existing Turing-band / argument-principle counting at T = 10^5. Estimate: 0.6–1.5k lines.
3. **The seam at t = 10^4.** The EM ladder already reaches 8000 (`AND.ladder_h8000_kernel`). Either extend it to 10^4, or re-tune the constants: a ≥ 18 gives t ≳ 2000, about 150 lines.
4. **Compute.** N(10^5) ≈ 1.38·10^5 zeros, so at least 3·10^5 sample points with about 126 terms each. This is the main risk.

## Proposed registry nodes (not yet registered; grants wait on #607)

| node | anchor | guard | depends on |
|---|---|---|---|
| `AND.rs_representation` | `RSInt.riemann_siegel_integral` | `RS_AxiomGuard` | none |
| `AND.rs_c0_identity` | `RSInt.rsJ_C0` | `RS_AxiomGuard` | none |
| `AND.rs_remainder_c0` | `RSInt.rs_remainder_C0` | `RS_AxiomGuardB3` | the two above |
| `AND.rs_Z_c0` | `RSInt.rs_Z_C0` | `RS_AxiomGuardB3` | `AND.rs_remainder_c0`, `AND.theta_branch` |

---

## Lane log (verbatim)

# LANE_NOTES_RS -- lane RS (worktree arda-rs, zeta_reflection island, Lean v4.32.0)

conjecture1_proved = False.  Finite-height zero verification infrastructure only.

## Task (2026-09-24)
First load-bearing Riemann-Siegel bricks, kernel-checked:
1. B2: Riemann's integral representation of zeta(s) for general complex s, with the residue
   bookkeeping zeta = sum_{n<=N} n^-s + chi(s) sum_{m<=M} m^(s-1) + remainder integrals.
2. B3: an explicit remainder bound on the critical line (or, if B2 is the session, a precise
   statement + design).

## Rules held
- Git read-only.  No edits under telperion/missions/.  New files only, prefix `RS_`.
- No sorry / admit / native_decide / axiom / opaque / implemented_by / ofReduceBool / extern.
- Heavy Lean via scratchpad/leanlock.sh; scratch under scratchpad/rs.
- lakefile.toml: append-only `[[lean_lib]]` entries (no defaultTargets edit).

## Route chosen for B2 (no residue theorem, no Hankel contour)
- Lines: lineUp c F = int F(c + v(1+i))(1+i) dv (slope +1), lineDn c F = int F(c + v(1-i))(1-i) dv.
- Kernels: rsG = e^{i pi x^2}/(e^{i pi x} - e^{-i pi x}), rsH = e^{-i pi x^2}/(same).
- Strip Cauchy (Mathlib rectangle theorem + limits) => line independence inside a gap.
- Pole crossing WITHOUT residues: remove the pole with dslope, and get the jump of the bare
  kernel from the difference equation rsG(x+1) = rsG x + e^{i pi (x^2+x)} + Fresnel integral.
- Mordell closed form: lineUp c (rsG e^{-xy}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.
- Mellin step (Fubini with the complex-scaled Gamma integral) + Bose series -> Gamma zeta,
  folding of the chi-side line through 0 -> identity for Re s > 2 -> identity theorem.
- Numerics (untrusted, design only): scratchpad/rs/check_b2.py verifies every identity to ~1e-30.

## Log
- RS_Strip.lean (337 lines): strip Cauchy, lineUp/lineDn, line independence.  Compiles clean.
- RS_Kernel.lean (940 lines): kernels, difference equations, Gaussian bounds, Fresnel/Gauss line
  integrals, same-gap + pole-crossing lemmas (both slopes, lineDn by conjugation), Mordell closed
  form.  Compiles clean.
- RS_Mellin.lean (594 lines): complex-scaled Gamma integral (identity theorem), Mellin/Fubini step,
  Mordell split, Bose integral = (1+i)^-s Gamma zeta (geometric series + termwise), chi-side kernel.
- RS_Fold.lean (247): continuity of rsH x^(s-1) at 0 (Re s > 2), folding of the chi-side line,
  moving it to c in (0,1).
- RS_Entire.lean (377): generic parametric holomorphy; both line integrals entire in s; rsChi and
  its Gamma identities (reflection + duplication).
- RS_B2.lean (472): identity for Re s > 2 -> identity theorem on C \ {1,3,5,...} -> residue
  bookkeeping -> HEADLINE `RSInt.riemann_siegel_integral`; critical line:
  `completedRiemannZeta_eq_rs` (completed zeta = 2 Re(Gammaℝ (S + R))) and
  `completed_re_eq_rs_cos` (Z-form with the island's polar phase).
- B2 TOTAL: 2,967 lines, all six modules build; `#print axioms` of the headlines:
  [propext, Classical.choice, Quot.sound].
- B3 numerics (scratchpad/rs/check_b3.py, untrusted): Z = main + 2 Re(e^{i theta} R_N) to 1e-27;
  2 Re(e^{-i pi/8} J(p)) = Psi(p) (tau=2 Mordell, 12 digits); remainder after C0 ~ 0.02 t^(-3/4).

## B3 (2026-09-24, same session) -- PROVED
- RS_C0.lean (512): Riemann's Psi = Gabcke's C0 from the tau = 2 Mordell integral:
  `RSInt.rsJ_C0` : 2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p), 0 < p < 1.
  Route: Gaussian Fourier on the (1-i) line + Fubini + inner tau = 1 Mordell + outer split
  (conjugate Mordell + one pole crossing) + symmetry rsJ(1-p) = rsJ p.
- RS_B3.lean (304): exact saddle-point reduction. `rsRem_factor` (remainder line moved to the saddle
  a = sqrt(t/2pi), stationary phase factored out), `rs_phase`, `rs_remainder_exact`:
  2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
    = (-1)^(N+1) a^(-1/2) [2 Re(e^{-i pi/8}(e^{i delta}-1) rsJ p) + 2 Re(e^{i(delta-pi/8)} rsE1 a p)].
- RS_B3Bound.lean (826): the analytic estimates + THE B3 HEADLINE `RSInt.rs_remainder_C0`:
  for t >= 10000, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, |phi - thetaMain t| <= 1/t,
      |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) (t/2pi)^(-1/4) Psi(p)| <= 2 t^(-3/4)
  (a-form `rs_remainder_C0_alpha`: <= (2/5) a^(-3/2)).  Ingredients: |rsPhi - 1| <= e e^e near the
  saddle (complex log Taylor), the saddle is a global max on the steepest-descent line
  (`saddle_arg_le`, derivative sign), |rsD| >= 2 pi |Im|, |rsD| >= 2 on the midline, |rsJ p| <= 4
  (strip shift to the midline), |rsE1 a p| <= (9/50)/a for a >= 39 (near |v|<=a/9 / far split,
  Gaussian moments, e^{-x} <= 120/x^5).  Budget: 0.36/a + 0.04/a <= 0.4/a vs the target 0.5/a.
  Gabcke's 0.127 t^(-3/4) is NOT claimed; our constant 2 is ~100x the true size (numerics: the
  C0-corrected remainder is ~0.02 t^(-3/4) on t in [200, 20000]).
- RS_Bridge.lean (88): `RSInt.rs_Z_C0` -- the phase discharged hypothesis-free with the island's
  ThetaConverge branch + ZeroSignDecomp_t14 polar form + RSTheta Stirling bracket:
  exists M > 0, phi with Gammaℝ(1/2+it) = M e^{i phi}, |phi - thetaMain t| <= 1/t and
  |Re Lambda(1/2+it)/M - (2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1)(t/2pi)^(-1/4) Psi(p))|
    <= 2 t^(-3/4),  t >= 10000.   (Re Lambda / M = Hardy Z; its sign = sign of gLine t.)
- Guards: RS_AxiomGuard.lean (186 directives, B2 + C0) and RS_AxiomGuardB3.lean (47 directives,
  RS_B3 + RS_B3Bound + RS_Bridge): all 233 print [propext, Classical.choice, Quot.sound].
- Forbidden-token scan: no sorry/admit/native_decide/axiom/opaque/implemented_by/ofReduceBool/extern
  in code (docstring mentions only, backtick-quoted).  No emoji.
- Line counts: B2 2,967 (Strip 337, Kernel 940, Mellin 594, Fold 247, Entire 377, B2 472);
  B3 1,730 (C0 512, B3 304, B3Bound 826, Bridge 88); guards 297.  Lane total 4,994.

## Remaining to a kernel ladder at height 1e5 (revised estimate)
- B4: in-kernel RS main-sum evaluator (interval enclosures of n^(-1/2), t log n mod 2 pi, cos,
  (t/2pi)^(-1/4), Psi(p) with |cos 2 pi p| bounded below; theta from RSTheta.theta_bracket), reusing
  the island's Arb4 / DIntv kernels, + soundness against `rs_Z_C0`: 1,000-2,000 lines.
- B5: `checkBandRS` sign certificate (sample t_i, verify 0 < p, cos(2 pi p) ≠ 0, |Z_main| > 2 t^(-3/4),
  IVT via continuity of Re Lambda on the line) + glue to the island's zero-counting (Turing band /
  argument principle) at T = 1e5: 600-1,500 lines.
- Seam: the proved range starts at t = 10000; below it the existing EM ladder must cover, or re-tune
  the constants (a >= 18 gives t >= ~2000) for ~150 lines.
- Emitter (untrusted Python) + generated certificates.  Compute is the dominant risk: N(1e5) ~ 1.38e5
  zeros, >= 3e5 sample points x N = 126 terms each.
- Estimate: 3,000-5,000 further Lean lines, 2-4 sessions of proof engineering plus the kernel
  compute budget.  B6 (off-line zero exclusion at 1e5) is not RS-specific.
