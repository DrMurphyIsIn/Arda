# LANE_NOTES_crux3: a height-local band certificate that Davenport-Heilbronn fails

conjecture1_proved = False. Nothing here proves, reduces, or is equivalent to RH. The result is a
positivity statement on a 2-dimensional band of tests at one window, which makes it an instance
statement. It certifies that the explicit-formula data up to x ≈ 57 leaves no off-line zero visible at
height about 86, at the window's resolution. Every one-prime surgery at a prime p0 > 57 fools it (the
fooling identity).

- Lane prefix: `Crux3_`.
- Worktree: `/Users/peterwmurphy/arda-crux3`, branch `cl/crux3`. The island is rvm_bridge, on Lean v4.33.0-rc2.
- Research directory: `telperion/research/Crux3_band_certificate/` (scripts plus README).
- Note: `telperion/docs/Crux3_BAND_CERTIFICATE_2026-09-24.md`.
- Scratch: `/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/crux3`.
  It holds `lean/*.lean` (development copies) and the same Python.

## Status log
- 2026-09-24. Part (a): separation found and validated against both zero sides.
- Part (b): `Crux3.band_floor` is kernel-checked and hypothesis-free on the registry vocabulary.
- Part (b), D side (later on 2026-09-24): D's failure is now kernel-checked as well.
  - `Crux3.dh_band_negative`: `Re weilFormD w (v * v~) <= -(1/2)||v||^2` at `c = (-3, 2)`.
  - `Crux3.band_separation`: both sides on the same nonzero test.
  - `Crux3.band_separation_cD`: the same at the closed-form weights `cD`, so the hypothesis is not vacuous.
  - The only hypothesis is the defining identity of D's weights.
- Registration: 7 modules, all registered as `lean_lib`s.
  - `AxiomGuardRvMBridge` imports `Crux3_BandCert` and `Crux3_BandDH`, inserted into the import block;
    the prints are appended.
  - 54 Crux3 prints, all `[propext, Classical.choice, Quot.sound]`.
  - Whole guard: 1030 reports, no `sorryAx`, and nothing non-standard. `lake build AxiomGuardRvMBridge` is green.
  - The drift check `generate.py --check` passes.
- D's value is also Arb-certified (`-0.6546`). Part (c): partial no-go at the round-2 target `x = 40`,
  with numerical evidence.
- Git: read-only, nothing committed.

## (a) The separation (COMPUTED; cross-checked against both zero sides)

The test space is `V = span{cos(k1 u), cos(k2 u)}` restricted to `[-A, A]`:
- `A = 9π/14`, so the window is `x = e^{2A} = e^{9π/7} = 56.780`;
- `k1 = 763/9 = 84.78` and `k2 = 259/3 = 86.33`.

These are Dirichlet cosines: `kA = π(m + 1/2)` with `m = 54, 55`, so every test is continuous. The band's
spectral mass sits at `|t|` in [83.2, 87.9], centre `r = 85.56`, width `B ≈ 2.3`.

The Weil form is `Q = Pole + Arch - Prime`, from the explicit formula with no zeros used. Values are in units of `‖v‖²`:

| function | λ_min(Q on V) | arch part (eigenvalues) | comb part, top eigenvalue | zero-side check |
|---|---|---|---|---|
| zeta | +0.69889 | [2.596, 2.617] | 1.919 | 0.6988851 (2000 zeros + tail) |
| D (DH) | -0.65462 | [4.206, 4.226] | 4.863 | -0.65464 (zeros to 200 + tail) |

D's negativity comes from the off-line quadruple `0.8085 ± 85.699i`. It contributes `-1.0459`, against
`+0.3896` from all on-line zeros. The other off-line pairs contribute less than `3e-4`.

In round-2 section 4.3 language:
- zeta: `A_B(r) = 1.919 < Ψ_0 ≈ 2.60` on the band;
- D: `A_B^D(r) = 4.863 > Ψ_0^D ≈ 4.21`;
- for scale, the pointwise comb mass is `A_L = 24.4`.

Detection horizons for D's off-line zeros, using height-local complex bands of at most 6 free modes (`horizon.py`):

| γ | β | first x (band-local) | for comparison |
|---|---|---|---|
| 85.699 | 0.3085 | 42.1 | full window: x ≈ 31 (κ-certify) |
| 114.163 | 0.1508 | 76.5 | |
| 166.479 | 0.0744 | 140.7 | |
| 176.702 | 0.2243 | 96.1 | |

At x = 40, D's least band eigenvalue is `+0.113, +0.111, +0.110, +0.103, +0.095` for d = 4, 6, 8, 12, 16 modes
near 86 (spacing at least 1.2). At x = 33 it is +0.46. At x = 42.5 it is -0.03 to -0.05. At x = 40, D's full-window
negative eigenvector is delocalised: it has mass at |m| = 9, 12, 17, 23 (heights 15 to 40) as well as at 50 and 51.

So round 2's target, `κ_ζ(40) = 0` beside `κ_D(40) ≥ 2`, **cannot** be reached height-locally. The first
height-local separation is at x ≈ 42. A robust two-mode separation (margins above 0.6) first appears at x ≈ 57.

## (b) Kernel: `Crux3.band_floor` (hypothesis-free)

```lean
theorem band_floor (c1 c2 : ℝ) :
    (1 / 2 : ℝ) * (∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2)
      ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re
```

`bandTest c1 c2 u = c1 cos(763u/9) + c2 cos(259u/3)` on `[-9π/14, 9π/14]`, and 0 outside.
`WeilForm.weilForm = archSide - primeSide`, ZhuSymbol's mirror of the registry vocabulary.

The same certificate in round-2 form:
- `band_comb_le`: `Re primeSide ≤ 1.92 ‖v‖²`;
- `band_arch_ge`: `Re archSide ≥ 2.49 ‖v‖²`.

Modules:
- `Crux3_BandAnalytic`
  - `FreqData.weil_re_ge`: a frequency-side lower bound for any continuous even real test with `K/(1+r²)` decay;
  - `arch_re_ge`, `prime_eq` as separate halves;
  - Lorentzian Parseval `integral_mul_lz`;
  - digamma floor `psiR_ge_lz`.
- `Crux3_BandTest`
  - the band test `bandV = wPair ∘ clamp` (continuous, not smooth);
  - `bandV_freqData` (the decay comes from the closed-form transform);
  - `acR_bandV`, `acR_bandV_zero`, `lorTerm_bandV` closed forms.
- `Crux3_BandNum`
  - rational balls `InB`;
  - log enclosures via `exp(q/8)^8` and `Real.exp_bound`, plus √ enclosures;
  - cos/sin via reduction and `KWin.cos_sub_tayl_le`;
  - `entryOK` / `entry_sound`.
- `Crux3_BandTable`
  - the 57-entry table;
  - `tab_ok` by `decide +kernel`;
  - negative control `tab_tamper`: the tampered entry is rejected;
  - `lam_tab`.
- `Crux3_BandCert`
  - the instance and `log π ≤ 1.1448`;
  - the rational sums (`decide +kernel`);
  - `quad_nonneg`;
  - `band_floor`, `band_comb_le`, `band_arch_ge`.

Cost: building everything takes about 50 s. Peak memory is about 6 GB, which is the Mathlib import;
the kernel checks themselves take seconds. This fits the 16 GB CI runner.

FOOTGUNS HIT:
- `decide` cannot evaluate `IsPrimePow 49`, because `minFac` is well-founded. It does work for some
  non-prime-powers, such as 36, but not 15. Use `vonMangoldt_apply_pow` and `_prime` for prime powers,
  and a coprime split for the rest.
- `linarith` treats `a*b` and `b*a` as different atoms. The same goes for sums that are elaborated in
  different places. Name the sum with a `def` (for example `lorTerm`) so all occurrences match syntactically.
- `integral_comp_abs` needs its `f` passed explicitly (higher-order pattern).
- `∫ ... : ℝ)` swallows a type ascription. Parenthesise integrals inside casts.
- `omit h in` must come before the docstring.
- `Set.mem_sdiff` is ambiguous with `Finset`.
- A big theorem context makes `nlinarith` and `norm_num` time out. Split the proof into small lemmas with named constants.

## D side: kernel-checked (`Crux3_BandDHData`, `Crux3_BandDH`)

```lean
theorem dh_band_negative (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 56 → aD n * Real.log n = ∑ d ∈ n.divisors, w d * aD (n / d)) :
    (weilFormD w (WeilForm.autocorr (fun u => ((bandTest (-3) 2 u : ℝ) : ℂ)))).re
      ≤ -(1 / 2 : ℝ) * ∫ x, ‖((bandTest (-3) 2 x : ℝ) : ℂ)‖ ^ 2
```

- `weilFormD w = archSideD - primeSideD w` is defined off-registry.
  - `archSideD g = g(0) log(5/π) + (1/2π)∫ h_g Re ψ(3/4 + ir/2)`, with no pole.
  - `primeSideD w g = Σ w(n)/√n (g(log n) + g(-log n))`.
- `hw` is `-D' = D·(-D'/D)` read coefficientwise, so it holds for D's true weights. It forces
  `w 1 = 0` (`w_one_of_conv`) and `w = cD` on `[1, 56]` (`eq_cD_of_conv`).
- `cD n` is in closed form: a polynomial in κ of degree at most 5, times prime logs (`dtab`).
  `cD_conv` proves it with one generated lemma per n.
- Arch upper bound `archD_band_le`:
  - digamma majorant `psiD_le` (series plus telescoped tails `(3/4)/N + (r/2)²/(2N²)`);
  - Lorentzian Parseval at `b = j + 3/4`;
  - the r² moment from `|h_v| <= K'/r²` beyond `2k2` (`Fsq_mul_sq_le`).
  - Instance: `N = 300`, `R = 175`.
- Numbers at c*, in units of `‖v‖²`:
  - arch is at most 4.3188 (stated 4.33; true value 4.2085);
  - prime is at least 4.8630 (stated 4.86);
  - the form is at most -0.5443 (stated -1/2; true value -0.6546).
- The prime-side checker is zeta's, with the weight ball `2·cdBall(dtab n)·(1/√n)`.
  - κ ball: `kap_InB`, from √ brackets.
  - Prime-log balls: `lp_InB`.
  - Table: `dtab_ok` by `decide +kernel`; negative control `dtab_tamper`.
- Cost: `Crux3_BandDH` takes about 20 s at 7.1 GB peak; `Crux3_BandDHData` takes about 40 s at 6.2 GB peak.
- Generators live in the research dir: `dh_symbolic.py`, `gen_dh.py`, `gen_dtabE.py` (their outputs appear
  verbatim in the modules) and `dfinal.py` (thresholds).
- NOT formalized: the explicit formula `weilFormD = Σ_ρ h(γ_ρ)` over D's zeros. It is cross-checked
  numerically by the zero side: -0.65464 against -0.65462.

FOOTGUNS (D side):
- The scratch development could not import a non-module file. Build the data module as a real
  `lean_lib` first, then import it.
- `InB.bAdd` with an explicit `(q, 0)` ball needs the pair spelled as `((q, 0) : ℚ × ℚ).1`/`.2` in the `have`;
  `InB (q : ℝ) q 0` does not unify with `?a.1 ?a.2`.
- `simp only [dOutB, he']` closes the Bool `if` without `if_false` (unused-simp-arg lint).
- The generated per-n proofs use `try` steps, which trip the unused/unreachable-tactic linters. Those linters
  are silenced per file.
