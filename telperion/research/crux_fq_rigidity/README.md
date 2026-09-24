# Zero-side quasicrystal rigidity for the Guinand-Weil pair (crux-fq, rigidity seat, builder)

`conjecture1_proved = False`. Nothing in this directory proves RH, reduces it, or moves a wall clause.
Status tags follow the program's ethos: THEOREM-kernel-checked, THEOREM-paper-proof,
CONJECTURE-with-evidence, HEURISTIC, and COMPUTED (floating point or mpmath, not interval) versus
Arb-certified (rigorous ball arithmetic, outside the kernel).

## The question, and the short answer

The user's lead for this round was the Fourier-quasicrystal (FQ) literature, read against round 1's
Theorem A. Theorem A pins down the integers as the only positive, self-dual measure with an atom at 0
and a gap. The kernel seat of this run proved its crystalline half in Lean (`CruxFQ_PoissonRigidity.lean`
on the li_positivity island) and showed that it is blind to where zeros are.

The rigidity seat asked the mirror question. The Guinand-Weil explicit formula pairs a "zero side" (a
measure on the ordinates of the zeros) with a "prime side" (a measure on the logarithms of prime
powers). Is there a rigidity on the zero side that an off-line zero would violate and that is not RH
in disguise?

The seat's answer was no. This builder has now put the core of that answer into the kernel, in the
corpus's own vocabulary (the corpus explicit formula `RvMBridge4.limit_explicit_formula` and the
corpus Weil criterion `RvMBridge9`):

1. **The zero-side positivity clause is RH, in both directions.** Zeta has a positive real measure
   that reproduces its explicit formula on every test (and integrates every test transform) if and
   only if RH holds (`zeta_positive_partner_iff_rh`). The forward direction goes through Weil
   positivity. The backward direction builds zeta's zero measure `Z_ζ = Σ_ρ m_ρ δ_{Im ρ}` from the
   corpus zero configuration and reads the corpus explicit formula on the critical line. The same
   holds for positive partners at every finite resolution taken together (`all_windows_iff_rh`),
   while any single resolution gives only window Weil positivity. So "the zero side is a positive
   quasicrystal-type measure" is not a route to RH. It is RH, written in another coordinate system.
   Verdict (b): CIRCULARITY.
2. **The only unconditional zero-side rigidity is blind to where the zeros are.** Lemma M, the
   antichain lemma, says that positive Guinand partners with a common archimedean term cannot be
   nested. If `μ₁ ≤ μ₂` are both positive partners with positive prime sides, then `μ₁ = μ₂` and
   the prime sides agree (`guinand_antichain_le`). No functional equation is used, and the
   archimedean functional is arbitrary. For zeta this means that no real zeros can be added to, or
   removed from, a positive partner (`zeta_partner_no_added_zeros`, `zeta_partner_no_deleted_zeros`).
   Under RH, `Z_ζ` is therefore both maximal and minimal (`zetaZeroMeasure_extremal_of_rh`). Lemma
   M says nothing about whether a positive partner exists, and existence is exactly RH (point 1).
   Verdict (a): true, and not a route.
3. **Positivity of the prime side and the absence of an atom at `u = 0` are both load-bearing.**
   Lebesgue measure and the zero measure form a nested pair of positive partners as soon as the
   smaller prime side carries an atom at 0 (a conductor-type term), or the larger one is signed
   (`antichain_negative_controls`).

Two further pieces of the seat's work are now kernel theorems.

- **Quantitative Theorem A** (the Fejer form of the seat's Lemma 8.1). Consider a positive measure
  with no mass in `(-1,1) \ {0}`. Its self-duality defect on the single Fejer test `tri` equals its
  `sinc²`-weighted mass off 0 (`fejer_defect_identity`, `poisson_defect_eq`), and it bounds the
  mass at distance at least `ε` from the integers inside `|x| ≤ R` (`offInteger_mass_le`):
  `(4ε²/π²R²) · ν{|x| ≤ R, dist(x, ℤ) ≥ ε} ≤ defect`. Theorem A is the case where the defect is 0.
  This is a stability version of Theorem A, and like Theorem A it is blind to zeros.
- **The Lee-Yang / Euler divide** (the kernel-checkable half of Theorem E):
  - A finite unimodular power sum that tends to 0 is identically 0 (`bohr_mean`,
    `unimodular_powerSum_coeff_eq_zero`). Such a sum exceeds every level below `max|a_i|`
    infinitely often (`unimodular_powerSum_frequently_large`).
  - So zeta's local Bragg sequence `-p^{-m/2}` is never a unimodular power sum, even at one prime
    and with any complex (for example signed integer) weights (`zeta_bragg_not_unimodular`). A
    Lee-Yang local factor has non-decaying power sums (`leeYang_powerSum_frequently_large`).
  - The Kurasov-Sarnak reality mechanism in two frequencies (`ks_real_zeros`) is proved, together
    with the seat's explicit example `PLY = 1 + z₁/2 + z₂/2 + z₁z₂` on `(log 2, log 3)`. `PLY` is
    Lee-Yang, all zeros of `PLY(2^{ix}, 3^{ix})` are real, and `PLY` is not a product of
    one-variable factors (its mixed coefficient is `3/4`).
  - The local dictionary (`local_dictionary`): all local zeros of `∏(1 - a_j p^{-s})` lie on
    `Re s = 1/2` if and only if every `|a_j| = √p`. The golden fake (`c = √5`) and `W1(29,11)`
    (`c = 11/√29`) fall on the non-Lee-Yang side (`quadratic_leeYang_fails`,
    `zoo_local_factors_not_leeYang`).

## The kernel file

`telperion/examples/rvm_bridge/lean/Crux/CruxFQ_rigidity.lean`

- 1929 lines, namespace `CruxFQRigidity`.
- Imports `Mathlib` and the corpus module `E6Bridge9`.
- Toolchain: Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 fbdc36bb.
- sha256 `9c7df870c8aa4663fd6941f760f8e149160bd2c15faa0ab465ebd8c177959754`.
- Contains no `sorry`, `admit`, `native_decide`, new `axiom`, `opaque`, or `set_option`.
- All 38 `#print axioms` lines report exactly `[propext, Classical.choice, Quot.sound]`. The
  transcript is in `lean_axioms_transcript.txt`.
- The file is untracked, like the other Crux files: it is not in CI and not in AxiomGuard.

Check command, with exit 0 and no warnings:

```
cd telperion/examples/rvm_bridge/lean
/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/leanlock.sh lake env lean Crux/CruxFQ_rigidity.lean
```

**Conventions.**

- Tests are the corpus class `WeilExplicit.IsWeilTest`: smooth, compactly supported `g : ℝ → ℂ`.
- The zero-side transform is `gwHat g r = ∫ g(u) e^{iru} du`. This is the corpus
  `weilKernel g (1/2 + ir)` and `paperFT g r`.
- `IsGuinandPartner E Pr μ` means that the positive measure `μ` satisfies `∫ ĝ dμ = E g - Pr g`
  for every test whose transform is `μ`-integrable.
- `IsZetaPartner` fixes `E = archSide` and `Pr = primeSide`, taken from the corpus.
- "Test-tempered" (`IsTestTempered`) means that every test transform is integrable. It is implied
  by `∫ (1+r²)⁻¹ dμ < ∞`.
- Temperedness is assumed where it is used. The seat's Lemma G, which derives it from positivity,
  is not formalized.

**How Lemma M is proved.** The test family is `ψ_d ⋆ ψ_d`, where `ψ_d` is Mathlib's normalized
smooth bump of radius `d`.

- Its transform is `ψ̂_d(r/2π)²`. This lies in `[0,1]` and tends to 1 as `d → 0`, using the bound
  `1 - ψ̂_d(ξ) ≤ 2π²d²ξ²`.
- On the prime side the test is at most `2|u|⁻¹` on `0 < |u| < 2d` and vanishes elsewhere. So its
  integral against a positive prime side that has no atom at 0 and satisfies
  `∫_{0<|u|<1} |u|⁻¹ dP < ∞` tends to 0 by dominated convergence.
- For zeta, the prime gap `(-log 2, log 2)` makes that integral exactly 0 once `d ≤ log 2 / 2`.
- Subtracting the two Guinand identities and applying Fatou's lemma (`measure_eq_zero_of_kd`)
  kills the difference.
- In the order form, the difference measure is built on compact windows with
  `Measure.sub_add_cancel_of_le`, and the two measures are then identified with `ext_of_Icc'`.
- Equality of the prime sides follows from agreement on all smooth tests, via bumps shrinking to
  closed intervals (`measure_eq_of_integral_test_eq`).

## What is not established here

- **Theorem D** (a positive prime side that has any zero-multiset partner under zeta's archimedean
  term must be `P_ζ`) and **Corollary D1** (the integer-valued classification). THEOREM-paper-proof
  only. They rest on round 1's Theorem A, whose Step 2 (the functional equation implies the Poisson
  identity: Hamburger 1922, as recorded by Kahane-Mandelbrojt 1958) is not formalized. They also
  rest on canonical-product growth bounds.
- **Corollary D2** (the partner of the continuous Beurling system `s/(s-1)` is negative on
  `[1, 5.8]`). Arb-certified outside the kernel (`n4`). The Lean file does not contain it.
- **Proposition 3.6** (a tempered signed partner exists if and only if RH): paper only.
- **Theorem E(i)** (Euler support forces a product and lattice zero sets). This needs the
  Kurasov-Sarnak Fourier formula for the zero measure, which is not formalized. The kernel has the
  consequences that do not need it.
- **Lemma G** (automatic temperedness): not formalized.
- **The Krein direction of Proposition K** (window positivity implies a window partner): not
  formalized.
- **`∫ (1+r²)⁻¹ dZ_ζ < ∞` under RH.** Only test-temperedness of `Z_ζ` is proved; that is all the
  equivalence needs.
- **The literature claims** (Miller 2002's zero-side LP, Bondarenko-Radchenko-Seip,
  Baake-Spindeler-Strungaru, and novelty): these come from the literature seat's reading, not from
  proofs. The novelty of Lemma M and of the Fejer stability bound is HEURISTIC ("not found"). Both
  are elementary, and either may be folklore.

## Negative controls, result by result

- **Z1 equivalence and window equivalence.** These are about zeta itself, through the corpus
  explicit formula. They are certificates of circularity, so there is nothing for a fake to slip
  through. For Davenport-Heilbronn, the analogous "positive real partner" is false, because DH has
  off-line zeros (0.8085 + 85.699i, Arb-certified in round 1). Its window partners at small
  resolution exist, but that is COMPUTED only (spectral lens, onset about `x = 30.5`). This is
  exactly why a single resolution certifies nothing.
- **Lemma M.** It is functional-equation-free and applies verbatim to any `E`. It separates nothing
  on its own, because it is silent on existence. Its two hypotheses are shown to be necessary in
  the kernel (`antichain_negative_controls`).
- **Theorem E pieces.** The dictionary detects the zoo's Euler-product fakes, because their
  off-line zeros are local zeros of non-Lee-Yang factors. The golden fake gives `Re s = 0.798994`
  and W1 gives `0.561221` (`n2`). A surgery that keeps `|a_j| = √p` (a Ramanujan factor, `c ≤ 2`)
  puts its local zeros on the line, and the dictionary cannot see it. This is consistent with the
  kernel seat's fooling family at `c ≤ 2`. Davenport-Heilbronn and Epstein have no Euler product,
  so the Euler-support results do not apply to them. DH carries composite Bragg amplitude
  (`b(6) = 1.936`), which is the non-product Lee-Yang signature of `PLY`, not zeta's.
- **Quantitative Theorem A.** Like Theorem A, it is a statement about measures, and it is blind to
  zeros. The kernel seat's fooling family `ν_{p,c}` violates the gap, so the defect identity does
  not apply to it, as expected.

## Computations (single process, no pools)

| script | what it does | status | result |
|---|---|---|---|
| `n1_gw_normalization.py` | GW normalization with 2000 zeta zeros, Gaussian tests | COMPUTED | residual `1.1e-22` at `σ = 0.3`, where the zero side is `1.87e-4` (relative `6e-19`). At `σ = 0.5` and `0.8` the zero side is `3.6e-11` and `6.9e-28`, so those residuals only test about 3 to 18 digits. The kernel does not depend on this: the corpus explicit formula is kernel-checked. |
| `n2_ks_euler_dictionary.py` | local roots of the zoo; the `PLY` example | COMPUTED | golden fake: `Re s = 0.798994`; W1: `0.561221`; F(5,5): `0.798994`. `c₁₁ = 0.75`. 17 zeros in `[0,60]×[-3,3]`, and all 17 are real. |
| `n3_continuous_partner.py` | the `s/(s-1)` partner `μ_cont` | COMPUTED | GW identity to 15 digits; `μ_cont < 0` exactly on `0.724435 < |r| < 5.947140` |
| `n4_arb_mu_cont.py` | Arb certificate for Corollary D2 | Arb-certified | `μ_cont < 0` on all of `[1, 5.8]` (9600 cells, 120 bits); `μ_cont(3) = -0.0840382413870272863356… ± 8e-37` |
| `n5_kernel_crosscheck.py` (new) | numerical cross-checks of the kernel constants | COMPUTED | see below |

What `n5_kernel_crosscheck.py` checks:

- The bump bounds `sup ψ_d ≤ 1/d` and `1 - ψ̂_d(ξ) ≤ 2π²d²ξ²` hold for a bump built in the same
  way as the kernel's.
- The Fejer lower bound `fej ≥ 4ε²/(π²R²)` holds off the integers.
- The quantitative Theorem A inequality holds on perturbed combs.
- `PLY(2^{ix}, 3^{ix}) e^{-ix log 6/2} = 2cos(x log 6/2) + cos(x log(2/3)/2)`, with error
  `3e-29`. The real zero count on `[0,60]` is 17.
- The local trichotomy of Bragg sequences:
  - Lee-Yang (unimodular roots): bounded and not decaying, with Bohr mean of `|s_m|²` equal to
    `2.00002`.
  - Zeta (root outside the disc): decays like `p^{-m/2}`.
  - Golden fake (a root inside the disc): grows like `φ^m`.

Reproduce each with `python3 <script>`. The outputs are in the matching `.out` files.
`n4` needs python-flint.

## Files

- `README.md`: this file.
- `lean_axioms_transcript.txt`: the 38 `#print axioms` lines.
- `n1`–`n5` `.py` scripts with their `.out` outputs. `n1`–`n4` are the seat's scripts, re-run
  here. `n5` is new.
- The seat's derivations are in `/private/tmp/claude-0/crux-fq/rigidity/NOTES.md`. The builder
  addendum is section 10 of that file.
