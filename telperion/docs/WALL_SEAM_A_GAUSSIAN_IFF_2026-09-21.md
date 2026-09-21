# Wall seam A: RH iff Gaussian positivity, in two real parameters (2026-09-21)

Status: both deliverables are kernel-checked on the rvm_bridge island (Lean v4.33.0-rc2,
Mathlib via the Zeta23 pin), every delivered theorem with axioms exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, and NO named sub-obligation left
(the `PrimeSideGaussianLimit` / `ArchSideGaussianLimit` placeholders the brief allowed were not
needed: both limits closed as lemmas).

Nothing here proves RH. An equivalence between RH and a two-parameter family of inequalities is
a change of coordinates on the Wall, not a crossing. conjecture1_proved = False.

## Files

- `telperion/examples/rvm_bridge/lean/E6Bridge10.lean` (namespace `RvMBridge10`, `import E6Bridge9`,
  577 lines).
- `telperion/examples/rvm_bridge/lean/Probes/E6Bridge10_probe.lean` (axiom audit of 20 declarations,
  shape probe, three non-vacuity probes).
- This memo.

Not touched: `lakefile.toml`, `AxiomGuardRvMBridge.lean`, every existing `E6Bridge*.lean`. The
integrator wires `E6Bridge10` as a `lean_lib` in `defaultTargets` and adds the guard lines listed
below. For the probe run the olean was emitted by hand
(`lake env lean -o .lake/build/lib/lean/E6Bridge10.olean -i .lake/build/lib/lean/E6Bridge10.ilean E6Bridge10.lean`);
a `lake build` after wiring reproduces it.

## Deliverable 1: the two-parameter Wall

```lean
/-- Gaussian positivity: the Wall in two real parameters. -/
def GaussianPositivity : Prop :=
  ∀ (c lam : ℝ), 0 < lam → 0 ≤ (RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)).re

theorem rh_iff_gaussian_positivity : RiemannHypothesis ↔ GaussianPositivity

theorem gaussian_positivity_iff_weil_positivity :
    GaussianPositivity ↔ (∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re)
```

In words. Write gamma_rho = (rho - 1/2)/i for the ordinate of a zero (real exactly when rho is on
the line). Then

    RH  <=>  for every centre c in R and every width lam > 0,
             Re  Sum_rho  m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2)  >=  0.

Forward (`rh_implies_gaussian_positivity`): under RH every nontrivial zero has real part 1/2
(`Zeta23.RH_implies_on_line`), so gamma_rho = Im rho is real (`gammaOf_eq_im_of_rh`), the summand is
m(rho) times the nonnegative real (x - c)^2 e^{-2 lam (x - c)^2} (`gaussTest_ofReal`,
`gauss_term_re_nonneg`; summands at non-zeros vanish by `RvMBridge4.zeroMult_eq_zero_of_not_nontrivial`),
the family is summable (`RvMBridge6.summable_gauss_zeroSide`), and `Complex.hasSum_re` +
`HasSum.nonneg` give the sign of the real part of the tsum.

Converse (`gaussian_positivity_implies_rh`): contrapositive of the discharged O2. If some nontrivial
zero were off the line, `RvMBridge7.gaussian_dominance` produces c, lam > 0 with
Re zeroSide (gaussTest c lam) < 0, contradicting GaussianPositivity; `RvMBridge6.rh_of_all_on_line`
turns "all nontrivial zeros on the line" into Mathlib's `RiemannHypothesis`.

The composition with E6Bridge9's dictionary theorem (`zeta_comb_membership_iff_rh`) gives the
third statement: Gaussian positivity is Weil positivity on Hermitian autocorrelations.

Why this is a seam. The MIRRORMERE goal statement quantifies over the infinite-dimensional class
C_c^infinity(R) of test functions. GaussianPositivity quantifies over two real numbers. The Wall
is now a picture: the (c, lam) half-plane, with RH the statement that a single explicit function
S(c, lam) := Re zeroSide (gaussTest c lam) is nonnegative everywhere on it. Every off-line zero
would carve out a region where S < 0 (that is the content of O2); RH says no such region exists.

## Deliverable 2: the Gaussian explicit formula (the prime-side form of the Wall)

```lean
theorem zeroSide_gaussTest_eq (c lam : ℝ) (hlam : 0 < lam) :
    RvMBridge6.zeroSide (RvMBridge6.gaussTest c lam)
      = WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))
        - WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))

theorem gaussian_positivity_iff_prime_le_arch :
    GaussianPositivity ↔ ∀ (c lam : ℝ), 0 < lam →
      (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re

theorem rh_iff_gaussian_prime_le_arch :
    RiemannHypothesis ↔ ∀ (c lam : ℝ), 0 < lam →
      (WeilExplicit.primeSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
        ≤ (WeilExplicit.archSide (WeilExplicit.autocorr (RvMBridge8.gaussPhi c lam))).re
```

Here phi = gaussPhi c lam is E6Bridge8's non-compactly-supported test
K u exp(-u^2/(4 lam)) exp(-i c u) (whose transform is (z - c) e^{-lam (z - c)^2}), and
autocorr phi (u) = ∫ phi(v) conj phi(v - u) dv is its Hermitian autocorrelation (the integral
definition of E6Bridge5, which converges for Gaussian decay). In words:

    RH  <=>  for every centre c and width lam > 0,  arch_{c,lam} >= prime_{c,lam},

where prime_{c,lam} = Sum_n Lambda(n)/sqrt n (f(log n) + f(-log n)) and arch_{c,lam} is the
archimedean side (the two pole terms, the -f(0) log pi term and the digamma integral) of
f = autocorr phi_{c,lam}. No zeros appear on either side of this inequality.

Route (all closed, no obligation left). E8 (`RvMBridge4.limit_explicit_formula`) holds for each
truncation g_n := gaussTests c lam n (an `IsWeilTest`), read as
weilForm (autocorr g_n) = zeroSide (hermitianTransform g_n) (`RvMBridge6.weilForm_autocorr_eq_zeroSide`).
Pass n -> infinity on both sides and use uniqueness of limits (`tendsto_nhds_unique`):

1. Zero side (section B): `zeroSide_gaussTests_tendsto`, the COMPLEX form of E6Bridge6's Tannery
   transfer (E6Bridge6 exports only the real part). Inputs: the n-uniform strip bound
   `exists_hermitian_gaussTests_bound` (re-assembled from `RvMBridge8.exists_paperFT_gaussTests_bound`)
   and the pointwise limit `hermitianTransform_gaussTests_tendsto`, against the local zero count
   `RvMBridge6.summable_mult_div_one_add_normSq`.
2. Autocorrelations (section C). `norm_gaussTests_le`: |g_n| <= |phi| (chi_n <= 1). The v-majorant
   `vMaj lam u v = |K|^2 ((v - u/2)^2 + u^2/4) e^{-2b (v - u/2)^2} e^{-(b/2) u^2}` dominates
   |phi(v)| |phi(v - u)| (`norm_phi_mul_phi_le`: |v||v - u| <= (v^2 + (v - u)^2)/2 and
   v^2 + (v - u)^2 = 2 (v - u/2)^2 + u^2/2), is integrable in v (`integrable_vMaj`) and integrates
   to the u-Gaussian `autocorrMaj lam u = |K|^2 (I2 + (I0/4) u^2) e^{-(b/2) u^2}` (`integral_vMaj`,
   shift invariance `integral_sub_right_eq_self`; I0, I2 the two moments of e^{-2b w^2}). Hence
   `norm_autocorr_gaussTests_le`: |autocorr g_n (u)| <= autocorrMaj lam u uniformly in n, and
   `autocorr_gaussTests_tendsto`: autocorr g_n (u) -> autocorr phi (u) (dominated convergence; the
   integrand is eventually constant in n once n + 1 >= max(|v|, |v - u|)).
3. Prime side (section D): `primeSide_gaussTests_tendsto` by `tendsto_tsum_of_dominated_convergence`
   with majorant `primeBound lam k = Lambda(k)/sqrt k * 2 autocorrMaj lam (log k)`
   (`norm_primeTerm_le`), summable (`summable_primeBound`): for k >= exp(12/b) the Gaussian factor
   e^{-(b/2)(log k)^2} is <= k^{-6}, Lambda(k)/sqrt k <= log k <= k and (log k)^2 <= k^2, so the term is
   <= D k^{-3}.
4. Archimedean side (section E). `weilKernel_gaussTests_tendsto`: for |Re s - 1/2| <= 1/2,
   weilKernel (autocorr g_n) s -> weilKernel (autocorr phi) s by dominated convergence in u with
   majorant `kernelMaj lam u = autocorrMaj lam u e^{|u|/2}` (`integrable_kernelMaj`). This covers the
   two pole terms (s = 0, 1) and the line s = 1/2 + i r. The digamma integral:
   `archIntegral_gaussTests_tendsto` by dominated convergence in r with majorant `archBound C r`
   (C/(1 + r^2) times the two Gamma_R log-derivative factors plus log pi), integrable by Zeta23's
   majorant lemma `integrable_mul_logDeriv_Gammaℝ_of_decay` applied to the function C/(1 + r^2)
   itself (`integrable_archBound`); the pointwise bound `norm_archIntegrand_le` uses the n-uniform
   line bound `exists_paperFT_autocorr_gaussTests_bound` (from the strip bound of step 1 through
   `RvMBridge6.weilKernel_autocorr` and gammaOf(1/2 + i r) = r). The -f(0) log pi term is step 2 at
   u = 0. `archSide_gaussTests_tendsto` assembles the four pieces.
5. Assembly (section F): `zeroSide_gaussTest_eq`, then the two corollaries by `Complex.sub_re` and
   `sub_nonneg`.

Design choice worth recording: the convolution theorem for the NON-compactly-supported phi
(paperFT (autocorr phi) = |paperFT phi|^2, a Fubini statement) was never needed. The archimedean side
of autocorr phi is reached purely as a limit of the archimedean sides of the truncations, so the only
facts about phi used are its Gaussian decay and continuity.

## Guard lines (for the integrator)

```lean
-- E6Bridge10 (seam A, 2026-09-21): the Wall in two real parameters.
#print axioms RvMBridge10.rh_iff_gaussian_positivity
#print axioms RvMBridge10.rh_implies_gaussian_positivity
#print axioms RvMBridge10.gaussian_positivity_implies_rh
#print axioms RvMBridge10.gaussian_positivity_iff_weil_positivity
#print axioms RvMBridge10.zeroSide_gaussTest_eq
#print axioms RvMBridge10.gaussian_positivity_iff_prime_le_arch
#print axioms RvMBridge10.rh_iff_gaussian_prime_le_arch
#print axioms RvMBridge10.zeroSide_gaussTests_tendsto
#print axioms RvMBridge10.norm_autocorr_gaussTests_le
#print axioms RvMBridge10.autocorr_gaussTests_tendsto
#print axioms RvMBridge10.summable_primeBound
#print axioms RvMBridge10.primeSide_gaussTests_tendsto
#print axioms RvMBridge10.weilKernel_gaussTests_tendsto
#print axioms RvMBridge10.archIntegral_gaussTests_tendsto
#print axioms RvMBridge10.archSide_gaussTests_tendsto
```

## Probe output (verbatim, `lake env lean Probes/E6Bridge10_probe.lean`)

```
'RvMBridge10.rh_iff_gaussian_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.rh_implies_gaussian_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.gaussian_positivity_implies_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.gaussian_positivity_iff_weil_positivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.zeroSide_gaussTest_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.gaussian_positivity_iff_prime_le_arch' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.rh_iff_gaussian_prime_le_arch' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.zeroSide_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.norm_autocorr_gaussTests_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.autocorr_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.summable_primeBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.primeSide_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.weilKernel_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.archIntegral_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.archSide_gaussTests_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.integral_vMaj' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge10.integrable_archBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_offline_zero_refutes' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_not_rh_iff_prime_gt_arch' depends on axioms: [propext, Classical.choice, Quot.sound]
'probe_gaussPhi_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Probes, beyond the axiom audit: the `GaussianPositivity` body is literally `∀ c lam, 0 < lam → P c lam`
for a `P : ℝ → ℝ → Prop` (shape); an off-line nontrivial zero would refute GaussianPositivity
(`probe_offline_zero_refutes`, so the definition is not a tautology); the falsifiability face
`¬ RH ↔ ∃ c lam, 0 < lam ∧ Re arch < Re prime` (`probe_not_rh_iff_prime_gt_arch`); phi is not the
zero function (`probe_gaussPhi_ne_zero`).

## What it is NOT

- Not a proof of RH, and not a proof of Gaussian positivity or of arch >= prime for any (c, lam).
  Every delivered theorem is an `↔` or an `=`; neither side of any `↔` is asserted.
- Not a new analytic input: the forward half is RH-on-the-line plus summability, the converse is
  O2 (E6Bridge7) read backwards, and the explicit formula for phi is E8 plus three dominated
  convergences. What is new is the coordinate system: the Wall is a sign question about one
  explicit function on the (c, lam) half-plane, with a prime-side expression that never mentions
  zeros.
- The inequality arch_{c,lam} >= prime_{c,lam} is stated for real parts; both sides are in fact real
  (zeroSide (gaussTest c lam) is real by `RvMBridge6.gauss_zeroSide_real`), so nothing is lost, but
  the imaginary-part identity was not separately recorded.
