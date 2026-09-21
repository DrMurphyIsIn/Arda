# Weil converse attack: positivity implies RH (2026-09-20)

Design memo and honest ledger for `telperion/examples/rvm_bridge/lean/E6Bridge6.lean`
(namespace `RvMBridge6`, island toolchain Lean v4.33.0-rc2, Mathlib pinned through the Zeta23
package). Probe file: `Probes/E6Bridge6_probe.lean`. conjecture1_proved = False throughout; the
theorem attacked here says Weil positivity implies RH and proves neither.

## 1. Outcome in one paragraph

The converse half of Weil's criterion is proved MODULO two named analytic obligations. The
delivered theorem is

```
theorem weil_positivity_implies_rh_of (hO1 : GaussianTransfer) (hO2 : GaussianDominance)
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis
```

together with `weil_positivity_implies_rh_of'`, the same with O1 replaced by the zero-free
`GaussianApprox` (section H of the file derives O1 from it by Tannery's theorem). Every theorem
in the file prints `[propext, Classical.choice, Quot.sound]`; no sorry anywhere; the obligations
are `def : Prop` consumed only as hypotheses, never as instances or axioms. What is kernel-checked
beyond the statement: the explicit formula for Hermitian autocorrelations with the zero side
isolated and shown real, the reflection symmetry on all of C, the pair term of an off-line zero
isolated from the rest of the sum, the strip lemma connecting Mathlib's RiemannHypothesis to the
strip zeros, the summability of the Gaussian-weighted zero sum from the local zero count, and the
dominated-convergence transfer from the strip to the zero side.

## 2. The argument as formalised

Write h = paperFT g and gamma_rho = gammaOf rho = (rho - 1/2)/i, so gamma is real exactly on the
line and gamma_{1 - conj rho} = conj gamma_rho (`gammaOf_reflect`). For f = autocorr g = g * g~
the E8 node (`RvMBridge4.limit_explicit_formula`) plus `Zeta23.EF.paperFT_weilTest` give

    weilForm f = Sum_rho m(rho) h(gamma_rho) conj(h(conj gamma_rho)) = zeroSide (hermitianTransform g)

(`weilForm_autocorr_eq_zeroSide`), a real number (`weilForm_autocorr_real`, from the involution
rho -> 1 - conj rho which preserves the registry multiplicity on all of C, `zeroMult_reflect`).
On-line zeros contribute m |h(gamma)|^2 >= 0. An off-line pair {rho_0, 1 - conj rho_0}
contributes 2 m Re H(gamma_0) (`zeroSide_pair_split`), and the sign of that is free.

The contradiction uses the Gaussian-derivative Hermitian transform

    G_{c,lam}(z) = (z - c)^2 exp(-2 lam (z - c)^2)   (= h h* for h(z) = (z - c) e^{-lam (z-c)^2}).

For a zero with w = gamma_rho - c = x + i y (x = Im rho - c, y = 1/2 - Re rho):

    |m G(w)| = m |w|^2 exp(2 lam (y^2 - x^2)),   arg G(w) = 2 arg w - 4 lam x y.

On the axis x = 0 the value is exactly -y^2 exp(2 lam y^2) < 0 (`gaussTest_axis`,
`gauss_zeroSide_pair_split`). The whole sum converges absolutely for every c and lam > 0
(`summable_gauss_zeroSide`, from the bound ‖G(z)‖ (1 + |z|^2) <= e^{lam/2}(2c^2 + 13/4)/min(1,lam)^2
on the strip, `norm_gaussTest_mul_le`, against Zeta23's Sum m/(1 + |gamma|^2) < infinity).

### O2 (GaussianDominance): the analytic heart

```
def GaussianDominance : Prop :=
  ∀ ρ₀ : ℂ, IsNontrivialZero ρ₀ → ρ₀.re ≠ 1 / 2 →
    ∃ (c lam : ℝ), 0 < lam ∧ (zeroSide (gaussTest c lam)).re < 0
```

Why it is true (paper proof, not formalised). Let rho_0 be off-line, delta_0 = 1/2 - Re rho_0.
Choose the centre c with |c - Im rho_0| < |delta_0|, so Phi_c(rho_0) := y^2 - x^2 > 0 at rho_0.
Only finitely many zeros have Phi_c >= 0 (they need |Im rho - c| < 1/2; Zeta23 `finite_window`), so
M := max Phi_c over all zeros is attained, M > 0, at an off-line zero rho_1. Choose c generic: two
zeros with different ordinates tie in Phi_c for exactly one c, and only zeros within ordinate
distance 1 of Im rho_0 can be involved, so the bad set of c is finite; for good c the maximiser is
unique up to the pair rho_1 <-> 1 - conj rho_1 (a zero with the same ordinate and the same y^2 is
one of the two). Its pair term is 2 m |w_1|^2 e^{2 lam M} cos(2 arg w_1 - 4 lam x_1 y_1). If
x_1 = 0 the cosine is -1 for every lam. If x_1 != 0 then x_1 y_1 != 0 and lam_k :=
(2 arg w_1 + pi + 2 pi k)/(4 x_1 y_1) -> +infinity (k -> +-infinity by sign) makes it -1. All other
zeros: the finitely many with Phi_c >= 0 other than the pair have Phi_c <= M - eta for some
eta > 0 and contribute at most C e^{2 lam (M - eta)}; the rest have Phi_c < 0 and their absolute
sum is at most its value at lam = 1, a constant. Hence Re S(c, lam_k) <= -2 m |w_1|^2 e^{2 lam_k M}
+ C e^{2 lam_k (M - eta)} + C' < 0 for k large. This is Weil's / Bombieri's localisation argument
with the centre moved off the ordinate of rho_0 so that a nearby zero with larger |delta| cannot
defeat the test; the phase rotation in lam is what makes a generic maximiser usable.

Why it is nontrivial and not circular: it is implied by RH vacuously, but its proof above never
uses RH, and it is a concrete statement about one explicit sum over the zeros. It is strictly
weaker than RH. What would discharge it in Lean: (i) the finite maximiser (finite_window + Finset
argmax); (ii) the generic-centre lemma (finite bad set, pick c in an interval avoiding it); (iii)
the tail bound splitting the tsum into the pair, the finite set with Phi_c >= 0, and the rest
(`zeroSide_pair_split` and `summable_gauss_zeroSide` are the tools; the rest needs
`Summable.sum_add_tsum_compl` twice and monotonicity of e^{2 lam Phi} in lam on Phi < 0); (iv) the
phase choice lam_k and the closing inequality. Rough size: 400 to 700 lines.

### O1 (GaussianTransfer) and O1' (GaussianApprox)

```
def GaussianTransfer : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    Tendsto (fun n => (zeroSide (hermitianTransform (g n))).re) atTop
      (𝓝 (zeroSide (gaussTest c lam)).re)

def GaussianApprox : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    (∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (g n) z‖ ≤ C / (1 + Complex.normSq z)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => hermitianTransform (g n) z) atTop (𝓝 (gaussTest c lam z)))
```

`gaussianTransfer_of_approx : GaussianApprox → GaussianTransfer` is PROVED (Tannery's
`tendsto_tsum_of_dominated_convergence` with the majorant m(rho) C/(1 + |gamma_rho|^2), summable
by `summable_mult_div_one_add_normSq`). So the live obligation is O1', which mentions no zeros.

Why O1' is true: take phi with paperFT phi (z) = (z - c) e^{-lam (z - c)^2}, i.e. phi(u) =
e^{-icu} times a derivative of a Gaussian (Mathlib `integral_cexp_quadratic` evaluates the
transform at complex z), and g_n = phi chi(./n) with chi a smooth cutoff equal to 1 on [-1, 1]
(`ContDiffBump`). Then g_n is a Weil test; h_{g_n}(z) -> h_phi(z) for every z by dominated
convergence in u (|e^{izu}| = e^{-u Im z} <= e^{|u|/2} against the Gaussian); and two integrations
by parts give |h_{g_n}(z)| <= (‖g_n''‖ weighted by e^{|u|/2}) / |z|^2 with the weighted norm
bounded uniformly in n (chi(./n) has derivatives O(1/n), O(1/n^2)). The product structure
hermitianTransform = h(z) conj h(conj z) turns this into the C/(1 + |z|^2) bound (the |z| <= 1
region is bounded by ‖g_n‖_1 e^{1/2}). Rough size in Lean: 300 to 500 lines; the Gaussian
transform at complex argument and the uniform integration by parts are the two real pieces.
Zeta23's `norm_Hfn_le` gives the bound for one fixed test with an existential constant; the
uniformity in n is what it does not give.

## 3. Lemma ledger (all kernel-checked, axioms [propext, Classical.choice, Quot.sound])

- `hermitianTransform g z = paperFT g z * conj (paperFT g (conj z))` (def)
- `zeroSide H = ∑' ρ : ℂ, zeroMult ρ * H (gammaOf ρ)` (def), `gaussTest c lam` (def)
- `weilKernel_autocorr`: H_{g * g~}(rho) = hermitianTransform g (gamma_rho)
- `hasSum_weilForm_autocorr`, `weilForm_autocorr_eq_zeroSide`, `summable_hermitian_zeroSide`
- `reflect_reflect`, `gammaOf_reflect`, `zeroMult_reflect` (on all of C), `reflectEquiv`
- `zeroSide_conj`: Hermitian-symmetric H has real zero side; `weilForm_autocorr_real`
- `hermitianTransform_conj`, `gaussTest_conj`
- `strip_of_zero`: zeta s = 0, s not trivial, s != 1 implies 0 < Re s < 1 (functional equation)
- `rh_of_all_on_line`: all strip zeros on the line implies Mathlib's RiemannHypothesis
- `weil_positivity_implies_rh_of`, `rh_iff_weil_positivity_of` (with E6Bridge5's forward half)
- `reflect_ne_self`, `zeroSide_pair_split`: the pair {rho_0, 1 - conj rho_0} isolated
- `gaussTest_axis`, `gaussTest_axis_re_neg`: the Gaussian on the off-line axis is negative
- `norm_gaussTest_mul_le`: strip bound with explicit constant
- `summable_mult_div_one_add_normSq`: the local-count majorant over all of C
- `summable_gauss_zeroSide`, `gauss_zeroSide_real`, `gauss_zeroSide_pair_split`
- `gaussianTransfer_of_approx`, `weil_positivity_implies_rh_of'`

## 4. Where the attack stopped

O2 stopped at the maximiser/generic-centre/tail argument: everything needed to state it is in the
file (pair split, summability, the negative axis value), but the finite argmax, the bad-set
avoidance, the split of the remainder into a finite exponentially-subdominant part and a
lam-uniform part, and the phase choice were not started. O1' stopped at the Fourier side: the
Gaussian transform at complex argument and the truncation-uniform integration by parts. Both are
believed true on classical grounds (Weil 1952; Bombieri 2000, Thm 1) and neither uses RH.

## 5. O2 discharge (E6Bridge7, 2026-09-20)

`RvMBridge7.gaussian_dominance : RvMBridge6.GaussianDominance` is kernel-checked with no
sub-obligation (`#print axioms` = [propext, Classical.choice, Quot.sound]; file
`telperion/examples/rvm_bridge/lean/E6Bridge7.lean`, probe `Probes/E6Bridge7_probe.lean`).
Corollary `RvMBridge7.weil_positivity_implies_rh_of_approx (hA : GaussianApprox) (hpos) :
RiemannHypothesis`: the Weil converse now rests on the single zero-free Fourier obligation O1'.

The proof follows section 2 exactly, with these Lean choices:

- Coordinates: `phi c ρ = (1/2 - Re ρ)^2 - (Im ρ - c)^2`, `wsq c ρ = (Im ρ - c)^2 + (1/2 - Re ρ)^2`,
  `term c lam ρ = m(ρ) G_{c,lam}(gamma_ρ)`; `norm_term` gives |term| = m wsq e^{2 lam phi} and
  `re_gaussTest` gives Re G = e^{2 lam phi}[(x^2 - y^2) cos(4 lam x y) + 2 x y sin(4 lam x y)].
- Window: `window ρ₀` is the Finset of nontrivial zeros with Im ρ₀ - 1 < Im ρ <= Im ρ₀ + 1
  (`zetaSeam.finite_window`).
- Generic centre: `badOf ρ ρ'` is the unique tying centre for zeros of different ordinates
  (`eq_badOf_of_phi_eq`); `badSet ρ₀` is its image over window × window; `exists_generic_centre`
  picks c in the open interval |c - Im ρ₀| < |1/2 - Re ρ₀| outside the bad set
  (`Set.Ioo_infinite`, `Set.Infinite.sdiff`).
- Maximiser and gap: `Finset.exists_max_image` on the window; `eq_or_eq_reflect_of_phi_eq`
  shows a tie at a generic centre forces ρ = ρ₁ or ρ = 1 - conj ρ₁; `exists_maximiser_gap` then
  produces η > 0 with phi <= M - η on the window minus the pair (η := 1 if that set is empty).
- Outside the window: `phi_neg_of_not_mem_window` (|Im ρ - c| > 1/2 >= |1/2 - Re ρ|).
- Tail: `majorant` = e^{2 lam (M - η)} [ρ ∈ window] m wsq + m C₁/(1 + |gamma_ρ|^2), with C₁ the
  lam = 1 strip constant of E6Bridge6; `norm_term_le_majorant` is the pointwise bound for
  lam >= 1 off the pair (inside the window by the gap, outside by monotonicity of e^{2 lam phi} in
  lam when phi < 0 and then `norm_gaussTest_mul_le` at lam = 1); `tail_bound` sums it with
  `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`, `Summable.tsum_subtype_le`, giving
  A e^{2 lam (M - η)} + B with A the finite window sum and B the majorant tsum.
- Phase: `exists_lam_trig` picks theta = arg(-(x + i y)^2) (`Complex.cos_arg`, `sin_arg`) and an
  integer k with lam = (theta + 2 pi k)/(4 x y) >= lam₀ (`exists_int_gt` / `exists_int_lt` by the
  sign of x y; `Real.cos_add_int_mul_two_pi`); x = 0 needs no choice. The genericity of c was not
  messy, so no `GenericCentre` sub-obligation was needed.
- Assembly: `re_zeroSide_le` (pair term + tail via `zeroSide_pair_split` and
  `Complex.re_le_norm`), then lam₀ := max(1, A/(2 η K), B/(2 M K)) with K = m₁ wsq₁ > 0 and
  `Real.add_one_le_exp` twice.

## 6. House notes

- E6Bridge5 existed and compiled when this file was started, so `autocorr` and `weilForm` are
  imported from it, not redefined. The olean for E6Bridge6 was emitted with `lake env lean -o`
  (no lakefile edit); the integrator should add `E6Bridge6` to `defaultTargets` and the
  AxiomGuard list (the guard names are in section 3).
- `push_neg` is deprecated on this toolchain (warning only); the file avoids it.
- `simp` reports "`simp` made no progress" with backticks; the probe's `#guard_msgs` strings
  match that spelling.
