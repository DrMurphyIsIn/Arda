# Blind Read-Back Audit — Route Statements — 2026-09-16

Auditor read only the seven listed statement files plus MMDefs.lean, RHDefs.lean, and
MM_bragg_bridge.lean (permitted for comparison). Provenance header claims were treated as
the thing under test, not as evidence. Testimony is to what is written in the formal text.

---

## 1. MM_recurrence_deficit_eq_excess.lean

**TESTIMONY.** The theorem asserts a conjunction of two claims about the authored function
`recurrenceDeficit δ = (Real.exp δ - 1) * (1 - Real.exp (-δ))`. First conjunct: at δ = 1/10,
`recurrenceDeficit (1/10) = excess`, where `excess = Aoff - Aon = (e^(1/10) + e^(-1/10)) - 2`
(unfolding BraggDefect's `Aoff`, `Aon = 2`). Second conjunct: for every real δ > 0,
`0 < recurrenceDeficit δ`.

Expanding the first conjunct algebraically: `(e^δ - 1)(1 - e^(-δ)) = e^δ - 1 - e^δ·e^(-δ) +
e^(-δ) = e^δ - 1 - 1 + e^(-δ) = e^δ + e^(-δ) - 2`. At δ = 1/10 this is exactly
`e^(1/10) + e^(-1/10) - 2 = Aoff - Aon = excess`. So the first conjunct is a **true identity**
— it holds because the algebraic simplification is an identity for all δ, not a coincidence at
1/10. It is NOT trivially `rfl`: it requires the multiplication expansion plus `e^δ·e^(-δ) = 1`
(`Real.exp_neg`/`exp_add`), which are propositional lemmas, not definitional unfolding. The
second conjunct is genuinely true (both factors are strictly positive for δ > 0: `e^δ > 1` and
`1 - e^(-δ) > 0`) and is not `rfl`. The whole statement is `by sorry`.

**FLAGS:** none. (Mathematically sound; identity is real, not degenerate; requires proof.)

---

## 2. MM_offline_disjoint_discs.lean

**TESTIMONY.** For any finite set `S : Finset ℂ` such that every `z ∈ S` lies in the open
critical strip (`0 < z.re ∧ z.re < 1`), there exists a real r > 0 such that (a) for any two
DISTINCT members z, w of S (`z ≠ w`), the closed balls of radius r around them are disjoint,
and (b) every member's closed ball of radius r is contained in the open strip
`{s | 0 < s.re ∧ s.re < 1}`. This is a true statement of elementary metric topology: a finite
set of interior points of an open set admits a common radius small enough to both separate the
points and keep each ball inside the set (take r below half the minimum pairwise distance and
below the minimum distance to the strip boundary).

Quantifier check: the statement is `∀ S (finite), hypothesis → ∃ r > 0, ...`. It is NOT true
for all finite S "in the strip" only if a point sat on the boundary, but the hypothesis pins
strict interiority, so no trap there. Distinctness is handled correctly: the disjointness clause
is guarded by `z ≠ w`, so coincident-index/equal-element cases are excluded and the claim does
not degenerate. `Finset` gives set-membership (no multiplicity), so the `z ≠ w` guard is exactly
the right distinctness notion. Edge cases S = ∅ or singleton: the ∃ r is satisfiable vacuously
(any r bounded by strip clearance), no vacuity in a harmful direction. Statement is `by sorry`.

**FLAGS:** none. (Well-posed; distinctness correctly guarded; true and non-trivial to prove.)

---

## 3. MM_speiser_box_probe.lean

**TESTIMONY.** The theorem asserts: for every `s : ℂ` with `1/4 ≤ s.re ≤ 3/8` and
`6 ≤ s.im ≤ 10`, `deriv riemannZeta s ≠ 0`. I.e. the derivative of the Riemann zeta function
has no zero in the concrete closed rectangle [1/4, 3/8] × [6, 10], which lies strictly to the
LEFT of the critical line Re = 1/2.

Truth conditions: this is true iff ζ′ genuinely has no zero in that specific box. Speiser's
theorem states RH is equivalent to ζ′ having no zeros in 0 < Re < 1/2. The nontrivial zeros of
ζ′ are known (Levinson–Montgomery, and extensive computation) to cluster just to the RIGHT of
the critical line; the region Re < 1/2 being zero-free is the RH-equivalent statement globally.
But THIS statement is a single bounded box with fixed numeric corners, a finitely-checkable
winding/argument-principle target — verifying one box does not decide RH. So the statement is
mathematically decidable in principle by a computation over that rectangle, and is NOT
RH-equivalent (it is a bounded probe, not the full strip 0 < Re < 1/2). Whether it is TRUE
depends on the actual zero locations of ζ′ near Im ∈ [6,10]; the box is left of the line and
small, plausibly zero-free, but this auditor did not compute the winding number. Statement is
`by sorry`.

**FLAGS:** none. (Correctly a bounded probe, explicitly NOT the RH-equivalent Speiser statement;
no vacuity/triviality — it is a substantive analytic claim over a compact region.)

---

## 4. MM_rect_trace_reading.lean

**TESTIMONY.** Under an identical hypothesis block to `MM_bragg_bridge` (rectangle corners
σ0 ≤ σ1, T0 ≤ T1, 1 < σ1; a ball (c,R) containing the box; 1 ∉ ball; ζ nonvanishing on the
four traversed edge-segments; all zeros in the ball strictly interior to the box), the theorem
asserts that the sum over the zero-finset of the zeta divisor multiplicities equals
`(1/(2πi)) · ( ∫ bottom logDeriv − ∫ top logDeriv − I•Σ braggTerm − I•∫ left logDeriv )`.

Comparison to `MM_bragg_bridge` (`rect_explicit_formula_bragg`): that theorem states
`2πI · (Σ divisor) = ( ∫bottom − ∫top − I•Σbragg − I•∫left )`, with the SAME hypotheses and the
SAME right-hand bracket. The present statement is EXACTLY that equation divided through by 2πi:
LHS drops the `2πI` factor, RHS gains the scalar `1/(2πI)` premultiplying the identical bracket.
This is a pure algebraic rearrangement (`X = 2πI·Y  ⟺  Y = (1/(2πI))·X`), valid since 2πI ≠ 0.
Nothing changed beyond the division: identical corner/ball/nonvanishing/interiority hypotheses,
identical `braggTerm sigma1 T0 T1` and `RHInBoxAnalytic.zeroFinset c R hs1` vocabulary, identical
bracket term-by-term (same signs, same `I•` scalings, same integrand `logDeriv riemannZeta` on
the same segments). Statement is `by sorry`.

Note: `zeroFinset` depends (via MMDefs) on `divisor_ball_support_finite_of_one_notMem`, which
MMDefs carries as a `sorry`-support lemma; this is upstream of the statement's own `sorry` and
does not change what the theorem asserts.

**FLAGS:** none. (Faithful algebraic restatement of MM_bragg_bridge; hypotheses and RHS identical
modulo the /2πi division; no drift.)

---

## 5. MM_spectral_cooked_control.lean

**TESTIMONY.** For every `n : ℕ` and every `γ : Fin n → ℝ`, there exists a complex matrix
`A : Matrix (Fin n) (Fin n) ℂ` that is Hermitian AND whose characteristic polynomial equals
`∏ i, (X − C (γ i))` (the monic polynomial over ℂ with the reals `γ i` as its roots, with
multiplicity). This is TRUE, witnessed by the diagonal matrix `diag(γ 0, …, γ (n-1))`: a real
diagonal matrix is Hermitian, and its characteristic polynomial is exactly ∏(X − γi).

The statement is essentially trivial — "there is a finite Hermitian operator with any prescribed
finite REAL spectrum" — and the diagonal matrix discharges it immediately. Per the file's own
framing, this triviality is THE POINT: it is a declared negative control marking "finite operator
with prescribed real spectrum" as content-free, so that any RH-relevant difficulty must live in
the (absent here) completion/positivity clause, not in operator existence. Its triviality is
therefore intended (a negative control), not a defect in an intended-hard statement. Statement is
`by sorry`.

**FLAGS:** TRIVIAL (intended). Reason: true by the diagonal-matrix witness; the triviality is the
declared purpose (negative control), not an accidental degeneracy. No LIKELY-FALSE / VACUOUS
concern — it is genuinely true and non-vacuous.

---

## 6. RH_bl_finite_multiset.lean

**TESTIMONY.** For a finite `S : Finset ℂ` with 0 ∉ S, 1 ∉ S, and closed under the map
ρ ↦ 1 − conj(ρ) (`hsym`), the theorem asserts the equivalence: [for all n > 0,
`0 ≤ Re( Σ_{ρ∈S} (1 − (1 − 1/ρ)⁻¹ ^ n) )`]  ⟺  [every ρ ∈ S has ρ.re = 1/2]. This is a finite,
zeta-free specialization of the Bombieri–Lagarias positivity criterion, with the summand written
in terms of w = (1 − 1/ρ)⁻¹.

Mathematics, both directions (verified numerically):
- (⇐) All points on Re = 1/2. For ρ = 1/2 + it, w = (1 − 1/ρ)⁻¹ has |w| = 1 exactly (confirmed
  computationally for t ∈ {0.5,1,2,5,10}). Then Re(1 − wⁿ) = 1 − cos(nθ) ≥ 0 for every n, so
  each summand's real part is nonnegative and the sum is ≥ 0. Note this direction holds
  term-by-term and does NOT require `hsym`.
- (⇒) Contrapositive via an off-line symmetric pair. Take ρ = 0.7 + 3i and its partner
  1 − conj(ρ) = 0.3 + 3i (a valid `hsym`-closed 2-element S). The combined sum's real part goes
  NEGATIVE at n = 18 (computed −0.0119). So positivity for all n forces every point onto the
  line. The `hsym` hypothesis is what lets the criterion package off-line points into symmetric
  pairs; it is genuinely used in the ⇒ direction.
- Edge cases: S = ∅ — LHS is `0 ≤ Re(0) = 0`, true for all n; RHS is vacuously true; iff holds.
  h0 (0 ∉ S) is needed so 1/ρ is meaningful; h1 (1 ∉ S) excludes ρ = 1 where 1 − 1/ρ = 0 and the
  inverse would be Lean's junk `0⁻¹ = 0`. Both exclusions are load-bearing.

The statement as written appears mathematically correct in both directions on the small cases
tested. One caveat on Lean's `⁻¹`: for the excluded/degenerate arguments Lean uses junk values,
but h0/h1 remove the problematic ρ, and for admissible ρ ≠ 0,1 the value 1 − 1/ρ can still be 0
only if ρ = 1 (excluded), so `(1 − 1/ρ)⁻¹` is a genuine inverse on all of S. No falseness found.
Statement is `by sorry`.

**FLAGS:** none. (Iff verified true in both directions on small cases; symmetry hypothesis used;
edge/exclusion cases sound. Note: this is the finite algebraic CORE of BL, deliberately zeta-free
— it is NOT itself RH, and the header does not claim otherwise.)

---

## 7. RH_li_rung0_kernel.lean

**TESTIMONY.** The theorem asserts `0 ≤ Re( LiCriterion.taylorCoeff LiCriterion.riemannXi 0 )`,
with no hypotheses. Unfolding the RHDefs vocabulary: `phi f z = f(1/(1−z))`;
`taylorCoeff f n = (deriv^[n] (logDeriv (phi f)) 0) / n!`; and
`riemannXi s = (1/2)·s·(s−1)·completedRiemannZeta₀ s + 1/2`. At n = 0:
`taylorCoeff riemannXi 0 = (deriv^[0] (logDeriv (phi riemannXi)) 0) / 0! =
logDeriv (phi riemannXi) (0)` (since `deriv^[0]` is the identity and 0! = 1). Now
`phi riemannXi 0 = riemannXi (1/(1−0)) = riemannXi 1`, and `logDeriv g z = (deriv g z)/(g z)`, so
this number is the logarithmic derivative of `z ↦ riemannXi(1/(1−z))` evaluated at z = 0 — i.e.
the 0-th coefficient of the Li generating expansion, which under the standard normalization is
the first Li coefficient λ₁ (up to the criterion's conventions).

Its real part being ≥ 0 is exactly a Li-coefficient positivity statement (λ₁ ≥ 0). By the
Li/Bombieri–Lagarias criterion, nonnegativity of ALL such coefficients is equivalent to RH; the
individual λ₁ ≥ 0 is a known, believed-true statement but its unconditional proof is nontrivial
(λ₁ has an explicit expression tied to zero locations). So this is NOT trivially true — it is a
believed-true-but-substantive positivity claim, one rung of the Li ladder with the "Arb"
numeric hypothesis dropped (no hypotheses remain). Statement is `by sorry`.

**FLAGS:** ELABORATION-RISK (minor). Reason: the value hinges on `deriv^[0]` reducing to identity
and `logDeriv (phi riemannXi)` elaborating against the concrete `completedRiemannZeta₀`-based
`riemannXi`; the concrete number is a genuine Li coefficient. NOT trivial — its nonnegativity is
believed-true-unproven (λ₁ ≥ 0), so the `sorry` conceals real mathematical content, not a
one-line reduction. No VACUOUS/LIKELY-FALSE concern (the inequality is expected to hold).

---

## SUMMARY

All seven statements read as faithfully what their headers describe, with no false or vacuous
traps found. The two RH iff/inequality statements (BL finite multiset, Li rung-0) are
mathematically sound on the cases checked: the BL iff holds in both directions (on-line ⇒
term-wise nonnegative via |w|=1; off-line symmetric pair goes negative at n=18), and the Li
rung-0 kernel is a believed-true-unproven λ₁ ≥ 0 positivity, not a triviality. The three
"AUTHORED" MM lemmas (recurrence identity, disjoint discs, Speiser box) are true and non-trivial.
`MM_rect_trace_reading` is an exact /2πi rearrangement of `MM_bragg_bridge` with identical
hypotheses and RHS — no drift. `MM_spectral_cooked_control` is trivial BY DESIGN (diagonal-matrix
witness), a declared negative control, so its triviality is the point rather than a defect. The
only substantive caveats are elaboration/reduction dependencies, none of which change the stated
assertions. Every file ends in `by sorry` (nothing is actually proved here).

### Complete flag list

| File | Flag | One-line reason |
|------|------|-----------------|
| MM_recurrence_deficit_eq_excess | none | Identity (e^δ−1)(1−e^−δ)=e^δ+e^−δ−2 is real (not rfl); positivity true for δ>0. |
| MM_offline_disjoint_discs | none | Well-posed metric-topology fact; `z≠w` distinctness correctly guarded; strip interiority strict. |
| MM_speiser_box_probe | none | Bounded finitely-checkable ζ′-zero-free box, correctly NOT the RH-equivalent Speiser strip. |
| MM_rect_trace_reading | none | Exact /2πi rearrangement of MM_bragg_bridge; hypotheses and RHS bracket identical. |
| MM_spectral_cooked_control | TRIVIAL (intended) | True via diagonal matrix; triviality is the declared negative-control point, not a defect. |
| RH_bl_finite_multiset | none | Iff holds both directions on small cases (on-line |w|=1 ⇒ ≥0; off-line pair negative at n=18); h0/h1/hsym load-bearing. |
| RH_li_rung0_kernel | ELABORATION-RISK (minor) | Reduces to Re λ₁ ≥ 0 (believed-true-unproven), not trivial; depends on deriv^[0]=id and riemannXi elaboration. |
