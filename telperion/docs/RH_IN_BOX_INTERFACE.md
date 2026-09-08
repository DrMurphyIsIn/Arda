# RH-in-a-Box: Consumption Interface

**Purpose.** One written contract for consuming the box-count-via-winding atoms from the
`zeta_zero_localization` example, so parallel sessions build against the real interface (not a
guessed one). Written by the box-driver session for the dVP-symmetry session (and anyone reusing the
argument-principle box count).

**Honesty invariant.** `conjecture1_proved = False` throughout. These atoms give a kernel-verified
*implication* (winding + boundary hypotheses => zero count / localization); the winding integer and
enclosures are documented **non-kernel Arb input**. Nothing here proves RH.

---

## 1. The atom: `RHInBoxAnalytic.zeta_count_eq_winding_generic`

File: `telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean` (on `main`).

```lean
zeta_count_eq_winding_generic
  (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ) (N : ℤ)
  (hRpos : 0 < R) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1)
  (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)                     -- box strictly inside the Blaschke ball
  (hs1 : (1 : ℂ) ∉ Metric.ball c R)            -- the pole s = 1 excluded from the ball
  (hwind : <four-segment boundary integral of logDeriv riemannZeta> = 2 * π * I * (N : ℂ))
  (hArb : ∀ (E : ℂ → ℂ), <split ⟹ edge-non-vanishing ∧ strict-interiority ∧ integrability>) :
  ∃ (s : Finset ℂ) (d : ℂ → ℤ),
    (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧                                        -- multiplicities ≥ 1
    (∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
       riemannZeta ρ = 0 → ρ ∈ s) ∧                                   -- every box zero is captured
    (∑ ρ ∈ s, d ρ) = N                                                -- total count = winding N
```

`s := RHInBoxAnalytic.zeroFinset c R hs1`, `d := MeromorphicOn.divisor riemannZeta (ball c R)` -- the
**actual** divisor of zeta on the ball, NOT a supplied/assumed set. The atom derives the Blaschke
split, E-holomorphicity, `d ≥ 1`, box-zero capture, and `∑ d = N` in-kernel.

Downstream: `RHInBox.rh_in_box_of_certificate` composes this with an on-line Finset to conclude
"every box zero has `Re = 1/2`". `AllZerosUpToHeight` + `AllZeros_h100` add dVP+FE confinement for
the "all zeros up to height T" statement.

## 2. Boundary convention (match `hwind` exactly)

`Bd_∂B(f) = (∫_{sigma0}^{sigma1} f(x + T0·i) dx) − (∫_{sigma0}^{sigma1} f(x + T1·i) dx)`
`           + I·(∫_{T0}^{T1} f(sigma1 + y·i) dy) − I·(∫_{T0}^{T1} f(sigma0 + y·i) dy)`

with `sigma0 ≤ sigma1`, `T0 ≤ T1` (counter-clockwise: bottom − top + I·right − I·left). `hwind`
asserts `Bd_∂B(logDeriv riemannZeta) = 2·π·I·N`, i.e. `N = (2πi)^{-1} ∮_∂B ζ'/ζ` = the winding number
of `ζ` around `∂B`.

## 3. Kernel vs Arb (the trust boundary)

- **KERNEL (the atom proves):** the split `ζ'/ζ = Σ_ρ d(ρ)/(z-ρ) + E` (E holomorphic), `d ≥ 1`,
  box-zero capture, and `∑ d = N` (argument principle: `Bd(E)=0` by Cauchy + `box_residue_sum` +
  per-pole `rect_winding`).
- **ARB NON-KERNEL INPUT (you supply; the driver certifies):** `N` (via `hwind`), edge non-vanishing
  on the four sides, and the integrability side-conditions (in `hArb`). `hs1` / `hbox_ball` are
  concrete geometry discharged by `norm_num`/`nlinarith`.

## 4. The Blaschke ball

The driver's `choose_ball` sets `c = ((sigma0+sigma1)/2) + ((T0+T1)/2)·I` and `R² =` the **exact-rational
midpoint** between the farthest box-corner distance² (`dc2`) and `|1 − c|²` (`d12`), giving
`dc2 < R² < d12` as exact rationals -- so the box is strictly inside the ball and `s = 1` is strictly
outside. For a box reaching near `Re = 1` the window `(dc2, d12)` is tiny but nonzero; the midpoint is
safe (exact arithmetic). Do NOT hand-pick `R`; use the driver.

## 5. The driver

`telperion/examples/zeta_zero_localization/generate.py`'s `run_box(re_lo, re_hi, im_lo, im_hi)`
computes, for any rational box: the winding integer `N` (rigorous zeta Taylor-segment enclosures ->
half-plane-witnessed winding), the edge non-vanishing, the Blaschke ball `(c, R)`, and emits a Lean
file wiring the `hwind` / `hArb` bundle. It REFUSES an invalid box (sigma-range excluding `1/2`, or
`s=1` in the ball) or an unresolved sweep. Point it at your box corners; it produces exactly what the
atom consumes.

## 6. Wiring a symmetry-reduced (half / quarter) box -- what it buys, and what it does NOT

`ZeroFreeBridge.zeta_zero_on_line_of_quarter_clear` (PR #320) reduces the work to the fundamental
domain of zeta's zero-set symmetry group. That group is the Klein four-group `V4 = {id, ρ↦1−ρ,
ρ↦conj ρ, ρ↦1−conj ρ}` -- two PERPENDICULAR mirrors (functional equation across `Re = 1/2`,
conjugation across `Im = 0`). Fundamental domain = ONE quarter (upper half of the right-of-line
strip). There is no third independent symmetry (a 45-degree mirror would need a relation zeta has
no such thing), so **quarter is the hard floor** -- 1/8, 1/16 are unreachable by symmetry. Anything
tighter than 1/4 comes from the zero-free REGION (width) or from raising the height floor, not from a
fraction.

**What the fold buys (a constant-factor edge win) -- and its hard limit.** Moving a vertical edge
inward from the expensive near-`Re = 0` / near-`Re = 1` zones (where zeta is FE-divergent /
pole-adjacent and ball-arithmetic widths blow up) into the central strip is a real per-enclosure win,
since the vertical edges dominate the winding cost (`arg` variation ~ `(T/2π)log T`) and their
placement near `Re ∈ {0,1}` is where enclosures are worst. BUT the edge canNOT be pushed all the way
to `Re = 1/2`: that line is the on-line-zero LOCUS, so `ζ'/ζ` has poles there and the `hArb`
edge-non-vanishing hypothesis `∀ y, riemannZeta (1/2 + iy) ≠ 0` is FALSE -- the contour would run
through zeros. The furthest a count-match edge can go is `Re = 1/2 + ε` (off the zeros).

**Why you cannot fold to a half-width count-match box -- you still need `hLine`.** It is tempting to
run the count-match on `[1/2, 1 − a] × [0, T]` (or `[1/2 + ε, 1 − a]`) and halve the width. This does
NOT work:
- An edge exactly at `Re = 1/2` is contaminated by the on-line zeros (above), so the `[1/2, 1 − a]`
  box is NOT admissible -- its `hArb` left-edge non-vanishing is false.
- Pushing to `[1/2 + ε, 1 − a]` and showing winding `0` clears only `Re > 1/2 + ε`, leaving the
  `ε`-sliver `(1/2, 1/2 + ε)` at the line uncertified -- and closing that sliver is exactly the hard
  thing being proved.

So the ROBUST count-match route keeps the FULL width `[a, 1 − a] × [0, T]`, with BOTH vertical edges
(`Re = a` and `Re = 1 − a`) off every zero, and matches `N` to an exhibited on-line list. The
count-matching architecture (`hLine`, `hcount`) is load-bearing; you cannot drop `hLine`.

**The symmetry fold is a THEOREM-LEVEL reduction, not a contour trick.** `#320` + the Im-preserving
reflection `ρ ↦ 1 − conj ρ` (`ZeroFreeBridge.riemannZeta_reflect_line_eq_zero`, PR #324) DO halve the
region conceptually: `RHInBoxBands.rh_full_box_of_left_half` (PR #324) proves that if every zero in
the closed left half `[a, 1/2] × [T0,T1]` is on the line, so is every zero in `[a, 1 − a] × [T0,T1]`.
This is a SOUND reduction, but its premise is subject to the SAME obstruction: certifying the closed
left half via the argument principle needs an edge on `Re = 1/2`. So the symmetry does NOT yield a
dischargeable half-width certificate; discharging the left half would require an indented-contour
("keyhole") argument that dodges the on-line zeros -- a separate piece of complex analysis.

**The lever that scales with T: height-tiling.** Width-narrowing is bounded (<=4x via symmetry) AND
capped by the above obstruction. To tame the `N ~ T log T` growth, stack `[0, T]` into height bands
`[T_k, T_{k+1}]`, certify each with its own small-`N` winding + local on-line zeros, and glue via a
band-ADDITIVITY lemma (`RHInBoxBands.rh_box_of_bands` / `rh_box_two_bands`, PR #324; a zero's `Im`
lies in one band, so per-band conclusions glue with no shared-edge integral needed). Each band's
vertical edges are short, enclosures stay local and tight, and bands parallelize. This is the
recipe for pushing `T` up.

**Build status (updated by PR #324):**
- ~~(1) a half-width variant of `rh_in_box_of_certificate` over `[1/2, 1 − a] × [0, T]`~~ -- NOT
  dischargeable (edge on the zero locus; see above). Superseded by (1').
- (1') the theorem-level width fold `RHInBoxBands.rh_full_box_of_left_half` is BUILT (PR #324); it
  awaits an indented-contour half-box certificate to discharge its left-half premise.
- (2) the band-additivity lemma `RHInBoxBands.rh_box_of_bands` is BUILT (PR #324); wire per-band
  `rh_in_box_of_certificate` results into it to certify tall boxes.

The `55/16` no-low-zeros residual (currently a documented hypothesis in `AllZeros_h100`) is separable:
a small bottom box over the confinement BAND `[a, 1 − a] × [0, 55/16]` with `∑ divisor = 0`
(winding `0`, `d ≥ 1` ⟹ `s = ∅`) would prove no zeros in the band below height `55/16`; combined with
the dVP region (no zeros OUTSIDE the band) this closes the residual and makes the height certificate
self-contained. Use the band width, NOT `[0, 1]` -- the latter puts the pole `s = 1` on a corner,
which the §4 ball construction cannot exclude. The band edges are off both the zeros and the pole, so
this box is NOT subject to the `ε`-sliver problem above.

## 7. Gotchas

- `hArb` is `∀ E, (split for E) → (big conjunction)` -- a universally-quantified bundle over the entire
  `E`; the driver discharges it. Do not try to prove it by hand; emit it.
- The atom's `s`/`d` are the ACTUAL `MeromorphicOn.divisor`, so `∑ d = N` is a statement about zeta's
  real zeros; do not substitute an assumed pole set.
- The `zeta_zero_localization` lakefile `require`s `../../zero_free_bridge/lean` (to consume the dVP
  region). Keep both siblings present and rev-locked (same mathlib rev) in any checkout that builds
  these targets.
- Everything is `#print axioms`-guarded (`AxiomGuardRHInBox.lean`) at `{propext, Classical.choice,
  Quot.sound}`; keep new consumers in that tier.
