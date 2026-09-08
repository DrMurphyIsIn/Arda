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

**What the fold buys (a genuine constant-factor edge win).** Work the right-half box
`[1/2, 1 − a] × [0, T]` instead of the full width `[a, 1 − a] × [0, T]`. This DELETES the expensive
near-`Re = 0` vertical edge (where zeta is FE-divergent and ball-arithmetic widths blow up) and
replaces it with the tame central line `Re = 1/2`; the horizontal edges halve. Since the vertical
edges dominate the winding cost (`arg` variation ~ `(T/2π)log T`) and their placement near `Re ∈ {0,1}`
is where enclosures are worst, pulling one edge into the central strip is a real per-enclosure win.

**What the fold does NOT buy -- you still need `hLine`.** It is tempting to instead take an OPEN-right
box `[1/2 + ε, 1 − a] × [0, T]`, show its winding is `0`, and conclude "all zeros on the line" with NO
on-line list. This does NOT work: pushing the contour to `Re = 1/2 + ε` clears only `Re > 1/2 + ε`,
leaving an `ε`-sliver `(1/2, 1/2 + ε)` at the line uncleared -- and closing that sliver is exactly the
hard thing being proved. The fold edge cannot sit ON `Re = 1/2` because that is where the on-line
zeros live and the contour must avoid zeros. So the robust route keeps BOTH edges off any zero
(the `[1/2, 1 − a]` box's edges at `1/2` and `1 − a` are zero-free by the region + the count-match)
and still matches `N` to an exhibited on-line list. The count-matching architecture (`hLine`,
`hcount`) is load-bearing; the fold is a constant-factor cost reduction on top of it, not a way to
drop `hLine`.

**The lever that scales with T: height-tiling.** Width-narrowing is bounded (<=4x via symmetry). To
tame the `N ~ T log T` growth, stack `[0, T]` into height bands `[T_k, T_{k+1}]`, certify each with its
own small-`N` winding + local on-line zeros, and sum via a band-ADDITIVITY lemma (the winding is
additive over stacked boxes; the shared horizontal edge cancels). Each band's vertical edges are
short, enclosures stay local and tight, and bands parallelize. `fold (constant factor) x tile
(T-scaling)` is the recipe for pushing `T` up.

**Suggested build order:** (1) a half-width variant of `rh_in_box_of_certificate` consuming
`zeta_count_eq_winding_generic` over `[1/2, 1 − a] × [0, T]` + `zeta_zero_on_line_of_quarter_clear`;
(2) a band-additivity lemma over stacked height boxes.

The `55/16` no-low-zeros residual (currently a documented hypothesis in `AllZeros_h100`) is separable
and closable, but the box shape needs care (two corrections over the naive version):

- **Use the band `[a, 1 − a] × [0, 55/16]`, NOT `[0, 1] × [0, 55/16]`.** The full-width box puts the
  pole `s = 1` at the corner `(1, 0)`, exactly as far from the ball center as the farthest box corner,
  so `choose_ball`'s window `(dc2, d12)` collapses to a point and the driver REFUSES it (no valid `R`
  excludes `s = 1`). The band's right edge `1 − a < 1` makes `|1 − c| >` the farthest-corner distance,
  so a valid ball exists.
- **The band alone does not clear the low strip -- the dVP region is SILENT below `55/16`.** The region
  requires `55/16 ≤ |γ|`, so for heights `Im < 55/16` a hypothetical zero is NOT confined to
  `[a, 1 − a]` -- it could a priori sit in the near-`Re = 1` sliver `(1 − a, 1)`. So the winding-0 band
  cert clears `[a, 1 − a]`, and the two outer slivers are closed KERNEL-SIDE with Mathlib facts:
  `riemannZeta_ne_zero_of_one_le_re` clears `Re ≥ 1` (hence `1 − a < Re < 1` reduces to the band edge
  via the region's own boundary), and the functional-equation reflection (`zeta_zero_reflect` /
  `riemannZeta_one_sub`) carries the `Re ≤ 0` side to the `Re ≥ 1` side. The kernel reduction lemma
  `no_low_zeros_of_empty_band` (dVP-symmetry session's lane) assembles these; the box-driver session
  emits the single winding-0 band Arb cert. Clean split.

Result: discharging `hγ_all` makes the `T = 100` certificate fully self-contained (only the irreducible
winding / edge-non-vanishing / enclosure Arb inputs remain). The band box's edges are still off any
zero, so it is NOT subject to the `ε`-sliver problem above -- that concern was specific to a fold edge
ON `Re = 1/2`.

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
