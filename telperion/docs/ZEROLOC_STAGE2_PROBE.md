# Stage-2 feasibility probe: argument-principle zero-count assembly

**Verdict: GO** — Stage 2 (exact total zero-count in a disk via the argument
principle) is assemblable from the merged atoms with one identified glue piece
(center-0-to-c shift lemma).

**conjecture1_proved = False.  NOT a proof of RH.**

---

## 1. Atoms assessed (origin/main, PRs #261/#262)

| Atom | Emitter | Lean artifact | Status |
|------|---------|---------------|--------|
| `argument_principle` | `emit_argument_principle.py` | `ArgumentPrinciple.lean` (dvp_geom_atoms) | kernel-green |
| `full_argument_principle` | `emit_full_argument_principle.py` | `FullArgumentPrinciple.lean` (dvp_geom_atoms) | kernel-green |
| `rect_argument_principle` | `emit_rect_argument_principle.py` | `RectArgumentPrinciple.lean` (dvp_geom_atoms) | kernel-green |
| `annulus_count` | `emit_annulus_count.py` | `AnnulusCount.lean` (dvp_geom_atoms) | kernel-green |
| Blaschke split | `DlvpBlaschkeSplitExpand.lean` | `logDeriv_eq_herglotz_add_entire` (zero_free_bridge) | kernel-green |

---

## 2. Composition analysis

### 2a. Does `full_argument_principle` + Blaschke split give `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor`?

**Yes, with one glue piece.**

`full_argument_principle` states: for `f = Σ_ρ (m ρ)(z-ρ)⁻¹ + E` with `E :
DiffContOnCl ℂ E (ball c R)`, `∮_{C(c,R)} f = 2πi · Σ_ρ (m ρ)`.  The center
`c` is a free variable — the theorem is not restricted to center 0.

`logDeriv_eq_herglotz_add_entire` states: `logDeriv f z = Σ_u (divisor f u)/(z-u)
+ [correction_sum + logDeriv g z]` where the sum is over `hfin.toFinset` (the
support of `divisor f (ball 0 R)`) and `g` is the zero-free part from the canonical
decomposition.  The correction sum `Σ_u (divisor u) * conj u / (R^2 - conj u * z)`
and `logDeriv g` together form the entire part `E` (analytic on `ball 0 R`, bounded
`O(L)` by `DlvpCorrectionBound` + item (c)).

**Glue needed:** The Blaschke split lives at center 0 (`ball 0 R`).
`full_argument_principle` uses a generic center `c`.  To apply them together, one
needs a **center-0-to-c shift lemma**: a transfer that re-expresses
`logDeriv ζ z = Σ (divisor ρ)/(z-ρ) + E` for `ρ ∈ ball c R` (not `ball 0 R`),
or equivalently confirms that translating `z -> z - c` converts the `ball 0 R`
Blaschke split into the `ball c R` form consumed by `full_argument_principle`.

Concretely: let `c` be the center of the localization disk, `T z = z - c` the
translation.  Then `divisor ζ (ball c R) ρ = divisor (ζ ∘ T) (ball 0 R) (ρ - c)`,
and the Blaschke split for `ζ ∘ T` at center 0 pulls back to one for `ζ` at center
`c`.  This is routine complex-analysis plumbing but requires a Lean lemma: either
`divisor_translate` or a direct re-centering of `logDeriv_eq_herglotz_add_entire`
replacing `0` with `c`.

Once the shift lemma is in hand, the full assembly is:

```
logDeriv_eq_herglotz_add_entire(c=0, shifted to c)
    ↓  match  f = ζ'/ζ,  m = divisor,  E = correction + logDeriv g
full_argument_principle(c, R)
    ↓
∮_{C(c,R)} ζ'/ζ = 2πi · Σ_{ρ ∈ ball c R} divisor ζ ρ
    ↓  divide by 2πi (non-zero: π ≠ 0)
(2πi)⁻¹ ∮_{C(c,R)} ζ'/ζ = Σ divisor  =  total zero count in ball c R
```

No further Mathlib gap: `circleIntegral.integral_sub_inv_of_mem_ball`,
`DiffContOnCl.circleIntegral_eq_zero`, `integral_fun_sum`, `integral_const_mul`,
and `integral_add` are all present (confirmed by the kernel-green artifacts).

### 2b. Toy composition confirmed

`WindingProbe.lean` (added to `examples/zeta_zero_localization/lean/`) proves
sorry-free that for `f z = 2*(z-c0)⁻¹` on `C(c0, 3/2)`:

```
∮_{C(c0,3/2)} f = 4πi         [winding_probe_single_pole, sorry-free]
(2πi)⁻¹ · ∮ f = 2             [winding_probe_count, sorry-free]
```

This uses the same Mathlib lemma chain as the emitted `FullArgumentPrinciple`
artifact and constitutes a concrete self-contained check of the composition.

---

## 3. Contour shape: disk vs. rectangle

Stage-3 localization boxes are **rectangles** in the critical strip, not disks.
The available atoms split on contour shape as follows:

- `full_argument_principle` + `argument_principle`: **disk** (`C(c,R)`).  Complete
  (residue sum + Cauchy vanishing both packaged).
- `rect_argument_principle`: **rectangle** (`∂([x0,x1] × [y0,y1])`).  Packages only
  the **Cauchy-vanishing half** (`∮_{∂rect} E = 0` for holomorphic `E`).  The
  residue-sum-on-a-rectangle is NOT packaged; Mathlib's residue lemmas are
  circle-based.

**Recommendation: use disk contours for Stage 2.**  Inscribe a disk `ball c R`
inside each localization rectangle (choose `R < half the shorter side`).  This
gives the full argument principle cleanly.  The Stage-3 containment argument
then requires: all zeros in the box are in the inscribed disk, which is a
geometric side condition (the box must be thin enough relative to `R`).

Alternatively, a rectangle residue-sum can be assembled from scratch via the
rectangular Cauchy theorem applied to `(z - ρ)⁻¹` for each pole separately —
but this requires new Lean work (the `integral_boundary_rect_eq_zero_of_differentiableOn`
path covers only the analytic half; the pole-encircling half on a rectangle needs
`winding_number_rect` or a manual residue calculation).  Estimated cost: 1-2 weeks
of Lean work.  The disk-inscribed approach is cheaper for Stage 2.

---

## 4. Center-0-to-c shift: the remaining dependency

The parallel RH session identified this gap and flagged it as a dependency.  This
probe confirms it is **the sole structural gap** between the merged atoms and a
complete Stage-2 certificate.

Required lemma (call it `logDeriv_shift_center`):

```lean
theorem logDeriv_shift_center {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp (f ∘ (· + c)) (g ∘ (· + c)) R) ... :
    logDeriv f z
      = (∑ u ∈ hfin.toFinset,
            (divisor f (ball c R) (u + c) : ℂ) / (z - (u + c)))
        + E_shifted z
```

or equivalently a version of `logDeriv_eq_herglotz_add_entire` with the ball
centered at `c` instead of `0`.  This is a straightforward translation argument
(change of variables `w = z - c`) but requires careful handling of the `divisor`
functoriality under translation, which is not yet in Mathlib.

Effort estimate: 3-5 days of focused Lean work for an expert familiar with
`MeromorphicOn.divisor` and `AnalyticOnNhd`.

---

## 5. Count-matching for Stage 3

Stage 1 produces a **lower bound**: at least N zeros of xi (equivalently zeta) on
the critical line up to height T, counted via sign-change certificates.  Stage 2
produces an **exact total**: the winding number `(2πi)⁻¹ ∮ ζ'/ζ` equals the total
zero count (with multiplicity) in the contour.

For Stage 3 ("all zeros in the box are on the line"), the comparison is:

```
Stage-1 count (on-line zeros, >= N)  =  Stage-2 count (total zeros, = N)
  ↓ both count with MULTIPLICITY
  ↓ both use the SAME contour / region
  all zeros in the region are on the line (no room for off-line zeros)
```

The counts are compatible: both use `MeromorphicOn.divisor` (the multiplicity map)
summed over a Finset.  The Stage-1 sign-change family uses `xi_line_zeros_family`
whose count is a lower bound on `∑_{ρ in region} divisor ζ ρ`.  Stage 2 gives the
exact value of this same sum.

One subtlety: Stage 1 counts zeros of `xi` (the completed zeta `Lambda`) while
Stage 2 counts zeros of `ζ` (the Riemann zeta); they coincide in the critical strip
away from `s=0,1` since `Lambda = completed_zeta` and `ζ` have the same zeros
there.  A `divisor_xi_eq_divisor_zeta` lemma is needed to equate the two counts
formally; this is a straightforward consequence of the functional equation and the
factor decomposition, estimated at 1-2 days.

Simplicity (simple vs. multiple zeros): both Stage 1 and Stage 2 count with
multiplicity.  No distinctness assumption is needed for the equality argument;
the bound `stage1_count >= N = stage2_count` forces the off-line multiplicity to be
zero, which implies every zero in the region is on the line (regardless of
multiplicity).

---

## 6. GO/NO-GO verdict and assembly path

**GO.**

The argument-principle zero-count certificate for Stage 2 is assemblable from the
merged atoms (PRs #261/#262 + the Blaschke split chain) with the following concrete
assembly sequence:

1. **Center shift** (new, ~3-5 days): `logDeriv_shift_center` re-expressing the
   Blaschke split at a generic center `c`.
2. **Match hypotheses** (~1 day): identify `f = ζ'/ζ`, `m = divisor ζ (ball c R)`,
   `E = correction_sum + logDeriv g` (holomorphic on `ball c R` by existing bounds).
3. **Apply `full_argument_principle`** (zero new work): `∮_{C(c,R)} ζ'/ζ = 2πi · Σ divisor`.
4. **Divide by 2πi** (~1 day): `(2πi)⁻¹ ∮ ζ'/ζ = Σ divisor` = zero count.
5. **xi-to-zeta divisor bridge** (~1-2 days): equate Stage-1 xi count and Stage-2
   zeta divisor sum.

Total estimated Stage-2 effort: **5-9 days of focused Lean work.**

Remaining pieces:
- `logDeriv_shift_center` (center-0-to-c, sole structural gap)
- box-vs-disk geometry (inscribed disk recommendation, negligible Lean cost)
- `divisor_xi_eq_divisor_zeta` (xi/zeta count bridge, minor)

No Mathlib gap in the contour-integral machinery itself; all required circle lemmas
are present and kernel-verified.

---

*Probe artifact: `examples/zeta_zero_localization/lean/WindingProbe.lean` (sorry-free
toy composition, NOT wired into CI).*
*conjecture1_proved = False.*
