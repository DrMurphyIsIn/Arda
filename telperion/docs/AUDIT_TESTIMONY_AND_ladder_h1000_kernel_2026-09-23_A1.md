# Audit testimony: AND_ladder_h1000_kernel (anduril), blind auditor A1, 2026-09-23

Verdict: **pass = true**, axioms_clean = true, statement_byte_identical = true.
**conjecture1_proved = False.** This is a finite verification up to height 1000. It says nothing about the Riemann Hypothesis.

## 1. Statement read-back (done before reading the artifact)
`Statements/AND_ladder_h1000_kernel.lean` imports only Mathlib and states
`∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2`.
This uses Mathlib's `riemannZeta`, which is defined at s = 1. The condition `0 < ρ.im` excludes the trivial zeros, which all have Im = 0. So the statement says: every zeta zero with height in (0, 1000] lies on the critical line.

## 2. Canonical gate
- The gate used `R.load_campaign(telperion/missions/anduril)`. The node was found with status `draft`.
- `V.statement_matches(AllZerosKernel_h1000.lean, _normalized_statement)` returned **True**.
- The declaration is byte-identical to the statement file up to `:=`, and it occurs once in the artifact.
- `artifact_incompleteness_markers` found nothing in the artifact or in any of the **254 modules** of its local import closure. The closure spans three source directories: zeta_reflection, zeta_zero_localization (AllZeros_h1000, RHInBox*, TuringBand, ...) and zero_free_bridge (Dlvp*, StripRepr*, ...).

## 3. Kernel
- `leanlock.sh lake build --no-build` reported: All targets up-to-date (9042 jobs).
- Probe `#print axioms AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000` returned [propext, Classical.choice, Quot.sound].
- An `example` restating the pure-Mathlib statement type-checked against the capstone. The probe has since been deleted.

## 4. Trust boundary
- I grepped the closure for axiom, opaque, native_decide, ofReduceBool, ofReduceNat, implemented_by, extern, unsafe, skipKernelTC, sorry and admit. Every hit is in a comment or docstring.
- Nothing in the closure redefines `riemannZeta`.
- The capstone is `H1000Line.all_nontrivial_zeros_up_to_height_1000_of_encl E hpin henc hslab0 hslab1`. Each of the four hypotheses is a proved theorem (`hpin`, `henc`, `hslab0`, `hslab1`), each with the three standard axioms only.
- Inside `_of_encl`, the remaining band inputs are also discharged by proved theorems:
  - band 0's lower slab: `slab0_band0`
  - hLine: `seg_lineHyp`
  - hγ: `HeightFloor.height_floor`, stated for every H with no hypotheses
  - geometry: `seg_geom`
  - band statements: `seg_stmt`
- Negative controls in the guard: the octant label + 4 is rejected, as is an F = 1000 octant budget, a point endpoint box and an F = 10 slab cell. The guard builds, so the kernel accepts each `= false`.
- My own controls:
  - Label 2 for T41 piece 0 was rejected, as expected.
  - Label 6 was accepted. This is not a fault: labels are half-plane tests, and ζ(2+41i) = 0.7958 - 0.0355i satisfies both Re > 0 and Im < 0.
  - A tighter slab budget F = 1.1e-6 was also accepted. That is a stronger check than the one used; soundness rests on the separate `budget` theorem.

## 5. Independent numerics (mpmath 1.3.0, single process)
- `nzeros(1000)` = **649**. Enumerating the zeros gives 649, the last at 999.7916 and the next at 1001.349. No zero lies below 55/16.
- All 25 declared band counts (7, 14, 17, ..., 32) match mpmath exactly. The declared counts sum to 650, which is 649 plus one double count: the zero at 241.0492 lies in the band 5/6 overlap [241, 241.25]. This is consistent.
- Slab spot checks found no zero inside any of the five slabs checked. For each, the table gives the nearest-zero distance and the minimum |ζ| on a grid over [1/2, 1] × slab:

  | Slab | Nearest zero | Min \|ζ\| |
  |---|---|---|
  | U41 | 0.081 | 0.12 |
  | L481 | 0.83 | 2.66 |
  | U965_4 | 0.20 | 0.55 |
  | L960 | 0.48 | 2.07 |
  | U1000 | 0.21 | 0.86 |

- The three U41 cells (σ = 7/12, 3/4, 11/12; R = 0.0882) have |ζ(center)| of 0.188, 0.321 and 0.443. The minimum on each disk is at least 0.074.
- Edge argument changes, computed numerically along x from 2 to -1, all fall inside the certified intervals:

  | T | Numeric value | Certified interval |
  |---|---|---|
  | 41 | 2.696558 | [2.695651, 2.706101] |
  | 520 | -3.345992 | [-3.364219, -3.341448] |
  | 241.25 | 2.677834 | [2.657303, 2.680931] |
  | 241 | -2.653202 | [-2.658984, -2.651562] |

## 6. What this establishes, and what it does not
**Established:** a kernel-checked, hypothesis-free Lean proof, using only the three standard axioms, that every ζ zero with 0 < Im ρ ≤ 1000 has Re ρ = 1/2. The data it rests on agrees with independent numerics.

**Not established:**
- RH, or anything above height 1000.
- CI enforcement. This audit ran locally only.

conjecture1_proved = False.
