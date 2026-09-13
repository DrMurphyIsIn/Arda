/-
RvMNTLadderH4000 — Arc A (effective RvM), the h4000-instantiated corollary.

`nt_effective_bound_of_ladder` (RvMNTLadder) takes the ladder conclusion abstractly; the ported
`AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands` discharges it from its 90
certified hypotheses (the per-band Arb winding/edge bundles — the documented trust seam).  This
file threads the two together: the effective Riemann–von Mangoldt bound

  `|N − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`   (4 ≤ T ≤ 4000)

holds under the ladder's OWN certificate bundle plus the single-point caveat `ζ(1/2+iT) ≠ 0`,
the box-edge ξ-nonvanishings, and the boundary winding `= 2πiN` — the whole-segment `hζne`
hypothesis fully replaced.  Pure mechanical instantiation; no new mathematics.
conjecture1_proved = False.
-/
import Mathlib
import RvMNTLadder
import AllZeros_h4000

open Complex Real MeasureTheory DiffractionCore

namespace Backlund

set_option maxHeartbeats 1000000 in
/-- **The effective RvM bound under the h4000 ladder certificates** — the fully-instantiated
trust-shrunk form.  conjecture1_proved = False. -/
theorem nt_effective_bound_h4000 (T : ℝ) (hT : 4 ≤ T) (hT4 : T ≤ 4000) (N : ℤ)
    (hband0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((0) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1050)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1050) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1100)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1100) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1150)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1150) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1250)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1250) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1300)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1300) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1350)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1350) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1450)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1450) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1500)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1500) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1550)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1550) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1650)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1650) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1700)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1700) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1750)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1750) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1850)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1850) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1900)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1900) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (1950)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hband38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((1950) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg0 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg1 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg2 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg3 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg4 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg5 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg6 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg7 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg8 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg9 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg10 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg11 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg12 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg13 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg14 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg15 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg16 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg17 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg18 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg19 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg20 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg21 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg22 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg23 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (2960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg24 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((2960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg25 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3000) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3040)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg26 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3040) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3080)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg27 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3080) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3120)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg28 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3120) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3160)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg29 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3160) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3200)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg30 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3200) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3240)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg31 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3240) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3280)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg32 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3280) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3320)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg33 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3320) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3360)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg34 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3360) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3400)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg35 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3400) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3440)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg36 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3440) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3480)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg37 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3480) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3520)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg38 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3520) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3560)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg39 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3560) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3600)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg40 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3600) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3640)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg41 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3640) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3680)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg42 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3680) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3720)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg43 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3720) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3760)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg44 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3760) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3800)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg45 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3800) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3840)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg46 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3840) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3880)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg47 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3880) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3920)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg48 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3920) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (3960)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hseg49 : ∀ ρ : ℂ, (((1 / 2000000) : ℝ) ≤ ρ.re ∧ ρ.re ≤ (1999999 / 2000000)) →
      (((3960) : ℝ) ≤ ρ.im ∧ ρ.im ≤ (4000)) → riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hγ : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → 55 / 16 ≤ |ρ.im|)
 (hhalf : riemannZeta (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzBot : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ)) ≠ 0)
    (hnzTop : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzL : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((-1:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hnzR : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((2:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hwind : (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((0:ℝ) : ℂ) * I))
        - (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((T:ℝ) : ℂ) * I))
        + I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((2:ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((-1:ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * (N : ℂ)) :
    |(N : ℝ) - 1 - ZeroFreeBridge.riemannSiegelTheta T / π|
      ≤ Real.log ((4 * T + 19) / (2 - Real.pi ^ 2 / 6)) / Real.log (7 / 6) + 2 :=
  nt_effective_bound_of_ladder T hT hT4 N
    (AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands
      hband0 hband1 hband2 hband3 hband4 hband5 hband6 hband7 hband8 hband9 hband10 hband11 hband12 hband13 hband14 hband15 hband16 hband17 hband18 hband19 hband20 hband21 hband22 hband23 hband24 hband25 hband26 hband27 hband28 hband29 hband30 hband31 hband32 hband33 hband34 hband35 hband36 hband37 hband38 hseg0 hseg1 hseg2 hseg3 hseg4 hseg5 hseg6 hseg7 hseg8 hseg9 hseg10 hseg11 hseg12 hseg13 hseg14 hseg15 hseg16 hseg17 hseg18 hseg19 hseg20 hseg21 hseg22 hseg23 hseg24 hseg25 hseg26 hseg27 hseg28 hseg29 hseg30 hseg31 hseg32 hseg33 hseg34 hseg35 hseg36 hseg37 hseg38 hseg39 hseg40 hseg41 hseg42 hseg43 hseg44 hseg45 hseg46 hseg47 hseg48 hseg49 hγ)
    hhalf hnzBot hnzTop hnzL hnzR hwind

end Backlund
