/-  ReflectedBand_t14_Kernel.lean -- ANDURIL G2, KERNEL DISCHARGE: the pilot conclusion of
    `ReflectedBand_t14.pilot` with NO hypotheses.

    ## What changed against `ReflectedBand_t14`

    `ReflectedBand_t14.pilot` proves "2 on-line zeros of `completedRiemannZeta` in [14, 22]" from the
    kernel-decided sign chain `ok` plus three Arb enclosure HYPOTHESES `hmem0/1/2`: `gLine t` lies in
    a dyadic box of relative width about 1e-75 at t = 14, 15, 22.  Those boxes need `|Gamma_R|` and
    zeta at about 250 bits; no evaluator on the island reaches that (the kernel zeta boxes used below
    are 0.016 to 0.44 wide, and nothing bounded `|Gamma_R|` at all before `KernelGammaEnvelope`).  So
    this file uses the documented fallback: a WIDER-box band certificate whose memberships the
    kernel CAN prove.

      * `dK`   : three dyadic `gLine` boxes, each sign-definite, far wider than Arb's:
                   t = 14 : [-2^-1,  -2^-37]      (true value -2.05e-6)
                   t = 15 : [ 2^-37,  2^2  ]      (true value  6.27e-6)
                   t = 22 : [-2^3,   -2^-55]      (true value -3.19e-8)
      * `okK`  : `checkLine dK.boxes = true`, decided by the kernel (`decide`), exactly as `ok`.
      * `KernelBandEnclosures.gLine14_encl`, `gLine15_encl`, `gLine22_encl` : the three
        memberships, PROVED.
      * `pilot_kernel` : the pilot conclusion, verbatim, with no hypotheses, through the unchanged
        once-proven soundness theorem `CheckBand.checkLine_correct` and the same grid
        `ReflectedBand_t14.grid`.

    ## How each membership is proved (all kernel-checked, no Arb input)

    `KernelGammaEnvelope.gLine_decomp_explicit` writes
        gLine t = M(t) * S(t),   S(t) = cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it),
    with `M(t) = pi^(-1/4) |Gamma(1/4 + i t/2)|` and `(3/4) exp(-pi |t|/2) <= M(t) <= 4`
    (`gammaRMag_bounds`: Euler-integral norm bound + reflection formula).  The two factors of S come from:

      * zeta boxes : `ForgeZeta14/15` (EM order 3, N = 50, existing) and `ForgeZeta22` (EM order 3,
        N = 10, new, emitted by the island's trig_forge.py);
      * phase boxes: `ForgeThetaBox.cossin_14/15` (existing) and `ForgePhi22.cossin22` (new:
        imLnVal (1/4) 11 128 + `ForgeRate.rate_at`, phase in [2.046, 2.585], so cos <= 0, sin >= 0.35).

    Then S(14) in [-0.1224, -0.0893], S(15) in [0.654, 0.769], S(22) in [-1.819, -0.1567], and the
    boxes follow by interval multiplication with the M envelope.  The inner (small) edge of every box
    is set by the crude lower bound on M, not by the zeta or phase precision; each has a margin of at
    least 2.5x.

    ## Layout

    The analysis (the three memberships, the Gamma_R envelope use, the S(t) bounds) lives in
    `KernelBandEnclosures`, together with the measured kernel time of every enclosure.  This file
    holds only the band: `dK`, `okK`, `pilot_kernel`, contiguous, in the shape of
    `ReflectedBand_t14` (`d`, `ok`, `grid`, `pilot`).

    conjecture1_proved = False.  Two verified zeros at low height by finite interval arithmetic and the
    intermediate value theorem; this is not a proof of RH.
-/
import CheckBand
import ReflectedBand_t14
import KernelBandEnclosures

open DIntvProd ZetaReflection XiLineZeros

namespace ReflectedBand_t14_Kernel

/-- The kernel-provable band: WIDE dyadic `gLine` boxes at the grid heights 14, 15, 22
    (`[-2^-1, -2^-37]`, `[2^-37, 2^2]`, `[-2^3, -2^-55]`), signs (neg, pos, neg). -/
def dK : BandData := ⟨[⟨-68719476736, -1, -37⟩, ⟨1, 549755813888, -37⟩, ⟨-288230376151711744, -1, -55⟩]⟩

/-- **KERNEL-CHECKED sign chain** of the wide boxes (same checker as `ReflectedBand_t14.ok`). -/
theorem okK : checkLine dK.boxes = true := by decide

/-- **THE G2 PILOT CONCLUSION, HYPOTHESIS-FREE.**  Verbatim conclusion of `ReflectedBand_t14.pilot`:
    two strictly increasing heights in `[14, 22]` where `completedRiemannZeta` vanishes on the
    critical line.  From the kernel-decided `okK`, the proved memberships
    `KernelBandEnclosures.gLine14_encl`, `gLine15_encl`, `gLine22_encl`, and the once-proven
    `CheckBand.checkLine_correct`. -/
theorem pilot_kernel :
    ∃ xs : List ℝ, xs.length = 2 ∧ xs.IsChain (· < ·) ∧
        (∀ t ∈ xs, (14 : ℝ) ≤ t ∧ t ≤ (22 : ℝ)) ∧
        (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  have hmem0 : DIntvProd.DIntv.memR (gLine (14 : ℝ)) (dK.boxes.get ⟨0, by decide⟩) := by
    show DIntvProd.DIntv.memR (gLine (14 : ℝ)) ⟨-68719476736, -1, -37⟩
    obtain ⟨h1, h2⟩ := KernelBandEnclosures.gLine14_encl
    unfold DIntvProd.DIntv.memR
    constructor <;> norm_num <;> linarith
  have hmem1 : DIntvProd.DIntv.memR (gLine (15 : ℝ)) (dK.boxes.get ⟨1, by decide⟩) := by
    show DIntvProd.DIntv.memR (gLine (15 : ℝ)) ⟨1, 549755813888, -37⟩
    obtain ⟨h1, h2⟩ := KernelBandEnclosures.gLine15_encl
    unfold DIntvProd.DIntv.memR
    constructor <;> norm_num <;> linarith
  have hmem2 : DIntvProd.DIntv.memR (gLine (22 : ℝ)) (dK.boxes.get ⟨2, by decide⟩) := by
    show DIntvProd.DIntv.memR (gLine (22 : ℝ)) ⟨-288230376151711744, -1, -55⟩
    obtain ⟨h1, h2⟩ := KernelBandEnclosures.gLine22_encl
    unfold DIntvProd.DIntv.memR
    constructor <;> norm_num <;> linarith
  refine checkLine_correct dK (14 : ℝ) (22 : ℝ) 2
    (by decide) ReflectedBand_t14.grid ?_ ?_ ?_ ?_ okK
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ReflectedBand_t14.grid] <;> norm_num
  · simp [ReflectedBand_t14.grid]
  · simp [ReflectedBand_t14.grid, Fin.last]
  · intro i
    fin_cases i
    · exact hmem0
    · exact hmem1
    · exact hmem2

end ReflectedBand_t14_Kernel
