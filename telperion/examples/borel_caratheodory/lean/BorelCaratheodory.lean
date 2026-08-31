/- THE BOREL–CARATHÉODORY THEOREM.

   If `f` is holomorphic on the open disk `ball 0 R` and continuous up to the boundary
   (`DiffContOnCl`), and its real part is bounded above by `A` on the boundary circle
   `sphere 0 R`, then `f` is quantitatively controlled inside a smaller disk `ball 0 r`,
   `r < R`, in terms of `A − Re (f 0)`:

     value form:       ‖f z − f 0‖ ≤ (2‖z‖ / (R − ‖z‖)) · (A − Re (f 0))         (‖z‖ < R)
     derivative form:  ‖deriv f z‖ ≤ (2R / (R − ‖z‖)²) · (A − Re (f 0))          (‖z‖ < R)

   This is the crux quantitative bound for the classical zeta zero-free region: it converts a
   ONE-SIDED bound on Re (log ζ) (available from a growth estimate on ζ) into a full bound on
   |ζ'/ζ|.  Mathlib v4.32.0 has the Schwarz lemma and Cauchy's derivative estimate but NOT
   Borel–Carathéodory itself; this file supplies it.  A certificate FEEDING the region, NOT the
   region and NOT a proof of RH.

   PROOF (Möbius–Schwarz).  Put `g = f − f 0` (so `g 0 = 0`), `B = A − Re (f 0)`.
   The maximum principle applied to `exp (g − B)` upgrades `Re g ≤ B` from the boundary to the
   whole disk (BC0).  The Möbius map `w = g / (2B − g)` then sends the disk into the unit disk
   (BC2/BC3), fixes 0, so Schwarz gives `‖w z‖ ≤ ‖z‖/R` (BC4); inverting the Möbius map
   (`g = 2B·w/(1+w)`) and using the reverse triangle inequality yields the value form (BC5/BC6).
   The derivative form is Cauchy's estimate on the subdisk `ball z (R−‖z‖)` (BC7).

   Status: best-effort DRAFT for CI iteration.  No `stub`, no `stub`. -/
import Mathlib

open scoped Real Topology
open Metric Set Complex

namespace BorelCaratheodory

/- ===================================================================================
   BC0.  MAXIMUM PRINCIPLE FOR THE REAL PART.
   If `g` is `DiffContOnCl` on `ball 0 R` and `Re (g ζ) ≤ B` for all `ζ` on the boundary
   circle, then `Re (g ζ) ≤ B` on the whole closed disk.  Proof: apply the maximum-modulus
   principle to `h ζ = exp (g ζ − B)`, whose norm is `exp (Re (g ζ) − B)`; the boundary bound
   gives `‖h‖ ≤ 1`, and monotonicity of `Real.exp` recovers the real-part inequality inside.
   =================================================================================== -/

/-- Upgrade a boundary bound on `Re g` to an interior bound, via `exp` + max modulus. -/
theorem re_le_on_closedBall_of_re_le_on_sphere
    {R B : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (ball 0 R))
    (hB : ∀ ζ ∈ sphere (0 : ℂ) R, (g ζ).re ≤ B)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    (g z).re ≤ B := by
  -- The auxiliary function `h ζ = exp (g ζ − B)`.
  set h : ℂ → ℂ := fun ζ => Complex.exp (g ζ - (B : ℂ)) with hh
  -- `h` is `DiffContOnCl` on the ball: `exp` is entire, precomposed with `g − const`.
  have hconst : DiffContOnCl ℂ (fun ζ : ℂ => g ζ - (B : ℂ)) (ball 0 R) := hg.sub_const (B : ℂ)
  have hdh : DiffContOnCl ℂ h (ball 0 R) :=
    Complex.differentiable_exp.comp_diffContOnCl hconst
  -- Norm bound on the frontier (= sphere).
  have hnorm_bound : ∀ ζ ∈ frontier (ball (0 : ℂ) R), ‖h ζ‖ ≤ 1 := by
    intro ζ hζ
    rw [frontier_ball 0 hR.ne'] at hζ
    have hle0 : (g ζ - (B : ℂ)).re ≤ 0 := by
      simp only [Complex.sub_re, Complex.ofReal_re]; linarith [hB ζ hζ]
    calc ‖h ζ‖ = Real.exp (g ζ - (B : ℂ)).re := by
            simp only [hh]; exact Complex.norm_exp _
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
      _ = 1 := Real.exp_zero
  -- Max modulus: the bound propagates to the closure (= closed ball).
  have hclosure : z ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne']; exact hz
  have hle : ‖h z‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdh hnorm_bound hclosure
  -- Recover `Re (g z) ≤ B` from `exp (Re (g z) − B) ≤ 1`.
  have hlz : Real.exp (g z - (B : ℂ)).re ≤ 1 := by
    have := hle; simp only [hh] at this; rwa [Complex.norm_exp] at this
  have hre : (g z - (B : ℂ)).re ≤ 0 := Real.exp_le_one_iff.mp hlz
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/- ===================================================================================
   BC2.  MÖBIUS SENDS A LEFT HALF-PLANE INTO THE UNIT DISK.
   For `0 < B` and `Re w ≤ B`, the point `w / (2B − w)` lies in the closed unit disk.
   The Positivstellensatz core: `‖w‖² ≤ ‖2B − w‖²` ⟺ `0 ≤ 4B(B − Re w)`, a product of
   nonnegatives.  (Telperion-certified as `4·(B − Re w)·B`.)
   =================================================================================== -/

/-- The denominator `2B − w` never vanishes when `Re w ≤ B` and `0 < B`. -/
theorem two_mul_sub_ne_zero {B : ℝ} (hB : 0 < B) {w : ℂ} (hw : w.re ≤ B) :
    (2 * (B : ℂ) - w) ≠ 0 := by
  intro hzero
  have hre : (2 * (B : ℂ) - w).re = 0 := by rw [hzero]; simp
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  nlinarith [hw, hB, hre]

/-- **Möbius into the unit disk.**  `Re w ≤ B`, `0 < B ⟹ ‖w / (2B − w)‖ ≤ 1`. -/
theorem norm_div_two_mul_sub_le_one {B : ℝ} (hB : 0 < B) {w : ℂ} (hw : w.re ≤ B) :
    ‖w / (2 * (B : ℂ) - w)‖ ≤ 1 := by
  have hden : (2 * (B : ℂ) - w) ≠ 0 := two_mul_sub_ne_zero hB hw
  have hpos : 0 < ‖2 * (B : ℂ) - w‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_le_one hpos]
  -- Reduce `‖w‖ ≤ ‖2B − w‖` to `‖w‖² ≤ ‖2B − w‖²` (both sides nonneg).
  have hsq : ‖w‖ ^ 2 ≤ ‖2 * (B : ℂ) - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
    -- Goal reduces to `0 ≤ 4B(B − Re w)` after ring normalization.
    nlinarith [hw, hB, sq_nonneg w.im, sq_nonneg w.re, mul_nonneg hB.le (sub_nonneg.mpr hw)]
  have hnn₁ : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [hsq, hnn₁, hpos.le]

/- ===================================================================================
   BC3.  THE MÖBIUS FUNCTION `w = g / (2B − g)` IS DIFFERENTIABLE ON THE DISK, FIXES 0,
   AND MAPS `ball 0 R → closedBall 0 1`.
   =================================================================================== -/

/-- The Möbius transform of `g` (with respect to bound `B`). -/
noncomputable def moebius (B : ℝ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun ζ => g ζ / (2 * (B : ℂ) - g ζ)

/-- `moebius B g 0 = 0` when `g 0 = 0`. -/
theorem moebius_zero (B : ℝ) {g : ℂ → ℂ} (hg0 : g 0 = 0) : moebius B g 0 = 0 := by
  simp [moebius, hg0]

/-- `moebius B g` is differentiable on the open ball, given `g` differentiable and the
    half-plane bound `Re (g ζ) ≤ B` (which keeps the denominator nonzero). -/
theorem moebius_differentiableOn {R B : ℝ} (hB : 0 < B) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hre : ∀ ζ ∈ ball (0 : ℂ) R, (g ζ).re ≤ B) :
    DifferentiableOn ℂ (moebius B g) (ball 0 R) := by
  have hden : ∀ ζ ∈ ball (0 : ℂ) R, (2 * (B : ℂ) - g ζ) ≠ 0 :=
    fun ζ hζ => two_mul_sub_ne_zero hB (hre ζ hζ)
  simp only [moebius]
  exact DifferentiableOn.div hg ((differentiableOn_const _).sub hg) hden

/-- `moebius B g` maps `ball 0 R` into `closedBall 0 1`, given the half-plane bound. -/
theorem moebius_mapsTo {R B : ℝ} (hB : 0 < B) {g : ℂ → ℂ}
    (hre : ∀ ζ ∈ ball (0 : ℂ) R, (g ζ).re ≤ B) :
    Set.MapsTo (moebius B g) (ball 0 R) (closedBall 0 1) := by
  intro ζ hζ
  rw [mem_closedBall, dist_zero_right]
  show ‖g ζ / (2 * (B : ℂ) - g ζ)‖ ≤ 1
  exact norm_div_two_mul_sub_le_one hB (hre ζ hζ)

/- ===================================================================================
   BC4.  SCHWARZ ON THE MÖBIUS FUNCTION.
   `w = moebius B g` fixes 0 and maps `ball 0 R → closedBall 0 1`, so the ratio-form Schwarz
   lemma gives `‖w z‖ ≤ (1/R)·‖z‖`.

   STRICTNESS NOTE.  BC2 only gives the NON-STRICT `‖w‖ ≤ 1` (equality is possible in principle,
   iff Re g = A).  We therefore use `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, whose hypothesis
   is `MapsTo w (ball 0 R) (closedBall (w 0) 1)` — the CLOSED target ball — so the non-strict
   bound is exactly what it consumes.  We deliberately do NOT route through
   `Complex.norm_le_norm_of_mapsTo_ball`, which requires the OPEN target ball `ball 0 1` (strict
   `‖w z‖ < 1`); that would force an extra maximum-modulus argument (`‖w‖=1` interior ⟹ `w` const
   ⟹ `w≡0`, contradiction) to upgrade `≤` to `<`.  The ratio-form closed-ball variant makes that
   step unnecessary here.
   =================================================================================== -/

/-- Schwarz bound on the Möbius transform: `‖w z‖ ≤ ‖z‖ / R`. -/
theorem moebius_schwarz {R B : ℝ} (hB : 0 < B) {g : ℂ → ℂ} (hg0 : g 0 = 0)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hre : ∀ ζ ∈ ball (0 : ℂ) R, (g ζ).re ≤ B)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ‖moebius B g z‖ ≤ ‖z‖ / R := by
  have hdiff : DifferentiableOn ℂ (moebius B g) (ball 0 R) :=
    moebius_differentiableOn hB hg hre
  have hmaps : Set.MapsTo (moebius B g) (ball 0 R) (closedBall (moebius B g 0) 1) := by
    rw [moebius_zero B hg0]; exact moebius_mapsTo hB hre
  -- Schwarz (ratio form): dist (w z) (w 0) ≤ (1/R) * dist z 0.
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps hz
  rw [moebius_zero B hg0] at hschwarz
  simpa [dist_zero_right, div_eq_inv_mul, mul_comm] using hschwarz

/- ===================================================================================
   BC5.  INVERSION OF THE MÖBIUS MAP + REVERSE TRIANGLE INEQUALITY.
   With `w = moebius B g ζ`, we have algebraically `g ζ = 2B·w / (1 + w)`.  Given `‖w‖ ≤ t`
   with `t < 1`, the reverse triangle inequality `‖1 + w‖ ≥ 1 − ‖w‖ ≥ 1 − t > 0` yields
   `‖g ζ‖ ≤ 2B·t / (1 − t)`.
   =================================================================================== -/

/-- Algebraic inversion identity: `w = g/(2B−g)` ⟹ `g = 2B·w/(1+w)` with `1 + w ≠ 0`,
    assuming `0 < B` and the denominator `2B − g` nonzero. -/
theorem moebius_inv {B : ℝ} (hB : 0 < B) {g w : ℂ}
    (hden : (2 * (B : ℂ) - g) ≠ 0)
    (hw : w = g / (2 * (B : ℂ) - g)) :
    (1 + w) ≠ 0 ∧ g = 2 * (B : ℂ) * w / (1 + w) := by
  have hBne : (2 * (B : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast hB.ne'
  subst hw
  -- `1 + g/(2B−g) = 2B/(2B−g)`, whose numerator `2B ≠ 0` gives `1 + w ≠ 0`.
  have h1w : (1 : ℂ) + g / (2 * (B : ℂ) - g) = 2 * (B : ℂ) / (2 * (B : ℂ) - g) := by
    field_simp
  have h1wne : (1 + g / (2 * (B : ℂ) - g)) ≠ 0 := by
    rw [h1w]; exact div_ne_zero hBne hden
  refine ⟨h1wne, ?_⟩
  -- Prove `g = 2B·w/(1+w)` by clearing the (nonzero) denominator `1 + w`.
  rw [eq_div_iff h1wne]
  field_simp
  ring

/-- Norm bound from Schwarz + inversion: if `‖w‖ ≤ t < 1` and `g = 2B·w/(1+w)`, then
    `‖g‖ ≤ 2B·t/(1−t)`. -/
theorem norm_g_le_of_norm_w_le {B t : ℝ} (hB : 0 < B) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {g w : ℂ} (hwt : ‖w‖ ≤ t) (h1w : (1 + w) ≠ 0)
    (hg : g = 2 * (B : ℂ) * w / (1 + w)) :
    ‖g‖ ≤ 2 * B * t / (1 - t) := by
  have hden_pos : 0 < ‖1 + w‖ := norm_pos_iff.mpr h1w
  -- Reverse triangle: ‖1 + w‖ ≥ 1 − ‖w‖ ≥ 1 − t > 0.
  have hrev : (1 : ℝ) - ‖w‖ ≤ ‖1 + w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    -- this : 1 - ‖w‖ ≤ ‖1 + w‖  (after `1 - (- w) = 1 + w`)
    simpa [sub_neg_eq_add] using this
  have h1mt_pos : 0 < 1 - t := by linarith
  have hlb : (1 : ℝ) - t ≤ ‖1 + w‖ := by linarith [hrev, hwt]
  -- Numerator norm: ‖2·B·w‖ = 2·B·‖w‖  (B > 0, so ‖(B:ℂ)‖ = |B| = B; ‖(2:ℂ)‖ = 2).
  have hnum : ‖2 * (B : ℂ) * w‖ = 2 * B * ‖w‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB,
      Complex.norm_ofNat]
  rw [hg, norm_div, hnum]
  -- 2B‖w‖ / ‖1+w‖ ≤ 2B·t / (1−t).
  rw [div_le_div_iff₀ hden_pos h1mt_pos]
  have hlhs : 2 * B * ‖w‖ * (1 - t) ≤ 2 * B * t * ‖1 + w‖ := by
    have hBt : (0 : ℝ) ≤ 2 * B := by positivity
    nlinarith [hwt, hlb, ht0, hden_pos.le, mul_nonneg hBt ht0, hB.le]
  linarith [hlhs]

/- ===================================================================================
   BC6.  VALUE FORM (main theorem).
   Assemble BC0, BC4, BC5 for `g = f − f 0`, `B = A − Re (f 0)`.  We assume the nondegeneracy
   `0 < A − Re (f 0)` (the degenerate case `A = Re (f 0)` forces `f` constant, a separate,
   easy branch not needed for the zero-free application).
   =================================================================================== -/

/-- **Borel–Carathéodory, value form.**  `f` holomorphic on `ball 0 R`, continuous up to the
    boundary, with `Re (f ζ) ≤ A` on `sphere 0 R` and `Re (f 0) < A`.  Then for `‖z‖ < R`:
    `‖f z − f 0‖ ≤ (2‖z‖ / (R − ‖z‖)) · (A − Re (f 0))`. -/
theorem borel_caratheodory_value
    {R A : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hA : ∀ ζ ∈ sphere (0 : ℂ) R, (f ζ).re ≤ A)
    (hf0 : (f 0).re < A)
    {z : ℂ} (hz : ‖z‖ < R) :
    ‖f z - f 0‖ ≤ (2 * ‖z‖ / (R - ‖z‖)) * (A - (f 0).re) := by
  -- Notation.
  set B : ℝ := A - (f 0).re with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  set g : ℂ → ℂ := fun ζ => f ζ - f 0 with hgdef
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; exact hz
  -- `g` is DiffContOnCl and differentiable on the ball.
  have hg_dcc : DiffContOnCl ℂ g (ball 0 R) := hf.sub_const (f 0)
  have hg_diff : DifferentiableOn ℂ g (ball 0 R) := hg_dcc.differentiableOn
  -- Boundary bound on Re g: `Re (g ζ) = Re (f ζ) − Re (f 0) ≤ A − Re (f 0) = B`.
  have hBsphere : ∀ ζ ∈ sphere (0 : ℂ) R, (g ζ).re ≤ B := by
    intro ζ hζ
    simp only [hgdef, Complex.sub_re]
    have := hA ζ hζ; rw [hBdef]; linarith
  -- Interior bound on Re g (BC0), on the ball (⊆ closed ball).
  have hBball : ∀ ζ ∈ ball (0 : ℂ) R, (g ζ).re ≤ B := by
    intro ζ hζ
    exact re_le_on_closedBall_of_re_le_on_sphere hR hg_dcc hBsphere (ball_subset_closedBall hζ)
  -- BC4: Schwarz bound on the Möbius transform.
  have hschwarz : ‖moebius B g z‖ ≤ ‖z‖ / R :=
    moebius_schwarz hB hg0 hg_diff hBball hzball
  -- BC5: invert.
  have hden : (2 * (B : ℂ) - g z) ≠ 0 := two_mul_sub_ne_zero hB (hBball z hzball)
  obtain ⟨h1w, hginv⟩ := moebius_inv hB hden (rfl : moebius B g z = g z / (2 * (B : ℂ) - g z))
  -- t := ‖z‖ / R < 1.
  set t : ℝ := ‖z‖ / R with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have ht1 : t < 1 := by rw [htdef, div_lt_one hR]; exact hz
  have hgbound : ‖g z‖ ≤ 2 * B * t / (1 - t) :=
    norm_g_le_of_norm_w_le hB ht0 ht1 hschwarz h1w hginv
  -- Rewrite `2B·t/(1−t)` as `(2‖z‖/(R−‖z‖))·B`.
  have hRmz_pos : 0 < R - ‖z‖ := by linarith
  have hRne : R ≠ 0 := hR.ne'
  have hRmz_ne : R - ‖z‖ ≠ 0 := hRmz_pos.ne'
  -- `1 − t > 0` (from `t < 1`), hence `≠ 0`.
  have h1t_ne : (1 : ℝ) - t ≠ 0 := (sub_pos.mpr ht1).ne'
  have hrewrite : 2 * B * t / (1 - t) = (2 * ‖z‖ / (R - ‖z‖)) * B := by
    rw [htdef]
    field_simp
    ring
  rw [hrewrite] at hgbound
  -- Finish: `‖f z − f 0‖ = ‖g z‖` and reorder.
  have : ‖f z - f 0‖ = ‖g z‖ := by rw [hgdef]
  rw [this]
  calc ‖g z‖ ≤ (2 * ‖z‖ / (R - ‖z‖)) * B := hgbound
    _ = (2 * ‖z‖ / (R - ‖z‖)) * (A - (f 0).re) := by rw [hBdef]

/- ===================================================================================
   BC7.  DERIVATIVE FORM (Cauchy's estimate).

   MATHEMATICAL NOTE.  The literature's SHARP derivative constant is `2R/(R−r)²` (case
   `f 0 = 0`; see the search sources cited in the return message).  Its proof requires a
   Poisson-kernel / mean-value refinement: the crude majorant `sup_{sphere} ‖g‖` obtained from
   the value form BLOWS UP at the boundary (`R − ‖ζ‖ → 0` as `‖ζ‖ → R`), so Cauchy's estimate
   against that sup does NOT recover `2R/(R−r)²`.  Rather than fabricate that constant, we prove
   the honest bound that Cauchy + the value form actually deliver: a family bound at every inner
   radius `0 < ρ' < R − ‖z‖`, and a clean closed form at `ρ' = (R − ‖z‖)/2`,

     ‖deriv f z‖ ≤ (4 (R + ‖z‖) / (R − ‖z‖)²) · (A − Re (f 0)).

   Since `R + ‖z‖ < 2R`, this is `≤ (8R/(R−‖z‖)²)·(A − Re (f 0))` — same shape as the sharp
   bound, off only by a constant factor.  Achieving the sharp `2R` is flagged as the top
   CI-iteration target (needs `MeanValue`/Poisson machinery).
   =================================================================================== -/

/-- Cauchy family bound: for every inner radius `0 < ρ' < R − ‖z‖`,
    `‖deriv f z‖ ≤ (2(‖z‖+ρ') / (ρ'·(R − ‖z‖ − ρ'))) · (A − Re (f 0))`. -/
theorem borel_caratheodory_deriv_family
    {R A : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hA : ∀ ζ ∈ sphere (0 : ℂ) R, (f ζ).re ≤ A)
    (hf0 : (f 0).re < A)
    {z : ℂ} (hz : ‖z‖ < R)
    {ρ' : ℝ} (hρ'0 : 0 < ρ') (hρ'lt : ρ' < R - ‖z‖) :
    ‖deriv f z‖ ≤ (2 * (‖z‖ + ρ') / (R - (‖z‖ + ρ'))) * (A - (f 0).re) / ρ' := by
  have hB : 0 < A - (f 0).re := by linarith
  have hRmz_pos : 0 < R - ‖z‖ := by linarith
  have hRzρ_pos : 0 < R - (‖z‖ + ρ') := by linarith
  -- deriv of `f` equals deriv of `g = f − f 0`.
  have hderiv_eq : deriv f z = deriv (fun ζ => f ζ - f 0) z := (deriv_sub_const _).symm
  -- The closed subball sits inside `ball 0 R`.
  have hsub : closedBall z ρ' ⊆ ball (0 : ℂ) R := by
    intro ζ hζ
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hζ
    calc ‖ζ‖ ≤ ‖z‖ + ‖ζ - z‖ := by simpa using norm_le_norm_add_norm_sub' ζ z
      _ ≤ ‖z‖ + ρ' := by linarith [hζ]
      _ < R := by linarith
  -- `f` is DiffContOnCl on the open subball (differentiable there + continuous on closure).
  have hf_sub : DiffContOnCl ℂ f (ball z ρ') := by
    refine DiffContOnCl.mk_ball ?_ ?_
    · -- differentiable on the open subball ⊆ ball 0 R
      exact hf.differentiableOn.mono (fun ζ hζ => hsub (ball_subset_closedBall hζ))
    · -- continuous on the closed subball ⊆ closure (ball 0 R)
      refine hf.continuousOn.mono (fun ζ hζ => ?_)
      -- hζ : ζ ∈ closedBall z ρ';  hsub hζ : ζ ∈ ball 0 R ⊆ closure (ball 0 R)
      exact subset_closure (hsub hζ)
  -- Boundary bound on `sphere z ρ'` via BC6 + monotone majorization.  Stated directly in terms
  -- of `A - (f 0).re` (avoiding the `set B` abbreviation inside the ∀-bound to keep `rw`s robust).
  have hbdry : ∀ ζ ∈ sphere z ρ',
      ‖(fun ζ => f ζ - f 0) ζ‖ ≤ (2 * (‖z‖ + ρ') / (R - (‖z‖ + ρ'))) * (A - (f 0).re) := by
    intro ζ hζ
    rw [mem_sphere_iff_norm] at hζ  -- `‖ζ − z‖ = ρ'`   [FLAG: mem_sphere_iff_norm]
    have hζub : ‖ζ‖ ≤ ‖z‖ + ρ' := by
      calc ‖ζ‖ ≤ ‖z‖ + ‖ζ - z‖ := by simpa using norm_le_norm_add_norm_sub' ζ z
        _ = ‖z‖ + ρ' := by rw [hζ]
    have hζR : ‖ζ‖ < R := lt_of_le_of_lt hζub (by linarith)
    have hval := borel_caratheodory_value hR hf hA hf0 hζR
    simp only at hval ⊢
    refine hval.trans ?_
    have hRζ_pos : 0 < R - ‖ζ‖ := by linarith
    have hmono : 2 * ‖ζ‖ / (R - ‖ζ‖) ≤ 2 * (‖z‖ + ρ') / (R - (‖z‖ + ρ')) := by
      rw [div_le_div_iff₀ hRζ_pos hRzρ_pos]
      nlinarith [norm_nonneg ζ, hζub, hRζ_pos, hRzρ_pos, hRmz_pos]
    exact mul_le_mul_of_nonneg_right hmono hB.le
  -- Cauchy's estimate on `g = f − f 0`.
  have hcauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ'0 (hf_sub.sub_const (f 0)) hbdry
  rw [← hderiv_eq] at hcauchy
  -- Rearrange `C / ρ'`.
  rw [le_div_iff₀ hρ'0]; exact hcauchy

/-- **Borel–Carathéodory, derivative form** (clean closed constant, `ρ' = (R−‖z‖)/2`).
    For `‖z‖ < R`:
    `‖deriv f z‖ ≤ (4(R + ‖z‖) / (R − ‖z‖)²) · (A − Re (f 0))`.

    This is the honest constant delivered by Cauchy's estimate against the value form.  It is
    `≤ (8R/(R−‖z‖)²)·(A − Re (f 0))`, matching the literature's SHARP `2R/(R−‖z‖)²` up to a
    constant factor.  The sharp factor needs Poisson/mean-value refinement (top risk item). -/
theorem borel_caratheodory_deriv
    {R A : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hA : ∀ ζ ∈ sphere (0 : ℂ) R, (f ζ).re ≤ A)
    (hf0 : (f 0).re < A)
    {z : ℂ} (hz : ‖z‖ < R) :
    ‖deriv f z‖ ≤ (4 * (R + ‖z‖) / (R - ‖z‖) ^ 2) * (A - (f 0).re) := by
  have hRmz_pos : 0 < R - ‖z‖ := by linarith
  have hB : 0 ≤ A - (f 0).re := by linarith
  set ρ' : ℝ := (R - ‖z‖) / 2 with hρ'def
  have hρ'0 : 0 < ρ' := by rw [hρ'def]; positivity
  have hρ'lt : ρ' < R - ‖z‖ := by rw [hρ'def]; linarith
  have hfam := borel_caratheodory_deriv_family hR hf hA hf0 hz hρ'0 hρ'lt
  -- Simplify the family bound at `ρ' = (R−‖z‖)/2`.
  -- `‖z‖ + ρ' = (R + ‖z‖)/2`,  `R − (‖z‖+ρ') = (R − ‖z‖)/2`,  divide by `ρ' = (R−‖z‖)/2`.
  have hRzρ_pos : 0 < R - (‖z‖ + ρ') := by rw [hρ'def]; linarith
  have hRmz_ne : R - ‖z‖ ≠ 0 := hRmz_pos.ne'
  have hsimp :
      (2 * (‖z‖ + ρ') / (R - (‖z‖ + ρ'))) * (A - (f 0).re) / ρ'
        = (4 * (R + ‖z‖) / (R - ‖z‖) ^ 2) * (A - (f 0).re) := by
    rw [hρ'def]
    rw [show R - (‖z‖ + (R - ‖z‖) / 2) = (R - ‖z‖) / 2 by ring]
    field_simp
    ring
  rw [hsimp] at hfam
  exact hfam

end BorelCaratheodory
