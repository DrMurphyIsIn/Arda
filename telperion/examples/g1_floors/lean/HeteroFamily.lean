import Mathlib
import HomogMasterAssembled

/-!
# Heterogeneous canonical-family cell (the interior `nu`-cell)

Companion to the "#37 scoped route"
(`proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md`) and the vertex lemma
`R3Cert/VertexLemmaFull.lean`.  The scoping route collapses the FULL heterogeneous
achievable master problem to the 2-integer + 1-real canonical family

    fam(a, b, nu) = base(a+b+1, a*knee + b/2 + nu)^11 * glemma(1/2)^b * glemma(nu)

with `knee = 37/120` (the kernel region split), `nu ∈ [knee, 1/2]`, `a` below-knee
children (Bcap = 1, only their mass enters through `base`), `b` children at the
bound `1/2`, and one interior child at `nu`.

This file lands the **interior `nu`-cell** rigorously and kernel-clean: the
sub-family `fam(0, 0, nu) ≤ T` for `nu ∈ [knee, 1/2]`, which is exactly the
homogeneous `k = 1` value `base(1, nu)^11 * glemma(nu)` and is discharged by the
already-green Bernstein bridges `HomogMasterAssembled.bridgeB` (`[37/120, 1/3]`) and
`bridgeC1` (`[1/3, 1/2]`).  The empirical family maximum (see
`proof/verification/hetero_family_scan.py`) is exactly this cell:
`0.872204*T` at `(a,b,nu) = (0,0,1/2)`.

The integer tails (`a`, `b`) are geometrically/monotonically dominated by this cell
(the scan confirms `fam(a+1,b,nu) ≤ fam(a,b,nu)` and `fam(a,b+1,nu) ≤ fam(a,b,nu)`),
but their kernel-level closure couples the arity `j` and the sum `S` in the `base`
ratio and is left as a scoped-open obligation (see the module docstring notes).
`conjecture1_proved = False`.
-/

namespace HeteroFamily

open HomogMasterAssembled

/-- The kernel region-split knee (rational relaxation of the true `glemma = 1` knee). -/
def knee : ℚ := 37 / 120

/-- `base_het j S = (3(j+1) + 3 S + 1) / (3(j+1))` — the g-step base at arity `j`,
    message sum `S` (matches `hetero_family_scan.base_het`). -/
def base_het (j : ℕ) (S : ℚ) : ℚ :=
  (3 * ((j : ℚ) + 1) + 3 * S + 1) / (3 * ((j : ℚ) + 1))

/-- The canonical family value `fam(a,b,nu)` (matches `hetero_family_scan.GS_family`). -/
def fam (a b : ℕ) (nu : ℚ) : ℚ :=
  base_het (a + b + 1) ((a : ℚ) * knee + (b : ℚ) * (1/2) + nu) ^ 11
    * glemma (1/2) ^ b * glemma nu

/-- `base_het 1 nu = 7/6 + nu/2 = HomogMasterAssembled.base 1 nu`. -/
theorem base_het_one (nu : ℚ) : base_het 1 nu = 7 / 6 + nu / 2 := by
  unfold base_het; norm_num; ring

/-- **The interior `nu`-cell (`a = b = 0`).**  `fam 0 0 nu = (7/6 + nu/2)^11 * glemma nu`,
    the homogeneous `k = 1` value. -/
theorem fam_zero_zero (nu : ℚ) :
    fam 0 0 nu = (7 / 6 + nu / 2) ^ 11 * glemma nu := by
  unfold fam
  simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, mul_one]
  rw [base_het_one]

/-- **`nu`-cell certification, lower interval `[37/120, 1/3]`.**  `fam 0 0 nu ≤ T`
    via the Bernstein bridge `bridgeB`. -/
theorem nu_cell_B (nu : ℚ) (h0 : 37 / 120 ≤ nu) (h1 : nu ≤ 1 / 3) :
    fam 0 0 nu ≤ T := by
  rw [fam_zero_zero]
  have hB := bridgeB nu h0 h1
  rw [pow_one] at hB
  exact hB

/-- **`nu`-cell certification, upper interval `[1/3, 1/2]`.**  `fam 0 0 nu ≤ T`
    via the Bernstein bridge `bridgeC1`. -/
theorem nu_cell_C (nu : ℚ) (h0 : 1 / 3 ≤ nu) (h1 : nu ≤ 1 / 2) :
    fam 0 0 nu ≤ T := by
  rw [fam_zero_zero]
  have hC := bridgeC1 nu h0 h1
  rw [pow_one] at hC
  exact hC

/-- **The interior `nu`-cell (assembled).**  For every `nu ∈ [knee, 1/2]`,
    `fam 0 0 nu ≤ T`.  This is the empirical family maximum
    (`0.872204*T` at `nu = 1/2`), certified kernel-clean by reusing the homogeneous
    Bernstein cells over the two sub-intervals `[37/120, 1/3]` and `[1/3, 1/2]`. -/
theorem nu_cell (nu : ℚ) (h0 : knee ≤ nu) (h1 : nu ≤ 1 / 2) :
    fam 0 0 nu ≤ T := by
  unfold knee at h0
  rcases le_total nu (1 / 3) with hB | hC
  · exact nu_cell_B nu h0 hB
  · exact nu_cell_C nu hC h1

/-- **Tightness witness.**  `fam 0 0 (1/2) = HomogMasterAssembled.GS 1 (1/2)` — the
    interior `nu`-cell's peak equals the homogeneous `k = 1`, `mu = 1/2` value
    (`= 0.872204*T`, the family max in the scan). -/
theorem fam_peak_eq_GS1 : fam 0 0 (1/2) = GS 1 (1/2) := by
  rw [fam_zero_zero]
  unfold GS Bcap master_ub glemma base GAMMA W
  norm_num [min_def]

/-! ## The integer tails: monotone reductions `a → 0` and `b → 0`

Both `a` (below-knee children) and `b` (children at the bound `1/2`) are monotone
tails: adding one never increases the family value.  Each reduction is a `base`-ratio
inequality with an ALL-NONNEGATIVE-COEFFICIENT numerator after substituting
`nu = knee + t` (`t ≥ 0`), so it closes by `positivity`/`nlinarith` with no `nlinarith`
timeout on the huge `T` constant (the `glemma` factor enters only through the exact
rational bound `R^11 · glemma(1/2) ≤ 1`). -/

/-- The `b`-step ratio bound constant: `R = 994/951`, with `R^11 · glemma(1/2) ≤ 1`. -/
def Rb : ℚ := 994 / 951

/-- `0 ≤ base_het j S` for `0 ≤ S`. -/
theorem base_het_nonneg (j : ℕ) (S : ℚ) (hS : 0 ≤ S) : 0 ≤ base_het j S := by
  unfold base_het
  have hden : (0:ℚ) < 3 * ((j:ℚ) + 1) := by positivity
  apply div_nonneg _ (le_of_lt hden)
  have : (0:ℚ) ≤ (j:ℚ) := by positivity
  linarith

/-- `glemma (1/2) ≥ 0`. -/
theorem glemma_half_nonneg : 0 ≤ glemma (1/2) := by
  unfold glemma GAMMA W; norm_num

/-- `glemma nu ≥ 0` for `nu ≥ 0`. -/
theorem glemma_nonneg' (nu : ℚ) (h : 0 ≤ nu) : 0 ≤ glemma nu := by
  unfold glemma GAMMA W
  have : (0:ℚ) < 1 + nu / 3 := by linarith
  positivity

/-- **`a`-step base inequality.**  For `a, b : ℕ` and `nu ≥ knee`,
    `base_het (a+b+2) (a·knee + b/2 + nu + knee) ≤ base_het (a+b+1) (a·knee + b/2 + nu)`.
    (Adding a below-knee child raises arity and sum by `(1, knee)`; `base` decreases.)
    Numerator after `nu = knee + t`: `23 b + 120 t + 3 ≥ 0`. -/
theorem astep_base (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee)
      ≤ base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) := by
  unfold base_het knee
  have ha : (0:ℚ) ≤ (a:ℚ) := by positivity
  have hb : (0:ℚ) ≤ (b:ℚ) := by positivity
  have ht : (0:ℚ) ≤ nu - 37/120 := by rw [knee] at hnu; linarith
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [ha, hb, ht, mul_nonneg ha hb, mul_nonneg ha ht, mul_nonneg hb ht]

/-- **`b`-step base-ratio inequality.**  For `a, b : ℕ` and `nu ≥ knee`,
    `base_het (a+b+2) (a·knee + b/2 + nu + 1/2) ≤ Rb · base_het (a+b+1) (a·knee + b/2 + nu)`.
    Numerator after `nu = knee + t`: an all-nonnegative-coefficient polynomial `≥ 0`. -/
theorem bstep_base (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + 1/2)
      ≤ Rb * base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) := by
  have ha : (0:ℚ) ≤ (a:ℚ) := by positivity
  have hb : (0:ℚ) ≤ (b:ℚ) := by positivity
  have ht : (0:ℚ) ≤ nu - 37/120 := by rw [knee] at hnu; linarith
  set N2 : ℚ := 3 * (((a + b + 2 : ℕ):ℚ) + 1) + 3 * ((a:ℚ) * (37/120) + (b:ℚ) * (1/2) + nu + 1/2) + 1
    with hN2
  set D2 : ℚ := 3 * (((a + b + 2 : ℕ):ℚ) + 1) with hD2
  set N1 : ℚ := 3 * (((a + b + 1 : ℕ):ℚ) + 1) + 3 * ((a:ℚ) * (37/120) + (b:ℚ) * (1/2) + nu) + 1
    with hN1
  set D1 : ℚ := 3 * (((a + b + 1 : ℕ):ℚ) + 1) with hD1
  have hd2 : (0:ℚ) < D2 := by rw [hD2]; positivity
  have hd1 : (0:ℚ) < D1 := by rw [hD1]; positivity
  show N2 / D2 ≤ 994 / 951 * (N1 / D1)
  -- rewrite RHS as a single fraction (994·N1)/(951·D1)
  have hrhs : (994 / 951 : ℚ) * (N1 / D1) = (994 * N1) / (951 * D1) := by
    field_simp
  rw [hrhs, div_le_div_iff₀ hd2 (by positivity)]
  -- cross-multiplied: N2 · (951 · D1) ≤ (994 · N1) · D2
  rw [hN2, hN1, hD2, hD1]
  push_cast
  nlinarith [ha, hb, ht, mul_nonneg ha hb, mul_nonneg ha ht, mul_nonneg hb ht,
    mul_nonneg ha ha, mul_nonneg hb hb]


/-- **`R^11 · glemma(1/2) ≤ 1`** (exact rational, the `b`-step's `glemma` accounting). -/
theorem Rb_pow_glemma_half : Rb ^ 11 * glemma (1/2) ≤ 1 := by
  unfold Rb glemma GAMMA W; norm_num

/-- **`a`-step reduction.**  `fam (a+1) b nu ≤ fam a b nu` for `nu ≥ knee`. -/
theorem astep (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    fam (a + 1) b nu ≤ fam a b nu := by
  unfold fam
  have hknee : (0:ℚ) ≤ knee := by unfold knee; norm_num
  have hnu0 : (0:ℚ) ≤ nu := le_trans hknee hnu
  -- the sum arg of fam (a+1) b nu is (a*knee + b/2 + nu) + knee
  have harg : ((a + 1 : ℕ):ℚ) * knee + (b:ℚ) * (1/2) + nu
      = (a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee := by push_cast; ring
  have harith : (a + 1 + b + 1 : ℕ) = a + b + 2 := by ring
  rw [harg, harith]
  have hS0 : (0:ℚ) ≤ (a:ℚ) * knee + (b:ℚ) * (1/2) + nu := by positivity
  have hbase_lo : 0 ≤ base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee) :=
    base_het_nonneg _ _ (by positivity)
  have hbase_hi : 0 ≤ base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) :=
    base_het_nonneg _ _ hS0
  have hbstep := astep_base a b nu hnu
  have hpow : base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee) ^ 11
      ≤ base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) ^ 11 := by
    gcongr
  -- glemma factors identical on both sides
  have hgl : 0 ≤ glemma (1/2) ^ b * glemma nu :=
    mul_nonneg (pow_nonneg glemma_half_nonneg b) (glemma_nonneg' nu hnu0)
  calc base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee) ^ 11
          * glemma (1/2) ^ b * glemma nu
      = base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + knee) ^ 11
          * (glemma (1/2) ^ b * glemma nu) := by ring
    _ ≤ base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) ^ 11
          * (glemma (1/2) ^ b * glemma nu) := by
        apply mul_le_mul_of_nonneg_right hpow hgl
    _ = base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) ^ 11
          * glemma (1/2) ^ b * glemma nu := by ring

/-- **`b`-step reduction.**  `fam a (b+1) nu ≤ fam a b nu` for `nu ≥ knee`.
    Uses `base(...+1/2)^11 · glemma(1/2) ≤ Rb^11 · base(...)^11 · glemma(1/2)
    ≤ base(...)^11` via `bstep_base` and `Rb_pow_glemma_half`. -/
theorem bstep (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    fam a (b + 1) nu ≤ fam a b nu := by
  unfold fam
  have hknee : (0:ℚ) ≤ knee := by unfold knee; norm_num
  have hnu0 : (0:ℚ) ≤ nu := le_trans hknee hnu
  have hS0 : (0:ℚ) ≤ (a:ℚ) * knee + (b:ℚ) * (1/2) + nu := by positivity
  -- sum/arity of fam a (b+1) nu
  have harg : ((a:ℚ) * knee + ((b + 1 : ℕ):ℚ) * (1/2) + nu)
      = (a:ℚ) * knee + (b:ℚ) * (1/2) + nu + 1/2 := by push_cast; ring
  have harith : (a + (b + 1) + 1 : ℕ) = a + b + 2 := by ring
  rw [harg, harith]
  -- abbreviations
  set B2 := base_het (a + b + 2) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu + 1/2) with hB2
  set B1 := base_het (a + b + 1) ((a:ℚ) * knee + (b:ℚ) * (1/2) + nu) with hB1
  have hB2nn : 0 ≤ B2 := base_het_nonneg _ _ (by positivity)
  have hB1nn : 0 ≤ B1 := base_het_nonneg _ _ hS0
  have hglh : 0 ≤ glemma (1/2) := glemma_half_nonneg
  have hgln : 0 ≤ glemma nu := glemma_nonneg' nu hnu0
  have hglb : 0 ≤ glemma (1/2) ^ b := pow_nonneg hglh b
  -- base-ratio bound: B2 ≤ Rb · B1, so B2^11 ≤ Rb^11 · B1^11
  have hbr := bstep_base a b nu hnu
  rw [← hB2, ← hB1] at hbr
  have hRbnn : (0:ℚ) ≤ Rb := by unfold Rb; norm_num
  have hpow : B2 ^ 11 ≤ (Rb * B1) ^ 11 := by gcongr
  have hpow' : B2 ^ 11 ≤ Rb ^ 11 * B1 ^ 11 := by rw [mul_pow] at hpow; exact hpow
  -- goal: B2^11 · glemma(1/2)^(b+1) · glemma nu ≤ B1^11 · glemma(1/2)^b · glemma nu
  -- LHS = (B2^11 · glemma(1/2)) · glemma(1/2)^b · glemma nu
  --     ≤ (Rb^11 · B1^11 · glemma(1/2)) · glemma(1/2)^b · glemma nu
  --     ≤ B1^11 · glemma(1/2)^b · glemma nu    (Rb^11 · glemma(1/2) ≤ 1)
  have hRg := Rb_pow_glemma_half
  have hkey : B2 ^ 11 * glemma (1/2) ≤ B1 ^ 11 := by
    calc B2 ^ 11 * glemma (1/2)
        ≤ (Rb ^ 11 * B1 ^ 11) * glemma (1/2) := by
          apply mul_le_mul_of_nonneg_right hpow' hglh
      _ = B1 ^ 11 * (Rb ^ 11 * glemma (1/2)) := by ring
      _ ≤ B1 ^ 11 * 1 := by
          apply mul_le_mul_of_nonneg_left hRg (pow_nonneg hB1nn 11)
      _ = B1 ^ 11 := by ring
  calc B2 ^ 11 * glemma (1/2) ^ (b + 1) * glemma nu
      = (B2 ^ 11 * glemma (1/2)) * (glemma (1/2) ^ b * glemma nu) := by
        rw [pow_succ]; ring
    _ ≤ B1 ^ 11 * (glemma (1/2) ^ b * glemma nu) := by
        apply mul_le_mul_of_nonneg_right hkey (mul_nonneg hglb hgln)
    _ = B1 ^ 11 * glemma (1/2) ^ b * glemma nu := by ring

/-- Reduce `b` to `0`: `fam a b nu ≤ fam a 0 nu` for `nu ≥ knee`. -/
theorem fam_b_le_zero (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    fam a b nu ≤ fam a 0 nu := by
  induction b with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (bstep a n nu hnu) ih

/-- Reduce `a` to `0` (at `b = 0`): `fam a 0 nu ≤ fam 0 0 nu` for `nu ≥ knee`. -/
theorem fam_a_le_zero (a : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    fam a 0 nu ≤ fam 0 0 nu := by
  induction a with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (astep n 0 nu hnu) ih

/-- **Full family reduction.**  `fam a b nu ≤ fam 0 0 nu` for `nu ≥ knee`. -/
theorem fam_le_cell (a b : ℕ) (nu : ℚ) (hnu : knee ≤ nu) :
    fam a b nu ≤ fam 0 0 nu :=
  le_trans (fam_b_le_zero a b nu hnu) (fam_a_le_zero a nu hnu)

/-- **The canonical family master bound (assembled).**

For every `a, b : ℕ` and every interior child `nu ∈ [knee, 1/2]`,
`fam a b nu ≤ T`.  This certifies the FULL heterogeneous canonical family
`C(a, b, nu)` of the "#37 scoped route": the two integer tails collapse to the
interior `nu`-cell (`astep`/`bstep` monotone reductions), which is discharged by the
homogeneous Bernstein bridges (`nu_cell`).  Equality is approached only at the peak
`(a,b,nu) = (0,0,1/2)` with value `0.872204*T`.  Kernel-clean, `conjecture1_proved = False`. -/
theorem family_master (a b : ℕ) (nu : ℚ) (h0 : knee ≤ nu) (h1 : nu ≤ 1 / 2) :
    fam a b nu ≤ T :=
  le_trans (fam_le_cell a b nu h0) (nu_cell nu h0 h1)

end HeteroFamily
