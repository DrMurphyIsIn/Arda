import CF_EData
import CF_Arch

/-!
# CF_Num: the M-mode prime-side checker, exp enclosures, and rounded sums

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Exact-rational ball arithmetic; nothing here bears on RH.

* `blk_sum_eq`: the autocorrelation of the M-mode test on `[0, 2A]` collapses to
  `g(y) = ((2A - y)/2) sum_i c_i^2 cos(k_i y) + sum_m alpha_m sin(k_m y)` with
  `alpha_m = c_m^2/(2 k_m) + 2 c_m s_m sum_{i != m} c_i s_i k_i/(k_i^2 - k_m^2)`;
* `mEntry_sound`: a table entry that passes `mEntryOK` (log n and 1/sqrt n enclosures via Mathlib's
  `Real.exp_bound`, the `M` phase reductions, and `log n < 2A`) yields a ball containing
  `2 (rho log n)/sqrt n g(log n)` for any rational `rho` (the weight is `rho log n`);
* `exp_le_Q` / `exp_ge_Q`: `exp q` for a rational `q` with `|q/8| <= 1`, from `exp(q/8)^8`;
* `sumLo_le` / `le_sumHi`: sums with every term rounded down / up to `10^-R`.
No `sorry`.
-/

open MeasureTheory Complex Set Filter Crux3

noncomputable section

namespace CF

/-! ## The block-sum identity -/

/-- The sine coefficient of the collapsed autocorrelation. -/
def alphaR (M : ℕ) (k s c : ℕ → ℝ) (m : ℕ) : ℝ :=
  c m ^ 2 / (2 * k m)
    + 2 * c m * s m * ∑ i ∈ Finset.range M, (if i = m then 0 else c i * s i * k i / (k i ^ 2 - k m ^ 2))

theorem blk_sum_eq (A : ℝ) (M : ℕ) (k s c : ℕ → ℝ) (hk : ∀ i, i < M → k i ≠ 0)
    (hinj : ∀ i, i < M → ∀ j, j < M → i ≠ j → k i ^ 2 - k j ^ 2 ≠ 0) (y : ℝ) :
    ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, c i * c j * blk A k s i j y
      = ((2 * A - y) / 2) * ∑ i ∈ Finset.range M, c i ^ 2 * Real.cos (k i * y)
        + ∑ m ∈ Finset.range M, alphaR M k s c m * Real.sin (k m * y) := by
  -- U i j = c_i c_j s_i s_j k_i sin(k_j y)/(k_i^2 - k_j^2) off the diagonal
  set U : ℕ → ℕ → ℝ := fun i j =>
    if i = j then 0 else c i * c j * s i * s j * k i * Real.sin (k j * y) / (k i ^ 2 - k j ^ 2) with hU
  have hsplit : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M, c i * c j * blk A k s i j y
      = (if i = j then c i ^ 2 * gD A (k i) y else 0) + (U i j + U j i) := by
    intro i hi j hj
    have hiM := Finset.mem_range.mp hi
    have hjM := Finset.mem_range.mp hj
    unfold blk
    simp only [hU]
    split_ifs with h1 h2 h2
    · subst h1; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · have hd := hinj i hiM j hjM h1
      have hd' := hinj j hjM i hiM h2
      have e : k j ^ 2 - k i ^ 2 = -(k i ^ 2 - k j ^ 2) := by ring
      rw [e]
      field_simp
      ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hsplit i hi j hj]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => U j i)]
  have hdiag : ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, (if i = j then c i ^ 2 * gD A (k i) y else 0)
      = ∑ i ∈ Finset.range M, c i ^ 2 * gD A (k i) y := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, if_pos hi]
  rw [hdiag]
  -- sum_i sum_j U i j = sum_j sin(k_j y) c_j s_j sum_i [i != j] c_i s_i k_i/(k_i^2 - k_j^2)
  have hU2 : ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, U i j
      = ∑ m ∈ Finset.range M, (c m * s m * ∑ i ∈ Finset.range M,
          (if i = m then 0 else c i * s i * k i / (k i ^ 2 - k m ^ 2))) * Real.sin (k m * y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hU]
    split_ifs <;> ring
  rw [hU2]
  have hgD : ∑ i ∈ Finset.range M, c i ^ 2 * gD A (k i) y
      = ((2 * A - y) / 2) * ∑ i ∈ Finset.range M, c i ^ 2 * Real.cos (k i * y)
        + ∑ i ∈ Finset.range M, c i ^ 2 / (2 * k i) * Real.sin (k i * y) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hk i (Finset.mem_range.mp hi)
    unfold gD
    field_simp
    try ring
  rw [hgD]
  unfold alphaR
  have e : ∀ m ∈ Finset.range M, (c m ^ 2 / (2 * k m) + 2 * c m * s m * ∑ i ∈ Finset.range M,
        (if i = m then 0 else c i * s i * k i / (k i ^ 2 - k m ^ 2))) * Real.sin (k m * y)
      = c m ^ 2 / (2 * k m) * Real.sin (k m * y)
        + ((c m * s m * ∑ i ∈ Finset.range M, (if i = m then 0 else c i * s i * k i / (k i ^ 2 - k m ^ 2)))
            * Real.sin (k m * y)
          + (c m * s m * ∑ i ∈ Finset.range M, (if i = m then 0 else c i * s i * k i / (k i ^ 2 - k m ^ 2)))
            * Real.sin (k m * y)) := fun m _ => by ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_add_distrib]
  ring

/-! ## The checker -/

/-- The M-mode test data: `A = Q pi`, frequencies `k`, signs `s = sin(k A)`, coefficients `c`. -/
structure MData where
  Q : ℚ
  M : ℕ
  k : ℕ → ℚ
  s : ℕ → ℚ
  c : ℕ → ℚ

/-- One table entry: `log n in [lo, hi]`, `1/sqrt n in [q0, q1]`, and the reduction multiples. -/
structure MEntry where
  lo : ℚ
  hi : ℚ
  q0 : ℚ
  q1 : ℚ
  ms : List ℤ

def yBm (E : MEntry) : ℚ × ℚ := ((E.lo + E.hi) / 2, (E.hi - E.lo) / 2)
def sBm (E : MEntry) : ℚ × ℚ := ((E.q0 + E.q1) / 2, (E.q1 - E.q0) / 2)
def phiM (D : MData) (E : MEntry) (i : ℕ) : ℚ × ℚ :=
  bRound (bSub (bC (D.k i) (yBm E)) (bC (2 * E.ms.getD i 0) piB)) RD

/-- The sine coefficient over `ℚ`. -/
def alphaQ (D : MData) (m : ℕ) : ℚ :=
  D.c m ^ 2 / (2 * D.k m)
    + 2 * D.c m * D.s m * ∑ i ∈ Finset.range D.M, (if i = m then 0 else D.c i * D.s i * D.k i / (D.k i ^ 2 - D.k m ^ 2))

/-- The ball of `g(log n)`. -/
def gBm (D : MData) (E : MEntry) : ℚ × ℚ :=
  bAdd (bMul (bC (1 / 2) (bSub (bC 2 (bC D.Q piB)) (yBm E)))
      (∑ i ∈ Finset.range D.M, bC (D.c i ^ 2) (cosB (phiM D E i))))
    (∑ i ∈ Finset.range D.M, bC (alphaQ D i) (sinB (phiM D E i)))

/-- The weight ball `2 rho log n / sqrt n`. -/
def wBm (rho : ℚ) (E : MEntry) : ℚ × ℚ := bMul (bC (2 * rho) (yBm E)) (sBm E)

/-- The output ball of an entry for the weight `rho log n`. -/
def outM (D : MData) (rho : ℚ) (E : MEntry) : ℚ × ℚ := bRound (bMul (wBm rho E) (gBm D E)) RT

/-- The Boolean check of an entry. -/
def mEntryOK (D : MData) (n : ℕ) (E : MEntry) : Bool :=
  decide (0 < n) && decide (|E.lo / 8| ≤ 1) && decide (|E.hi / 8| ≤ 1) &&
   decide ((expSQ KX (E.lo / 8) + expRQ KX (E.lo / 8)) ^ 8 ≤ (n : ℚ)) &&
   decide (0 ≤ expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) &&
   decide ((n : ℚ) ≤ (expSQ KX (E.hi / 8) - expRQ KX (E.hi / 8)) ^ 8) &&
   decide (0 ≤ E.q0) && decide (E.q0 ^ 2 * n ≤ 1) && decide (1 ≤ E.q1 ^ 2 * n) && decide (0 ≤ E.q1) &&
   (List.range D.M).all (fun i => decide (|(phiM D E i).1| ≤ ((2 * MT + 1 : ℕ) : ℚ) / 2)) &&
   decide (E.hi < 2 * D.Q * PLOq)

/-- The collapsed autocorrelation as a real function. -/
def gstar (D : MData) (y : ℝ) : ℝ :=
  ((2 * ((D.Q : ℝ) * Real.pi) - y) / 2) * ∑ i ∈ Finset.range D.M, ((D.c i : ℝ)) ^ 2 * Real.cos ((D.k i : ℝ) * y)
    + ∑ m ∈ Finset.range D.M, ((alphaQ D m : ℚ) : ℝ) * Real.sin ((D.k m : ℝ) * y)

lemma InB.fst_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (b : ι → ℚ × ℚ)
    (h : ∀ i ∈ s, InB (x i) (b i).1 (b i).2) : InB (∑ i ∈ s, x i) (∑ i ∈ s, b i).1 (∑ i ∈ s, b i).2 := by
  rw [Prod.fst_sum, Prod.snd_sum]
  exact InB.sum s x (fun i => (b i).1) (fun i => (b i).2) h

/-- **Soundness of one entry** (any rational weight `rho`). -/
theorem mEntry_sound (D : MData) (hQ : 0 ≤ D.Q) (n : ℕ) (E : MEntry) (hok : mEntryOK D n E = true) (rho : ℚ) :
    InB (2 * ((rho : ℝ) * Real.log n) / Real.sqrt n * gstar D (Real.log n)) (outM D rho E).1 (outM D rho E).2
      ∧ Real.log n < 2 * ((D.Q : ℝ) * Real.pi) := by
  have hok' := hok
  unfold mEntryOK at hok'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hlo8⟩, hhi8⟩, hexp1⟩, hexp2⟩, hexp3⟩, hq0⟩, hq01⟩, hq11⟩, hq1⟩, hph⟩, hA⟩ := hok'
  have hy : InB (Real.log n) (yBm E).1 (yBm E).2 := by
    apply InB.of_bounds
    · exact le_log_of KX (by unfold KX; norm_num) n hn hlo8 hexp1
    · exact log_le_of KX (by unfold KX; norm_num) n hn hhi8 hexp2 hexp3
  have hs : InB (1 / Real.sqrt n) (sBm E).1 (sBm E).2 := by
    obtain ⟨a, b⟩ := inv_sqrt_between hn hq0 hq01 hq11 hq1
    exact InB.of_bounds a b
  have hpi : InB Real.pi piB.1 piB.2 := pi_InB
  have hphi : ∀ i : ℕ, InB ((D.k i : ℝ) * Real.log n - ((E.ms.getD i 0 : ℤ) : ℝ) * (2 * Real.pi))
      (phiM D E i).1 (phiM D E i).2 := by
    intro i
    have := ((hy.bC (D.k i)).bSub (hpi.bC (2 * E.ms.getD i 0))).bRound RD
    refine this.of_eq ?_
    push_cast; ring
  have hc : ∀ i, i < D.M → InB (Real.cos ((D.k i : ℝ) * Real.log n)) (cosB (phiM D E i)).1 (cosB (phiM D E i)).2 := by
    intro i hi
    have := InB.cos_of MT (E.ms.getD i 0) (hphi i) (hph i hi)
    unfold cosB
    refine this.mono (le_of_eq ?_)
    ring
  have hsn : ∀ i, i < D.M → InB (Real.sin ((D.k i : ℝ) * Real.log n)) (sinB (phiM D E i)).1 (sinB (phiM D E i)).2 := by
    intro i hi
    have hm' : |(phiM D E i).1| ≤ ((2 * MT + 1 + 1 : ℕ) : ℚ) / 2 := by
      refine (hph i hi).trans ?_
      push_cast
      linarith
    have := InB.sin_of MT (E.ms.getD i 0) (hphi i) hm'
    unfold sinB
    refine this.mono (le_of_eq ?_)
    ring
  have htA : InB ((2 * ((D.Q : ℝ) * Real.pi) - Real.log n) / 2)
      (bC (1 / 2) (bSub (bC 2 (bC D.Q piB)) (yBm E))).1 (bC (1 / 2) (bSub (bC 2 (bC D.Q piB)) (yBm E))).2 := by
    have := (((hpi.bC D.Q).bC 2).bSub hy).bC (1 / 2)
    refine this.of_eq ?_
    push_cast; ring
  have hC : InB (∑ i ∈ Finset.range D.M, ((D.c i : ℝ)) ^ 2 * Real.cos ((D.k i : ℝ) * Real.log n))
      (∑ i ∈ Finset.range D.M, bC (D.c i ^ 2) (cosB (phiM D E i))).1
      (∑ i ∈ Finset.range D.M, bC (D.c i ^ 2) (cosB (phiM D E i))).2 := by
    refine InB.fst_sum _ _ _ fun i hi => ?_
    have := (hc i (Finset.mem_range.mp hi)).bC (D.c i ^ 2)
    refine this.of_eq ?_
    push_cast; ring
  have hS : InB (∑ m ∈ Finset.range D.M, ((alphaQ D m : ℚ) : ℝ) * Real.sin ((D.k m : ℝ) * Real.log n))
      (∑ i ∈ Finset.range D.M, bC (alphaQ D i) (sinB (phiM D E i))).1
      (∑ i ∈ Finset.range D.M, bC (alphaQ D i) (sinB (phiM D E i))).2 :=
    InB.fst_sum _ _ _ fun i hi => (hsn i (Finset.mem_range.mp hi)).bC (alphaQ D i)
  have hg : InB (gstar D (Real.log n)) (gBm D E).1 (gBm D E).2 := (htA.bMul hC).bAdd hS
  have hw : InB (2 * ((rho : ℝ) * Real.log n) / Real.sqrt n) (wBm rho E).1 (wBm rho E).2 := by
    have := (hy.bC (2 * rho)).bMul hs
    refine this.of_eq ?_
    push_cast; ring
  refine ⟨(hw.bMul hg).bRound RT, ?_⟩
  have h1 := hy.le
  have h2 : ((E.lo + E.hi) / 2 + (E.hi - E.lo) / 2 : ℚ) = E.hi := by ring
  unfold yBm at h1
  simp only at h1
  rw [h2] at h1
  have h3 : ((E.hi : ℚ) : ℝ) < ((2 * D.Q * PLOq : ℚ) : ℝ) := by exact_mod_cast hA
  have h4 := Real.pi_gt_d20
  push_cast at h3
  have hPL : (PLOq : ℝ) ≤ Real.pi := by unfold PLOq; push_cast; linarith
  have hQR : (0 : ℝ) ≤ D.Q := by exact_mod_cast hQ
  have h5 : 2 * (D.Q : ℝ) * PLOq ≤ 2 * ((D.Q : ℝ) * Real.pi) := by nlinarith
  linarith

/-! ## exp enclosures of rationals -/

lemma exp_le_Q {q : ℚ} (hq : |q / 8| ≤ 1) :
    Real.exp (q : ℝ) ≤ (((expSQ KX (q / 8) + expRQ KX (q / 8)) ^ 8 : ℚ) : ℝ) := by
  have h := exp_near KX (by unfold KX; norm_num) hq
  have hup : Real.exp ((q / 8 : ℚ) : ℝ) ≤ ((expSQ KX (q / 8) + expRQ KX (q / 8) : ℚ) : ℝ) := by
    have := le_abs_self (Real.exp ((q / 8 : ℚ) : ℝ) - (expSQ KX (q / 8) : ℝ))
    rw [Rat.cast_add]
    linarith
  have h8 : Real.exp (q : ℝ) = Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [h8, Rat.cast_pow]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hup 8

lemma exp_ge_Q {q : ℚ} (hq : |q / 8| ≤ 1) (hpos : 0 ≤ expSQ KX (q / 8) - expRQ KX (q / 8)) :
    (((expSQ KX (q / 8) - expRQ KX (q / 8)) ^ 8 : ℚ) : ℝ) ≤ Real.exp (q : ℝ) := by
  have h := exp_near KX (by unfold KX; norm_num) hq
  have hlo : ((expSQ KX (q / 8) - expRQ KX (q / 8) : ℚ) : ℝ) ≤ Real.exp ((q / 8 : ℚ) : ℝ) := by
    have := neg_abs_le (Real.exp ((q / 8 : ℚ) : ℝ) - (expSQ KX (q / 8) : ℝ))
    rw [Rat.cast_sub]
    linarith
  have h8 : Real.exp (q : ℝ) = Real.exp ((q / 8 : ℚ) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hposR : (0 : ℝ) ≤ ((expSQ KX (q / 8) - expRQ KX (q / 8) : ℚ) : ℝ) := by exact_mod_cast hpos
  rw [h8, Rat.cast_pow]
  exact pow_le_pow_left₀ hposR hlo 8

/-! ## Rounded sums -/

/-- Round up to `10^-R`. -/
def ceilR (q : ℚ) (R : ℕ) : ℚ := -KWin.floorR (-q) R

lemma le_ceilR (q : ℚ) (R : ℕ) : q ≤ ceilR q R := by
  unfold ceilR
  have := KWin.floorR_le (-q) R
  linarith

/-- The sum with every term rounded down. -/
def sumLo (f : ℕ → ℚ) (n R : ℕ) : ℚ := ∑ j ∈ Finset.range n, KWin.floorR (f j) R

/-- The sum with every term rounded up. -/
def sumHi (f : ℕ → ℚ) (n R : ℕ) : ℚ := ∑ j ∈ Finset.range n, ceilR (f j) R

lemma sumLo_le (f : ℕ → ℚ) (n R : ℕ) : sumLo f n R ≤ ∑ j ∈ Finset.range n, f j :=
  Finset.sum_le_sum fun j _ => KWin.floorR_le (f j) R

lemma le_sumHi (f : ℕ → ℚ) (n R : ℕ) : ∑ j ∈ Finset.range n, f j ≤ sumHi f n R :=
  Finset.sum_le_sum fun j _ => le_ceilR (f j) R

end CF
