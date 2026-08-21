/- The block-level g-lemma, wired by structural induction over the cavity block tree.

   Completes Piece 3: defines the block tree with its cavity recursion (message mu, amplitude, Phi^11),
   the potential g C = Phi^11(C) * (1+mu_C/3)^11, and proves g C <= gamma for every block by structural
   induction -- applying the coordinate-wise capstone gstep_lt_gamma (Piece 1) at each branching node.

   Uses phi_le_one (Phi^11 <= 1, the proven <= half of BG) as a HYPOTHESIS at each child -- the strictness
   layer.  All over R.  conjecture1_proved = False. -/
import R3Cert.GArmExtAbstract

namespace G1
namespace GLemma

open ArmExtremality

/-- `W = 64/621`. -/
noncomputable def Wr : ℝ := 64 / 621
/-- `γ = W^2 (5/3)^11`. -/
noncomputable def gammaR : ℝ := Wr ^ 2 * (5 / 3) ^ 11

theorem Wr_pos : 0 < Wr := by unfold Wr; norm_num
theorem gammaR_pos : 0 < gammaR := by unfold gammaR Wr; positivity

/-- A cavity block: a root with a list of child blocks.  A leaf is `node []`. -/
inductive Blk where
  | node : List Blk → Blk

/- Cavity message mu_v = 1/(1 + j + S), j = #children, S = sum child messages. (Leaf: 1.) -/
mutual
noncomputable def muV : Blk → ℝ
  | .node ch => 1 / (1 + (ch.length : ℝ) + muSum ch)
noncomputable def muSum : List Blk → ℝ
  | [] => 0
  | b :: r => muV b + muSum r
end

/- Phi^11(v) = W * a_v^11 * prod Phi^11(child), a_v = 1 + S/(1+j). (Leaf: W.) -/
mutual
noncomputable def phiV : Blk → ℝ
  | .node ch => Wr * (1 + muSum ch / (1 + (ch.length : ℝ))) ^ 11 * phiProd ch
noncomputable def phiProd : List Blk → ℝ
  | [] => 1
  | b :: r => phiV b * phiProd r
end

/-- The g-potential `g(C) = Φ^11(C) · (1 + μ_C/3)^11`. -/
noncomputable def gV (C : Blk) : ℝ := phiV C * (1 + muV C / 3) ^ 11

mutual
theorem muV_pos (b : Blk) : 0 < muV b := by
  cases b with
  | node ch =>
    have hS : 0 ≤ muSum ch := muSum_nonneg ch
    rw [muV]
    apply div_pos one_pos
    have : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
    linarith
theorem muSum_nonneg (l : List Blk) : 0 ≤ muSum l := by
  cases l with
  | nil => simp [muSum]
  | cons b r => rw [muSum]; have := muV_pos b; have := muSum_nonneg r; linarith
end

/-- The message of a NON-leaf block (`≥ 1` child) is `≤ 1/2`. -/
theorem muV_nonleaf_le_half (ch : List Blk) (h : ch ≠ []) : muV (.node ch) ≤ 1 / 2 := by
  have hlen : 1 ≤ ch.length := List.length_pos_of_ne_nil h
  have hlen' : (1 : ℝ) ≤ (ch.length : ℝ) := by exact_mod_cast hlen
  have hS : 0 ≤ muSum ch := muSum_nonneg ch
  rw [muV, div_le_iff₀ (by linarith)]
  linarith

/-- **Structural identity.**  `g(node ch) = W · boostR (|ch|) (S)^11 · ∏ Φ^11(child)`, `S = Σ μ_child`. -/
theorem gV_node (ch : List Blk) :
    gV (.node ch) = Wr * boostR ch.length (muSum ch) ^ 11 * phiProd ch := by
  have hS : 0 ≤ muSum ch := muSum_nonneg ch
  have hlen : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
  have hd1 : (1 : ℝ) + (ch.length : ℝ) ≠ 0 := by positivity
  have hd2 : (1 : ℝ) + (ch.length : ℝ) + muSum ch ≠ 0 := by positivity
  have hd3 : (3 : ℝ) * (ch.length : ℝ) + 3 ≠ 0 := by positivity
  have hbe : (1 + muSum ch / (1 + (ch.length : ℝ))) * (1 + muV (.node ch) / 3)
      = boostR ch.length (muSum ch) := by
    rw [muV, boostR]; field_simp; ring
  rw [gV, phiV]
  rw [show Wr * (1 + muSum ch / (1 + (ch.length : ℝ))) ^ 11 * phiProd ch * (1 + muV (.node ch) / 3) ^ 11
        = Wr * ((1 + muSum ch / (1 + (ch.length : ℝ))) * (1 + muV (.node ch) / 3)) ^ 11 * phiProd ch by
      rw [mul_pow]; ring]
  rw [hbe]

/- Phi^11 >= 0 (needs no phi_le_one). -/
mutual
theorem phiV_nonneg (b : Blk) : 0 ≤ phiV b := by
  cases b with
  | node ch =>
    have hS : 0 ≤ muSum ch := muSum_nonneg ch
    have hlen : (0 : ℝ) ≤ (ch.length : ℝ) := by positivity
    rw [phiV]
    apply mul_nonneg (mul_nonneg Wr_pos.le (by positivity)) (phiProd_nonneg ch)
theorem phiProd_nonneg (l : List Blk) : 0 ≤ phiProd l := by
  cases l with
  | nil => rw [phiProd]; norm_num
  | cons b r => rw [phiProd]; exact mul_nonneg (phiV_nonneg b) (phiProd_nonneg r)
end

/-! ### The crossover `μ*` as a real (`(1+μ*/3)^11 = γ`, `0 ≤ μ* < 1/3`). -/

noncomputable def muStar : ℝ := 3 * gammaR ^ ((1 : ℝ) / 11) - 3

theorem muStar_crossover : (1 + muStar / 3) ^ 11 = gammaR := by
  have h : (1 : ℝ) + muStar / 3 = gammaR ^ ((1 : ℝ) / 11) := by unfold muStar; ring
  rw [h, ← Real.rpow_natCast (gammaR ^ ((1 : ℝ) / 11)) 11, ← Real.rpow_mul gammaR_pos.le]
  norm_num

theorem muStar_nonneg : 0 ≤ muStar := by
  have hg : (1 : ℝ) ≤ gammaR := by unfold gammaR Wr; norm_num
  have h1 : (1 : ℝ) ≤ gammaR ^ ((1 : ℝ) / 11) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 11) := (Real.one_rpow _).symm
      _ ≤ gammaR ^ ((1 : ℝ) / 11) := Real.rpow_le_rpow (by norm_num) hg (by norm_num)
  unfold muStar; linarith

theorem muStar_lt_third : muStar < 1 / 3 := by
  have hg : gammaR < ((10 : ℝ) / 9) ^ 11 := by unfold gammaR Wr; norm_num
  have h1 : gammaR ^ ((1 : ℝ) / 11) < (((10 : ℝ) / 9) ^ 11) ^ ((1 : ℝ) / 11) :=
    Real.rpow_lt_rpow gammaR_pos.le hg (by norm_num)
  rw [← Real.rpow_natCast ((10 : ℝ) / 9) 11, ← Real.rpow_mul (by norm_num)] at h1
  norm_num at h1
  unfold muStar; linarith

/-- `(ch.map muV).sum = muSum ch`. -/
theorem map_muV_sum (l : List Blk) : (l.map muV).sum = muSum l := by
  induction l with
  | nil => simp [muSum]
  | cons b r ih => rw [List.map_cons, List.sum_cons, muSum, ih]

/-- `gCoreOff` on `ch.map muV` expands to `boostR · ∏ factorR`. -/
theorem gCoreOff_expand (l : List Blk) :
    gCoreOff gammaR l.length 0 (l.map muV)
      = boostR l.length (muSum l) ^ 11 * (l.map (fun d => factorR gammaR (muV d))).prod := by
  unfold gCoreOff
  rw [zero_add, map_muV_sum, List.map_map]
  simp only [Function.comp_def]

/-- Termwise product bound: if each child's `Φ^11 ≤ factorR γ (μ child)`, the product drops. -/
theorem phiProd_le (l : List Blk)
    (h : ∀ d ∈ l, phiV d ≤ factorR gammaR (muV d)) :
    phiProd l ≤ (l.map (fun d => factorR gammaR (muV d))).prod := by
  induction l with
  | nil => simp [phiProd]
  | cons b r ih =>
    rw [phiProd, List.map_cons, List.prod_cons]
    have hb : phiV b ≤ factorR gammaR (muV b) := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrec := ih (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))
    have hfacb : 0 ≤ factorR gammaR (muV b) := factorR_nonneg gammaR (muV b) gammaR_pos (muV_pos b).le
    calc phiV b * phiProd r
        ≤ factorR gammaR (muV b) * phiProd r :=
          mul_le_mul_of_nonneg_right hb (phiProd_nonneg r)
      _ ≤ factorR gammaR (muV b) * (r.map (fun d => factorR gammaR (muV d))).prod :=
          mul_le_mul_of_nonneg_left hrec hfacb

/-- Real forms of the leaf / j=1 rational leaves. -/
theorem Wr_four_thirds_lt : Wr * (4 / 3 : ℝ) ^ 11 < gammaR := by unfold gammaR Wr; norm_num
theorem Wr_seventeen_le : Wr * (17 / 14 : ℝ) ^ 11 ≤ 1 := by unfold Wr; norm_num
theorem gammaR_lt_ten_ninths : gammaR < ((10 : ℝ) / 9) ^ 11 := by unfold gammaR Wr; norm_num

/-- The child factor bound: from `phi_le_one` and `g(d) ≤ γ` (IH), `Φ^11(d) ≤ factorR γ (μ d)`. -/
theorem child_factor_bound (d : Blk) (hpo : ∀ D, phiV D ≤ 1) (hd : gV d ≤ gammaR) :
    phiV d ≤ factorR gammaR (muV d) := by
  have hmu : 0 < 1 + muV d / 3 := by have := muV_pos d; linarith
  have hp : 0 < (1 + muV d / 3) ^ 11 := by positivity
  unfold factorR
  refine le_min (hpo d) ?_
  rw [le_div_iff₀ hp]
  have h := hd; rw [gV] at h; linarith

/-- `boostR 1 x = (7 + 3x)/6`. -/
theorem boostR_one (x : ℝ) : boostR 1 x = (7 + 3 * x) / 6 := by
  unfold boostR; rw [show (3 * ((1 : ℕ) : ℝ) + 3) = 6 by norm_num]; ring

/-- `0 ≤ W · boostR j S ^ 11` when `0 ≤ S`. -/
theorem Wr_boost_nonneg (j : ℕ) (S : ℝ) (hS : 0 ≤ S) : 0 ≤ Wr * boostR j S ^ 11 :=
  mul_nonneg Wr_pos.le (pow_nonneg (boostR_pos j S hS).le 11)

/- The g-lemma. Assuming phi_le_one, g C <= gamma for every block, by structural induction:
   leaf (leaf II), j=1 (rational split / exact arm equality), j>=2 (capstone). -/
mutual
theorem gV_le (hpo : ∀ D, phiV D ≤ 1) (C : Blk) : gV C ≤ gammaR := by
  cases C with
  | node ch =>
    have ihall : ∀ d ∈ ch, gV d ≤ gammaR := gVList_le hpo ch
    have hcf : ∀ d ∈ ch, phiV d ≤ factorR gammaR (muV d) :=
      fun d hd => child_factor_bound d hpo (ihall d hd)
    rw [gV_node]
    rcases ch with _ | ⟨c0, ds⟩
    · -- j = 0 (leaf)
      simp only [List.length_nil, muSum, phiProd, mul_one]
      rw [show boostR 0 (0 : ℝ) = 4 / 3 by unfold boostR; norm_num]
      exact Wr_four_thirds_lt.le
    · rcases ds with _ | ⟨c1, rest⟩
      · -- j = 1 : ch = [c0]
        have hM : muSum [c0] = muV c0 := by simp [muSum]
        have hP : phiProd [c0] = phiV c0 := by simp [phiProd]
        have hfac : phiV c0 ≤ factorR gammaR (muV c0) := hcf c0 (List.mem_cons.mpr (Or.inl rfl))
        rw [show [c0].length = 1 from rfl, hM, hP]
        have hμ0 : 0 < muV c0 := muV_pos c0
        have hb1pos : 0 < boostR 1 (muV c0) := boostR_pos 1 _ hμ0.le
        set μ := muV c0 with hμ
        cases c0 with
        | node cch =>
          by_cases hleaf : cch = []
          · -- leaf child: g = γ exactly
            subst hleaf
            have hmv : μ = 1 := by rw [hμ, muV]; simp [muSum]
            have hpv : phiV (.node []) = Wr := by rw [phiV]; simp [muSum, phiProd]
            rw [hpv, hmv, boostR_one]
            apply le_of_eq; unfold gammaR Wr; norm_num
          · -- non-leaf child: rational split at 1/3
            have hle_half : μ ≤ 1 / 2 := by rw [hμ]; exact muV_nonleaf_le_half cch hleaf
            by_cases hlt3 : μ < 1 / 3
            · -- light
              have hb43 : boostR 1 μ < 4 / 3 := by rw [boostR_one]; rw [div_lt_iff₀ (by norm_num)]; nlinarith
              have hfac1 : factorR gammaR μ ≤ 1 := min_le_left _ _
              calc Wr * boostR 1 μ ^ 11 * phiV (.node cch)
                  ≤ Wr * boostR 1 μ ^ 11 * factorR gammaR μ :=
                    mul_le_mul_of_nonneg_left hfac (Wr_boost_nonneg 1 μ hμ0.le)
                _ ≤ Wr * boostR 1 μ ^ 11 * 1 :=
                    mul_le_mul_of_nonneg_left hfac1 (Wr_boost_nonneg 1 μ hμ0.le)
                _ = Wr * boostR 1 μ ^ 11 := by ring
                _ ≤ Wr * (4 / 3) ^ 11 := by
                    apply mul_le_mul_of_nonneg_left _ Wr_pos.le; gcongr
                _ ≤ gammaR := Wr_four_thirds_lt.le
            · -- heavy
              rw [not_lt] at hlt3
              have hmu3 : 0 < 1 + μ / 3 := by linarith
              have hmu3p : 0 < (1 + μ / 3) ^ 11 := by positivity
              have hge : gammaR ≤ (1 + μ / 3) ^ 11 := by
                have h109 : ((10 : ℝ) / 9) ^ 11 ≤ (1 + μ / 3) ^ 11 := by gcongr; linarith
                linarith [gammaR_lt_ten_ninths]
              have hfac2 : factorR gammaR μ = gammaR / (1 + μ / 3) ^ 11 := by
                unfold factorR; rw [min_eq_right (by rw [div_le_one hmu3p]; exact hge)]
              -- key: Wr * boostR^11 ≤ (1+μ/3)^11  (via pow of 14·boost ≤ 17·(1+μ/3) + core_nonleaf_j1)
              have h14 : 14 * boostR 1 μ ≤ 17 * (1 + μ / 3) := by
                rw [boostR_one, ← mul_div_assoc, div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]; nlinarith [hle_half]
              have hb0 : (0 : ℝ) ≤ 14 * boostR 1 μ := by positivity
              have hpow : (14 * boostR 1 μ) ^ 11 ≤ (17 * (1 + μ / 3)) ^ 11 := by gcongr
              rw [mul_pow, mul_pow] at hpow
              have hWr17 : Wr * 17 ^ 11 ≤ 14 ^ 11 := by
                have h := Wr_seventeen_le
                rw [div_pow, ← mul_div_assoc, div_le_one (by positivity)] at h; linarith
              have hM : (0 : ℝ) ≤ (1 + μ / 3) ^ 11 := by positivity
              have hkey : Wr * boostR 1 μ ^ 11 ≤ (1 + μ / 3) ^ 11 := by
                have p1 : (14 : ℝ) ^ 11 * (Wr * boostR 1 μ ^ 11) ≤ Wr * 17 ^ 11 * (1 + μ / 3) ^ 11 := by
                  nlinarith [mul_le_mul_of_nonneg_left hpow Wr_pos.le]
                have p2 : Wr * 17 ^ 11 * (1 + μ / 3) ^ 11 ≤ 14 ^ 11 * (1 + μ / 3) ^ 11 :=
                  mul_le_mul_of_nonneg_right hWr17 hM
                exact le_of_mul_le_mul_left (le_trans p1 p2) (by positivity)
              calc Wr * boostR 1 μ ^ 11 * phiV (.node cch)
                  ≤ Wr * boostR 1 μ ^ 11 * factorR gammaR μ :=
                    mul_le_mul_of_nonneg_left hfac (Wr_boost_nonneg 1 μ hμ0.le)
                _ = (Wr * boostR 1 μ ^ 11) * (gammaR / (1 + μ / 3) ^ 11) := by rw [hfac2]
                _ ≤ (1 + μ / 3) ^ 11 * (gammaR / (1 + μ / 3) ^ 11) :=
                    mul_le_mul_of_nonneg_right hkey (div_nonneg gammaR_pos.le hmu3p.le)
                _ = gammaR := by field_simp
      · -- j ≥ 2 : ch = c0 :: c1 :: rest
        set ch := c0 :: c1 :: rest with hch
        have hlen2 : 2 ≤ ch.length := by rw [hch]; simp
        have hpl := phiProd_le ch hcf
        have hcap := gstep_lt_gamma ch.length hlen2 gammaR Wr muStar
          muStar_nonneg muStar_lt_third muStar_crossover Wr_pos Wr_four_thirds_lt
          (ch.map muV) (by rw [List.length_map]) (by
            intro v hv; rw [List.mem_map] at hv; obtain ⟨d, _, rfl⟩ := hv; exact (muV_pos d).le)
        calc Wr * boostR ch.length (muSum ch) ^ 11 * phiProd ch
            ≤ Wr * boostR ch.length (muSum ch) ^ 11 * (ch.map (fun d => factorR gammaR (muV d))).prod :=
              mul_le_mul_of_nonneg_left hpl (Wr_boost_nonneg _ _ (muSum_nonneg ch))
          _ = Wr * gCoreOff gammaR ch.length 0 (ch.map muV) := by rw [gCoreOff_expand]; ring
          _ ≤ gammaR := hcap.le
theorem gVList_le (hpo : ∀ D, phiV D ≤ 1) (l : List Blk) : ∀ d ∈ l, gV d ≤ gammaR := by
  intro d hd
  cases l with
  | nil => simp at hd
  | cons b r =>
    rw [List.mem_cons] at hd
    rcases hd with h | h
    · rw [h]; exact gV_le hpo b
    · exact gVList_le hpo r d h
end

end GLemma
end G1
