/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/
import Arb4_Edge

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The slab budget -/

/-- `C_5 (R L)^6 ((N - 1) + emcB) + 3 corrVar + C_6' Qr / (N^12 r0) / (25/2)`, `C_6' = 84107·10^-15`. -/
def slabBudgetQ (N : ℕ) (R L a U : Q) (Qr r0 : ℕ) : Q :=
  add (add (mul (mul (CpQ 5) (npow (mul R L) (5 + 1))) (add (sub (ofNat N) (ofNat 1)) (emcBQ 6 N a U)))
      (mul (ofNat 3) (corrVarQ 6 N R a U)))
    (div (div (mul (frac 84107 (10 ^ 15)) (ofNat Qr)) (ofNat (N ^ 12 * r0))) (frac 25 2))

theorem slabBudget_le (N : ℕ) (hN : 1 ≤ N) (R L a U : Q) (Qr r0 : ℕ) (hr0 : 0 < r0) (ha : 0 < a.n) :
    ArbEcon.Off.Cp 5 * (R.val * L.val) ^ (5 + 1) * (((N : ℝ) - 1) + ArbEcon.Off.emcB 6 N a.val U.val)
        + 3 * ArbEcon.Off.corrVar 6 N R.val a.val U.val
        + ArbEcon.Off.CK 6 * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2)
      ≤ (slabBudgetQ N R L a U Qr r0).val := by
  have hNr : (0 : ℤ) < ((N ^ 12 * r0 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) hr0
  unfold slabBudgetQ
  rw [val_add, val_add, val_mul, val_mul, val_CpQ, val_npow, val_mul, val_add, val_sub, val_ofNat,
    val_ofNat, val_emcBQ 6 N (by norm_num) (by omega) a U ha, val_mul, val_ofNat,
    val_corrVarQ 6 N (by norm_num) (by omega) R a U ha, val_div _ (by norm_num [frac]),
    val_div _ hNr, val_mul, val_frac _ (by norm_num), val_frac _ (by norm_num), val_ofNat, val_ofNat]
  have hC := H1000Oct.CK_six_le
  have hC0 := ArbEcon.Off.CK_nonneg 6
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (2 * 6) * r0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have : (0 : ℝ) < r0 := by exact_mod_cast hr0
    positivity
  have hm : ArbEcon.Off.CK 6 * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2)
      ≤ (84107 / 1000000000000000 : ℝ) * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2) := by
    gcongr
  push_cast at hm ⊢
  norm_num at hm ⊢
  linarith

/-! ## B. The certificate data -/

/-- One cell `[xs j, xs (j+1)] × [lo, hi]` of a slab: center `σ = (a - b)/q ≥ 0`, `tc = tn / 2^tq`,
    radius `rn / rd`, half-widths `w`, `hh` of the rectangle around the center. -/
structure CellD where
  a : ℕ
  b : ℕ
  q : ℕ
  tn : ℕ
  rn : ℕ
  rd : ℕ
  w : Q
  hh : Q

/-- The certificate data of one slab `[1/2, 1] × [lo, hi]` (the reflection covers `(0, 1/2)`). -/
structure SlabD where
  /-- dyadic exponent of every cell center height -/
  tq : ℕ
  /-- EM cut, log bound, budget radius `R` (at least every cell radius) -/
  N : ℕ
  L : Q
  R : Q
  /-- the slab `[lo, hi]`; `lo` is also the lower bound `a ≤ Im s` of the budget -/
  lo : Q
  hi : Q
  /-- `‖c + j‖ ≤ U`, `pochNormSq 1 hi 13 ≤ Qr²`, `r0² ≤ N`, the budget `FN / FD` -/
  U : Q
  Qr : ℕ
  r0 : ℕ
  FN : ℕ
  FD : ℕ
  /-- `m` columns `[xs j, xs (j+1)]`, `xs 0 = 1/2`, `xs m = 1` -/
  m : ℕ
  xs : ℕ → Q
  cell : ℕ → CellD

namespace CellD

noncomputable def σ (C : CellD) : ℝ := ((C.a : ℝ) - C.b) / C.q

def σQ (C : CellD) : Q := frac ((C.a : ℤ) - C.b) C.q

def oc (C : CellD) : ArbEcon.Off.OCfg := ⟨C.a, C.b, C.q, 2 ^ (C.q * 64), 256⟩

theorem val_σQ (C : CellD) (hq : 1 ≤ C.q) : C.σQ.val = C.σ := by
  rw [σQ, val_frac _ hq, σ]; push_cast; ring

end CellD

/-! ## C. One cell -/

/-- **The cell checker** (cell `j` of slab `S`): the evaluator run at the center (recomputed), the
    kernel check `checkCell`, and the cell's side conditions and rectangle geometry. -/
noncomputable def cellOK (S : SlabD) (j : ℕ) : Bool :=
  let C := S.cell j
  let c := ArbEcon.OrderK.cfg64 C.tn S.tq
  let s1 := ArbEcon.Off.runO c C.oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c C.oc 1 s1
  Nat.ble 2 S.N && Nat.ble 1 C.q && Nat.ble 1 C.rd && Nat.ble C.b C.a &&
    ArbEcon.Off.checkCell c C.oc 6 S.N 5 s1.acc sN.acc C.rn C.rd S.FN S.FD &&
    le (frac (C.rn : ℤ) C.rd) S.R && le (ofNat sN.lhi) (mul S.L (ofNat (2 ^ 64))) &&
    le S.lo (tQ C.tn S.tq) &&
    le (add (npow (add C.σQ (ofNat 11)) 2) (npow (tQ C.tn S.tq) 2)) (npow S.U 2) &&
    le (qabs (sub (S.xs j) C.σQ)) C.w && le (qabs (sub (S.xs (j + 1)) C.σQ)) C.w &&
    le (qabs (sub S.lo (tQ C.tn S.tq))) C.hh && le (qabs (sub S.hi (tQ C.tn S.tq))) C.hh &&
    le (add (npow C.w 2) (npow C.hh 2)) (npow (frac (C.rn : ℤ) C.rd) 2)

/-- The slab-level facts every cell uses. -/
def slabHeadOK (S : SlabD) : Bool :=
  Nat.ble 1 S.m && Nat.ble 1 S.FD && eqB (S.xs 0) (frac 1 2) && eqB (S.xs S.m) (ofNat 1) &&
    le (mul S.R S.L) (ofNat 1) && decide (0 < S.lo.n) && decide (0 ≤ S.U.n) &&
    le (pochQ (ofNat 1) S.hi 13) (ofNat (S.Qr * S.Qr)) && Nat.ble 1 S.r0 &&
    Nat.ble (S.r0 * S.r0) S.N && Nat.ble 1 S.N &&
    le (slabBudgetQ S.N S.R S.L S.lo S.U S.Qr S.r0) (frac (S.FN : ℤ) S.FD)

theorem runs_inv_cell (S : SlabD) (C : CellD) (hN : 2 ≤ S.N) (hq : 1 ≤ C.q) :
    ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.σ ((C.tn : ℝ) / 2 ^ S.tq) (S.N - 1)
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
          (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5)) ∧
      ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.σ ((C.tn : ℝ) / 2 ^ S.tq) S.N
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc 1
          (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
            (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5))) := by
  set c := ArbEcon.OrderK.cfg64 C.tn S.tq with hc
  set t : ℝ := (C.tn : ℝ) / 2 ^ S.tq with ht
  have hv : ArbEcon.Valid c t 9 := ArbEcon.OrderK.valid64 C.tn S.tq t rfl
  have ho : ArbEcon.Off.OValid c C.oc C.σ := ⟨rfl, hq, rfl⟩
  have i0 := ArbEcon.Off.initO_sound c C.σ t 5 hv.one_eq
  have i1 := ArbEcon.Off.runO_sound c C.oc C.σ t 9 hv ho (S.N - 2) 1 _ i0
  rw [show 1 + (S.N - 2) = S.N - 1 by omega] at i1
  have i2 := ArbEcon.Off.runO_sound c C.oc C.σ t 9 hv ho 1 (S.N - 1) _ i1
  rw [show S.N - 1 + 1 = S.N by omega] at i2
  exact ⟨i1, i2⟩

set_option maxHeartbeats 1000000 in
/-- **Soundness of one cell**: `ζ ≠ 0` on the rectangle `[xs j, xs (j+1)] × [lo, hi]` (for
    `1/2 ≤ x ≤ 1`). -/
theorem cellOK_sound (S : SlabD) (hS : slabHeadOK S = true) (j : ℕ) (h : cellOK S j = true) :
    ∀ x y : ℝ, x ∈ Set.uIcc (S.xs j).val (S.xs (j + 1)).val →
      S.lo.val ≤ y → y ≤ S.hi.val → 1 / 2 ≤ x → x ≤ 1 →
      riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro x y hx hy0 hy1 hxh hx1
  simp only [slabHeadOK, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, hFD⟩, _⟩, _⟩, hRL⟩, hlo⟩, hU0⟩, hQ⟩, hr0⟩, hr0N⟩, hN1⟩, hbud⟩ := hS
  simp only [cellOK, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN2, hq⟩, hrd⟩, hba⟩, hchk⟩, hrR⟩, hL⟩, hta⟩, hU⟩, hw0⟩, hw1⟩, hh0⟩, hh1⟩,
    hwr⟩ := h
  set C := S.cell j with hC
  set tc : ℝ := (C.tn : ℝ) / 2 ^ S.tq with htc
  obtain ⟨i1, i2⟩ := runs_inv_cell S C hN2 hq
  -- values
  have hrR' := le_sound hrR
  rw [val_frac _ hrd] at hrR'
  push_cast at hrR'
  have hL' := le_sound hL
  rw [val_ofNat, val_mul, val_ofNat] at hL'
  have hta' := le_sound hta
  rw [val_tQ] at hta'
  have hU' := le_sound hU
  rw [val_add, val_npow, val_add, C.val_σQ hq, val_ofNat, val_npow, val_tQ, val_npow] at hU'
  have hRL' := le_sound hRL
  rw [val_mul, val_ofNat, Nat.cast_one] at hRL'
  have hQ' := le_sound hQ
  rw [val_pochQ, val_ofNat, val_ofNat, Nat.cast_one] at hQ'
  have hbud' := le_trans (slabBudget_le S.N hN1 S.R S.L S.lo S.U S.Qr S.r0 hr0 hlo) (le_sound hbud)
  rw [val_frac _ hFD] at hbud'
  push_cast at hbud'
  have hσ0 : 0 ≤ C.σ := by
    unfold CellD.σ
    have : (C.b : ℝ) ≤ C.a := by exact_mod_cast hba
    have : (0 : ℝ) < C.q := by exact_mod_cast hq
    apply div_nonneg <;> linarith
  have hP64 : (ArbEcon.OrderK.cfg64 C.tn S.tq).P = 64 := rfl
  have e64 : ((2 ^ 64 : ℕ) : ℝ) = (2 : ℝ) ^ (64 : ℕ) := by push_cast; ring
  have hL'' : ((ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc 1
      (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
        (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5))).lhi : ℝ)
      ≤ S.L.val * 2 ^ (ArbEcon.OrderK.cfg64 C.tn S.tq).P := by
    rw [hP64, ← e64]; exact hL'
  have e11 : (2 * ((6 : ℕ) : ℝ) - 1 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
  have hU'' : (C.σ + (2 * ((6 : ℕ) : ℝ) - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ S.U.val ^ 2 := by
    rw [e11]; exact hU'
  have hQ'' : pochNormSq 1 S.hi.val (2 * 6 + 1) ≤ (S.Qr : ℝ) ^ 2 := by
    rw [sq]; push_cast at hQ' ⊢; exact hQ'
  have hcell := H1000Oct.cell_zeta_ne_zero_R (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc C.σ tc rfl rfl 6
    S.N 5 (by norm_num) hN2 _ _ i1 i2 C.rn C.rd S.FN S.FD hchk S.R.val S.L.val S.lo.val S.U.val
    S.hi.val (S.Qr : ℝ) S.r0 hrR' hL'' hRL' (val_pos hlo) hta' hσ0 (val_nonneg hU0) hU''
    (Nat.cast_nonneg _) hQ'' hr0 (by rw [sq]; exact hr0N) hbud'
  -- the rectangle is inside the disc
  have hw0' := le_sound hw0
  have hw1' := le_sound hw1
  have hh0' := le_sound hh0
  have hh1' := le_sound hh1
  have hwr' := le_sound hwr
  rw [val_qabs, val_sub, C.val_σQ hq] at hw0' hw1'
  rw [val_qabs, val_sub, val_tQ] at hh0' hh1'
  rw [val_add, val_npow, val_npow, val_npow, val_frac _ hrd] at hwr'
  have hxw : |x - C.σ| ≤ C.w.val := H1000Oct.abs_sub_le_of_mem_uIcc hx hw0' hw1'
  have hyh : |y - tc| ≤ C.hh.val :=
    H1000Oct.abs_sub_le_of_mem_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hy0, hy1⟩)) hh0' hh1'
  have hr0' : (0 : ℝ) ≤ (C.rn : ℝ) / C.rd := by positivity
  have hdisc := ArbEcon.Off.dist_le_of_box x y C.σ tc C.w.val C.hh.val ((C.rn : ℝ) / C.rd) hxw hyh hr0'
    (by push_cast at hwr' ⊢; exact hwr')
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  exact hcell _ hdisc (by rw [him]; exact hy0) (by rw [him]; exact hy1) (by rw [hre]; exact hxh)
    (by rw [hre]; exact hx1)

/-! ## D. THE SLAB -/

/-- Any `x ∈ [f 0, f m]` (`m ≥ 1`) lies in some `[f j, f (j+1)]`, `j < m` (no monotonicity needed). -/
theorem exists_col (f : ℕ → ℝ) (x : ℝ) : ∀ m : ℕ, 1 ≤ m → f 0 ≤ x → x ≤ f m →
    ∃ j, j < m ∧ f j ≤ x ∧ x ≤ f (j + 1)
  | 0, hm, _, _ => absurd hm (by norm_num)
  | m + 1, _, h0, hm => by
    by_cases hx : x ≤ f m
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact ⟨0, by norm_num, h0, hm⟩
      · obtain ⟨j, hj, h1, h2⟩ := exists_col f x m h h0 hx
        exact ⟨j, by omega, h1, h2⟩
    · push Not at hx
      exact ⟨m, by omega, hx.le, hm⟩

/-- **The slab checker**: the slab-level facts and every cell. -/
noncomputable def slabOK (S : SlabD) : Bool :=
  slabHeadOK S && (List.range S.m).all (cellOK S)

/-- **Soundness of the slab checker**: the slab `(0, 1) × [lo, hi]` is zero-free. -/
theorem slabOK_sound (S : SlabD) (h : slabOK S = true) : EdgeClearGlue.SlabClear S.lo.val S.hi.val := by
  simp only [slabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hS, hcells⟩ := h
  have hS' := hS
  simp only [slabHeadOK, Bool.and_eq_true, Nat.ble_eq] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, _⟩, hx0⟩, hxm⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hS'
  have hx0' : (S.xs 0).val = 1 / 2 := by rw [eqB_sound hx0, val_frac _ (by norm_num)]; norm_num
  have hxm' : (S.xs S.m).val = 1 := by rw [eqB_sound hxm, val_ofNat]; norm_num
  apply ArbEcon.Off.slabClear_of_right_half
  intro x y hx0'' hx1 hy0 hy1
  obtain ⟨j, hj, h1, h2⟩ := exists_col (fun j => (S.xs j).val) x S.m hm (by rw [hx0']; exact hx0'')
    (by rw [hxm']; exact hx1.le)
  exact cellOK_sound S hS j (hcells j hj) x y (Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)) hy0 hy1 hx0''
    hx1.le

end Arb4
