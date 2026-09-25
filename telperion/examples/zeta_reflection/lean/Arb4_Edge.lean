/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/
import Arb4_Side

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. Small Boolean helpers -/

/-- `a = b` as rationals (both inequalities). -/
def eqB (a b : Q) : Bool := le a b && le b a

theorem eqB_sound {a b : Q} (h : eqB a b = true) : a.val = b.val := by
  simp only [eqB, Bool.and_eq_true] at h
  exact le_antisymm (le_sound h.1) (le_sound h.2)

/-- `|x - σ| ≤ r`. -/
def inRad (x : Q) (P : PieceD) : Bool := le (qabs (sub x P.σQ)) P.rQ

theorem inRad_sound {x : Q} {P : PieceD} (hq : 1 ≤ P.q) (hrd : 1 ≤ P.rd) (h : inRad x P = true) :
    |x.val - P.σ| ≤ (P.rn : ℝ) / P.rd := by
  have h' := le_sound h
  rw [val_qabs, val_sub, P.val_σQ hq, P.val_rQ hrd] at h'
  exact h'

/-! ## B. The evaluator invariants of a piece center -/

theorem runs_inv (tn tq N : ℕ) (P : PieceD) (hN : 2 ≤ N) (hq : 1 ≤ P.q) :
    ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 tn tq) P.σ ((tn : ℝ) / 2 ^ tq) (N - 1)
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
          (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5)) ∧
      ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 tn tq) P.σ ((tn : ℝ) / 2 ^ tq) N
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc 1
          (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
            (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5))) := by
  set c := ArbEcon.OrderK.cfg64 tn tq with hc
  set t : ℝ := (tn : ℝ) / 2 ^ tq with ht
  have hv : ArbEcon.Valid c t 9 := ArbEcon.OrderK.valid64 tn tq t rfl
  have ho : ArbEcon.Off.OValid c P.oc P.σ := ⟨rfl, hq, rfl⟩
  have i0 := ArbEcon.Off.initO_sound c P.σ t 5 hv.one_eq
  have i1 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho (N - 2) 1 _ i0
  rw [show 1 + (N - 2) = N - 1 by omega] at i1
  have i2 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho 1 (N - 1) _ i1
  rw [show N - 1 + 1 = N by omega] at i2
  exact ⟨i1, i2⟩

/-! ## C. Endpoint enclosures and their corner slopes -/

/-- One corner `(a, b)` of an endpoint box in octant `(α, β)`: `X = α a + β b > 0` and
    `qlo X ≤ Y ≤ qhi X` for `Y = α b - β a`. -/
def cornerOK (al be : ℤ) (a b qlo qhi : Q) : Bool :=
  lt (ofInt 0) (add (mul (ofInt al) a) (mul (ofInt be) b)) &&
    le (mul qlo (add (mul (ofInt al) a) (mul (ofInt be) b))) (sub (mul (ofInt al) b) (mul (ofInt be) a)) &&
    le (sub (mul (ofInt al) b) (mul (ofInt be) a)) (mul qhi (add (mul (ofInt al) a) (mul (ofInt be) b)))

theorem cornerOK_sound {al be : ℤ} {a b qlo qhi : Q} (h : cornerOK al be a b qlo qhi = true) :
    0 < (al : ℝ) * a.val + be * b.val ∧
      qlo.val * ((al : ℝ) * a.val + be * b.val) ≤ (al : ℝ) * b.val - be * a.val ∧
      (al : ℝ) * b.val - be * a.val ≤ qhi.val * ((al : ℝ) * a.val + be * b.val) := by
  simp only [cornerOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' := lt_sound h1
  have h2' := le_sound h2
  have h3' := le_sound h3
  simp only [val_add, val_mul, val_sub, val_ofInt] at h1' h2' h3'
  push_cast at h1'
  exact ⟨h1', h2', h3'⟩

/-- An endpoint enclosure at the center of piece `P` (the evaluator run recomputed): the point box
    `[reLo, reHi] × [imLo, imHi] / D` by `ArbEcon.Off.checkG`, and its four corners in the octant of
    `P` with slopes in `[qlo, qhi]`. -/
noncomputable def boxOK (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 D && !s1.acc.isEmpty && !sN.acc.isEmpty &&
    ArbEcon.Off.checkG c P.oc 6 N (s1.acc.headD ArbEcon.Off.Acc.zero)
      (sN.acc.headD ArbEcon.Off.Acc.zero) D reLo reHi imLo imHi Qp Rn Rd &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imHi D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imHi D) qlo qhi

theorem boxOK_sound (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) (h : boxOK tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi = true) :
    ArgHoriz.InBox (riemannZeta ((P.σ : ℂ) + (((tn : ℝ) / 2 ^ tq : ℝ) : ℂ) * I))
        (frac reLo D).val (frac reHi D).val (frac imLo D).val (frac imHi D).val ∧
      ∀ a ∈ ({(frac reLo D).val, (frac reHi D).val} : Set ℝ),
        ∀ b ∈ ({(frac imLo D).val, (frac imHi D).val} : Set ℝ),
        0 < (ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b ∧
          qlo.val * ((ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b)
            ≤ (ArgHoriz.octA P.kk : ℝ) * b - ArgHoriz.octB P.kk * a ∧
          (ArgHoriz.octA P.kk : ℝ) * b - ArgHoriz.octB P.kk * a
            ≤ qhi.val * ((ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b) := by
  simp only [boxOK, Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hq⟩, hD⟩, hne1⟩, hne2⟩, hG⟩, c00⟩, c01⟩, c10⟩, c11⟩ := h
  obtain ⟨i1, i2⟩ := runs_inv tn tq N P hN hq
  have hbox := H1000Oct.inBox_of_checkG (ArbEcon.OrderK.cfg64 tn tq) P.oc P.σ ((tn : ℝ) / 2 ^ tq)
    rfl rfl 6 N _ _ i1 i2 hne1 hne2 D reLo reHi imLo imHi Qp Rn Rd hG
  have hv : ∀ z : ℤ, (frac z D).val = (z : ℝ) / (D : ℝ) := fun z => val_frac z hD
  refine ⟨?_, ?_⟩
  · rw [hv, hv, hv, hv]; exact hbox
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact cornerOK_sound c00
    · exact cornerOK_sound c01
    · exact cornerOK_sound c10
    · exact cornerOK_sound c11

/-! ## D. The two final inequalities -/

/-- Rational lower bound of `arctan q` (`ArgHoriz.atanLo`). -/
def atanLoQ (q : Q) : Q := if 0 ≤ q.n then sub q (div (npow q 3) (ofNat 3)) else q

/-- Rational upper bound of `arctan q` (`ArgHoriz.atanHi`). -/
def atanHiQ (q : Q) : Q := if 0 ≤ q.n then q else sub q (div (npow q 3) (ofNat 3))

theorem val_nonneg_iff (q : Q) : 0 ≤ q.val ↔ 0 ≤ q.n := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : q.val < 0 := by
      have hn' : (q.n : ℝ) < 0 := by exact_mod_cast hn
      exact div_neg_of_neg_of_pos hn' (den_pos q)
    linarith
  · exact val_nonneg

theorem val_atanLoQ (q : Q) : (atanLoQ q).val = ArgHoriz.atanLo q.val := by
  unfold atanLoQ ArgHoriz.atanLo
  by_cases h : 0 ≤ q.n
  · rw [if_pos h, if_pos ((val_nonneg_iff q).mpr h), val_sub, val_div _ (by norm_num [ofNat]),
      val_npow, val_ofNat]
    push_cast; ring
  · rw [if_neg h, if_neg (fun h' => h ((val_nonneg_iff q).mp h'))]

theorem val_atanHiQ (q : Q) : (atanHiQ q).val = ArgHoriz.atanHi q.val := by
  unfold atanHiQ ArgHoriz.atanHi
  by_cases h : 0 ≤ q.n
  · rw [if_pos h, if_pos ((val_nonneg_iff q).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((val_nonneg_iff q).mp h')), val_sub,
      val_div _ (by norm_num [ofNat]), val_npow, val_ofNat]
    push_cast; ring

/-- The `π` bound that makes `dk · π` smallest (`3.141592 < π < 3.141593`). -/
def piL (dk : ℤ) : Q := if 0 ≤ dk then frac 3141592 1000000 else frac 3141593 1000000

/-- The `π` bound that makes `dk · π` largest. -/
def piH (dk : ℤ) : Q := if 0 ≤ dk then frac 3141593 1000000 else frac 3141592 1000000

theorem piL_le (dk : ℤ) : (dk : ℝ) * (piL dk).val ≤ (dk : ℝ) * Real.pi := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  unfold piL
  by_cases h : 0 ≤ dk
  · rw [if_pos h, val_frac _ (by norm_num)]
    have hd : (0 : ℝ) ≤ dk := by exact_mod_cast h
    apply mul_le_mul_of_nonneg_left _ hd
    norm_num at h1 ⊢; linarith
  · rw [if_neg h, val_frac _ (by norm_num)]
    have hd : (dk : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    apply mul_le_mul_of_nonpos_left _ hd
    norm_num at h2 ⊢; linarith

theorem le_piH (dk : ℤ) : (dk : ℝ) * Real.pi ≤ (dk : ℝ) * (piH dk).val := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  unfold piH
  by_cases h : 0 ≤ dk
  · rw [if_pos h, val_frac _ (by norm_num)]
    have hd : (0 : ℝ) ≤ dk := by exact_mod_cast h
    apply mul_le_mul_of_nonneg_left _ hd
    norm_num at h2 ⊢; linarith
  · rw [if_neg h, val_frac _ (by norm_num)]
    have hd : (dk : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    apply mul_le_mul_of_nonpos_left _ hd
    norm_num at h1 ⊢; linarith

/-- `Lo ≤ dk π/4 + atanLo qlo1 - atanHi qhi0` with `π` replaced by its safe rational bound. -/
def finalLoOK (dk : ℤ) (qhi0 qlo1 Lo : Q) : Bool :=
  le Lo (sub (add (div (mul (ofInt dk) (piL dk)) (ofNat 4)) (atanLoQ qlo1)) (atanHiQ qhi0))

/-- `dk π/4 + atanHi qhi1 - atanLo qlo0 ≤ Hi` with `π` replaced by its safe rational bound. -/
def finalHiOK (dk : ℤ) (qlo0 qhi1 Hi : Q) : Bool :=
  le (sub (add (div (mul (ofInt dk) (piH dk)) (ofNat 4)) (atanHiQ qhi1)) (atanLoQ qlo0)) Hi

theorem finalLo_sound {dk : ℤ} {qhi0 qlo1 Lo : Q} (h : finalLoOK dk qhi0 qlo1 Lo = true) :
    Lo.val ≤ (dk : ℝ) * Real.pi / 4 + Real.arctan qlo1.val - Real.arctan qhi0.val := by
  have h' := le_sound h
  rw [val_sub, val_add, val_div _ (by norm_num [ofNat]), val_mul, val_ofInt, val_ofNat,
    val_atanLoQ, val_atanHiQ] at h'
  have a1 := ArgHoriz.atanLo_le qlo1.val
  have a2 := ArgHoriz.le_atanHi qhi0.val
  have p := piL_le dk
  push_cast at h'
  linarith

theorem finalHi_sound {dk : ℤ} {qlo0 qhi1 Hi : Q} (h : finalHiOK dk qlo0 qhi1 Hi = true) :
    (dk : ℝ) * Real.pi / 4 + Real.arctan qhi1.val - Real.arctan qlo0.val ≤ Hi.val := by
  have h' := le_sound h
  rw [val_sub, val_add, val_div _ (by norm_num [ofNat]), val_mul, val_ofInt, val_ofNat,
    val_atanLoQ, val_atanHiQ] at h'
  have a1 := ArgHoriz.le_atanHi qhi1.val
  have a2 := ArgHoriz.atanLo_le qlo0.val
  have p := le_piH dk
  push_cast at h'
  linarith

/-! ## E. THE EDGE -/

/-- The certificate data of one horizontal edge `[2, -1] + i t`, `t = tn / 2^tq`. -/
structure EdgeD where
  tn : ℕ
  tq : ℕ
  /-- EM cut and log bound `L ≥ log N` of every piece -/
  N : ℕ
  L : Q
  /-- `m` pieces; piece `j` (`pc j`) covers `[x (j+1), x j]`; `x 0 = 2`, `x m = -1` -/
  m : ℕ
  x : ℕ → Q
  pc : ℕ → PieceD
  /-- the endpoint box at `x = 2` (center of piece 0) and its corner slopes -/
  D0 : ℕ
  reLo0 : ℤ
  reHi0 : ℤ
  imLo0 : ℤ
  imHi0 : ℤ
  Qp0 : ℕ
  Rn0 : ℕ
  Rd0 : ℕ
  qlo0 : Q
  qhi0 : Q
  /-- the endpoint box at `x = -1` (center of piece `m - 1`) and its corner slopes -/
  D1 : ℕ
  reLo1 : ℤ
  reHi1 : ℤ
  imLo1 : ℤ
  imHi1 : ℤ
  Qp1 : ℕ
  Rn1 : ℕ
  Rd1 : ℕ
  qlo1 : Q
  qhi1 : Q
  /-- the certified enclosure of the argument change -/
  Lo : Q
  Hi : Q

namespace EdgeD

/-- The height `t = tn / 2^tq`. -/
noncomputable def T (E : EdgeD) : ℝ := (E.tn : ℝ) / 2 ^ E.tq

/-- The octant certificate of the edge. -/
noncomputable def cert (E : EdgeD) : ArgHoriz.OctCert := ⟨E.m, fun j => (E.x j).val, fun j => (E.pc j).kk⟩

end EdgeD

/-- **The edge checker**: every piece (`pieceOK`, with both breakpoints inside its radius), the
    label steps, the two endpoint boxes with their corners, and the final enclosure. -/
noncomputable def edgeOK (E : EdgeD) : Bool :=
  Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
    (List.range E.m).all (fun j => pieceOK E.tn E.tq E.N E.L (E.pc j) &&
      inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)) &&
    (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
    eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1)) &&
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 &&
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 &&
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo &&
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi

set_option maxHeartbeats 1000000 in
/-- **Soundness of the edge checker**: the horizontal argument change of `ζ` along `[2, -1] + i t`
    lies in `[Lo, Hi]`. -/
theorem edgeOK_sound (E : EdgeD) (h : edgeOK E = true) :
    DiffractionCore.argChangeHoriz riemannZeta E.T 2 (-1) ∈ Set.Icc E.Lo.val E.Hi.val := by
  simp only [edgeOK, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, htn⟩, hx0⟩, hxm⟩, hpcs⟩, hsteps⟩, hc0⟩, hc1⟩, hb0⟩, hb1⟩, hlo⟩, hhi⟩ := h
  have hT : E.T ≠ 0 := by
    have : (0 : ℝ) < E.tn := by exact_mod_cast htn
    unfold EdgeD.T; positivity
  -- the pieces
  have hpc : ∀ j, j < E.m → pieceOK E.tn E.tq E.N E.L (E.pc j) = true ∧
      inRad (E.x j) (E.pc j) = true ∧ inRad (E.x (j + 1)) (E.pc j) = true := by
    intro j hj
    have := hpcs j hj
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- piece side facts (q ≥ 1, rd ≥ 1) from the piece checker
  have hqr : ∀ j, j < E.m → 1 ≤ (E.pc j).q ∧ 1 ≤ (E.pc j).rd := by
    intro j hj
    have hp := (hpc j hj).1
    simp only [pieceOK, Bool.and_eq_true, Nat.ble_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hq⟩, hrd⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hp
    exact ⟨hq, hrd⟩
  have hnc : E.cert.NoCross riemannZeta E.T := by
    intro j hj x hx
    obtain ⟨hP, hr0, hr1⟩ := hpc j hj
    obtain ⟨hq, hrd⟩ := hqr j hj
    exact pieceOK_sound E.tn E.tq E.N E.L (E.pc j) hP x
      (H1000Oct.abs_sub_le_of_mem_uIcc hx (inRad_sound hq hrd hr0) (inRad_sound hq hrd hr1))
  have hstep : E.cert.StepOK := by
    intro j hj
    exact hsteps j (by change j + 1 < E.m at hj; omega)
  have hp0 : E.cert.p 0 = 2 := by
    show (E.x 0).val = 2
    rw [eqB_sound hx0, val_ofNat]; norm_num
  have hpm : E.cert.p E.cert.m = -1 := by
    show (E.x E.m).val = -1
    rw [eqB_sound hxm, val_ofInt]; norm_num
  -- the endpoint boxes
  obtain ⟨hw0, hS0⟩ := boxOK_sound E.tn E.tq E.N (E.pc 0) _ _ _ _ _ _ _ _ _ _ hb0
  obtain ⟨hw1, hS1⟩ := boxOK_sound E.tn E.tq E.N (E.pc (E.m - 1)) _ _ _ _ _ _ _ _ _ _ hb1
  have hσ0 : (E.pc 0).σ = 2 := by
    rw [← (E.pc 0).val_σQ (hqr 0 (by omega)).1, eqB_sound hc0, val_ofNat]; norm_num
  have hσ1 : (E.pc (E.m - 1)).σ = -1 := by
    rw [← (E.pc (E.m - 1)).val_σQ (hqr (E.m - 1) (by omega)).1, eqB_sound hc1, val_ofInt]; norm_num
  rw [hσ0] at hw0
  rw [hσ1] at hw1
  have hw0' : ArgHoriz.InBox (riemannZeta (((2 : ℝ) : ℂ) + ((E.T : ℝ) : ℂ) * I))
      (frac E.reLo0 E.D0).val (frac E.reHi0 E.D0).val (frac E.imLo0 E.D0).val (frac E.imHi0 E.D0).val :=
    hw0
  have hw1' : ArgHoriz.InBox (riemannZeta (((-1 : ℝ) : ℂ) + ((E.T : ℝ) : ℂ) * I))
      (frac E.reLo1 E.D1).val (frac E.reHi1 E.D1).val (frac E.imLo1 E.D1).val (frac E.imHi1 E.D1).val :=
    hw1
  have hL := finalLo_sound hlo
  have hH := finalHi_sound hhi
  push_cast at hL hH
  exact ArgHoriz.hAH_of_octCert_boxes (T := E.T) (L := E.Lo.val) (H := E.Hi.val) hT E.cert hm hp0 hpm
    hstep hnc hw0' hS0 hw1' hS1 hL hH

end Arb4
