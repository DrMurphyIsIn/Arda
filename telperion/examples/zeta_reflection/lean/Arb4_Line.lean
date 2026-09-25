/-  Arb4_Line.lean -- lane Arb4 (h1000 compaction): the on-line sign certificate of a Turing band
    with the evaluator states recomputed in the kernel (brick K4 in EM form, `H1000Line`).

    The band modules `H1000Line_Bxx` of lane h1000-prep store, per grid point, the two evaluator
    states after `N - 1` and `N` Dirichlet terms as computable definitions (compiled to IR: about
    20 KB of olean per point).  Here a point is `mkPt tn tq N Q r k nl m pos`, whose states ARE the
    evaluator runs (`ArbEcon.run`), so `H1000Line.ptCheck (mkPt …)` recomputes them, and a whole band
    is ONE Boolean `bandB` run by ONE `decide +kernel`:

      * `mkPt`            -- a point record with recomputed states;
      * `allB`, `allB_sound` -- every point of a list passes `H1000Line.ptCheck`;
      * `bandB`, `bandB_sound` -- the band: `allB` and `H1000Line.bandOk` give the band's verbatim
                             `hLine` (`n` increasing zeros of `completedRiemannZeta` on the critical
                             line in `[T0, T1]`) through `H1000Line.band_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic and the intermediate value theorem; nothing here bears on the Riemann Hypothesis.
-/
import H1000Line

namespace Arb4

/-- A grid point at `t = tn / 2^tq` whose evaluator states are the evaluator runs themselves (after
    `N - 1` and `N` terms), so the kernel recomputes them in `ptCheck`. -/
noncomputable def mkPt (tn tq N Q r k nl m : ℕ) (pos : Bool) : H1000Line.LinePt :=
  ⟨tn, tq, N,
    ArbEcon.run (ArbEcon.OrderK.cfg64 tn tq) (N - 2) (ArbEcon.St.init (ArbEcon.OrderK.cfg64 tn tq)),
    ArbEcon.run (ArbEcon.OrderK.cfg64 tn tq) 1
      (ArbEcon.run (ArbEcon.OrderK.cfg64 tn tq) (N - 2) (ArbEcon.St.init (ArbEcon.OrderK.cfg64 tn tq))),
    Q, r, k, nl, m, pos⟩

/-- Every point passes `ptCheck`. -/
noncomputable def allB : List H1000Line.LinePt → Bool
  | [] => true
  | p :: ps => H1000Line.ptCheck p && allB ps

theorem allB_sound : ∀ ps : List H1000Line.LinePt, allB ps = true → H1000Line.AllOk ps
  | [], _ => H1000Line.AllOk.nil
  | p :: ps, h => by
    have h' : (H1000Line.ptCheck p && allB ps) = true := h
    rw [Bool.and_eq_true] at h'
    exact H1000Line.AllOk.cons h'.1 (allB_sound ps h'.2)

/-- **The band checker**: every point, and the band conditions (order, edges, alternation). -/
noncomputable def bandB (T0n T0d T1n T1d n : ℕ) (ps : List H1000Line.LinePt) : Bool :=
  allB ps && H1000Line.bandOk T0n T0d T1n T1d n ps

/-- **Soundness**: the band's `hLine`. -/
theorem bandB_sound (T0 T1 : ℝ) (T0n T0d T1n T1d n : ℕ) (hT0 : T0 = (T0n : ℝ) / T0d)
    (hT1 : T1 = (T1n : ℝ) / T1d) (ps : List H1000Line.LinePt) (h : bandB T0n T0d T1n T1d n ps = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  have h' : (allB ps && H1000Line.bandOk T0n T0d T1n T1d n ps) = true := h
  rw [Bool.and_eq_true] at h'
  exact H1000Line.band_sound T0 T1 T0n T0d T1n T1d n hT0 hT1 ps (allB_sound ps h'.1) h'.2

/-! ## Points with the states computed ONCE (no `dirOk` comparison) -/

/-- The data of a grid point (the states are the evaluator runs, not data). -/
structure PtD where
  tn : ℕ
  tq : ℕ
  N : ℕ
  Q : ℕ
  r : ℕ
  k : ℕ
  nl : ℕ
  m : ℕ
  pos : Bool

/-- The point record of `d`, its states the evaluator runs. -/
noncomputable def PtD.pt (d : PtD) : H1000Line.LinePt := mkPt d.tn d.tq d.N d.Q d.r d.k d.nl d.m d.pos

open H1000Line in
/-- `H1000Line.ptCheck` without the `dirOk` comparisons: for a point whose states ARE the evaluator
    runs there is nothing to compare, and the kernel evaluates every run once. -/
noncomputable def ptCheckC (p : H1000Line.LinePt) : Bool :=
  decide (2 ≤ p.N) && (remP p).1 && decide (0 < (remP p).2.2) && phaseOk p.tn p.tq p.k &&
    decide (0 ≤ thLo p) &&
    (bif p.pos then decide (sRad p < sCtr p) else decide (sCtr p + sRad p < 0))

open H1000Line in
/-- The conjuncts of `ptCheckC` (extracted by rewriting, as in `H1000Line.ptCheck_spec`). -/
theorem ptCheckC_spec {p : H1000Line.LinePt} (h : ptCheckC p = true) :
    2 ≤ p.N ∧ (remP p).1 = true ∧ 0 < (remP p).2.2 ∧ phaseOk p.tn p.tq p.k = true ∧
      0 ≤ thLo p ∧ (p.pos = true → sRad p < sCtr p) ∧ (p.pos = false → sCtr p + sRad p < 0) := by
  have h' : (((((decide (2 ≤ p.N) && (remP p).1) && decide (0 < (remP p).2.2)) && phaseOk p.tn p.tq p.k)
      && decide (0 ≤ thLo p))
      && (bif p.pos then decide (sRad p < sCtr p) else decide (sCtr p + sRad p < 0))) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hN, hR⟩, hED⟩, hph⟩, hlo0⟩, hs⟩ := h'
  refine ⟨of_decide_eq_true hN, hR, of_decide_eq_true hED, hph, of_decide_eq_true hlo0,
    fun hp => ?_, fun hp => ?_⟩
  · have hs' := hs
    rw [hp, cond_true] at hs'
    exact of_decide_eq_true hs'
  · have hs' := hs
    rw [hp, cond_false] at hs'
    exact of_decide_eq_true hs'

/-- The evaluator invariants of a point's states (they are the runs, `ArbEcon.run_sound`). -/
theorem pt_inv (d : PtD) (hN : 2 ≤ d.N) :
    ArbEcon.Inv (ArbEcon.OrderK.cfg64 d.pt.tn d.pt.tq) (H1000Line.tOf d.pt) (d.pt.N - 1) d.pt.s1 ∧
      ArbEcon.Inv (ArbEcon.OrderK.cfg64 d.pt.tn d.pt.tq) (H1000Line.tOf d.pt) d.pt.N d.pt.s2 := by
  have hv := ArbEcon.OrderK.valid64 d.tn d.tq (H1000Line.tOf d.pt) rfl
  have i0 := ArbEcon.inv_init (ArbEcon.OrderK.cfg64 d.tn d.tq) (H1000Line.tOf d.pt) hv.one_eq
  have i1 := ArbEcon.run_sound _ _ 9 hv (d.N - 2) 1 _ i0
  rw [show 1 + (d.N - 2) = d.N - 1 by omega] at i1
  have i2 := ArbEcon.run_sound _ _ 9 hv 1 (d.N - 1) _ i1
  rw [show d.N - 1 + 1 = d.N by omega] at i2
  exact ⟨i1, i2⟩

open H1000Line Filter Topology in
/-- **Soundness of the point checker** (as `H1000Line.ptCheck_sound`): the claimed sign of
    `gLine t` is the true one. -/
theorem ptCheckC_sound (d : PtD) (h : ptCheckC d.pt = true) :
    (d.pt.pos = true → 0 < XiLineZeros.gLine (tOf d.pt)) ∧
      (d.pt.pos = false → XiLineZeros.gLine (tOf d.pt) < 0) := by
  obtain ⟨hN, hR, hED, hph, hlo0, hpos, hneg⟩ := ptCheckC_spec h
  obtain ⟨h1, h2⟩ := pt_inv d hN
  obtain ⟨hW, hX, hY⟩ := zball_sound d.pt hN h1 h2 hR hED
  obtain ⟨_, _, _, htn, _⟩ := phaseOk_spec hph
  have htpos : 0 < tOf d.pt := by
    have : (0 : ℝ) < d.pt.tn := by exact_mod_cast htn
    unfold tOf; positivity
  obtain ⟨Λ, hΛ, hMpos, hgl⟩ := gLine_eq_mag_mul d.pt htpos
  obtain ⟨hc, hsn⟩ := trig_phase d.pt hph hlo0 Λ hΛ
  have hSW := s_ball d.pt Λ hc hsn hX hY
  set S := Real.cos (phiOf d.pt Λ) * (riemannZeta (ArbEcon.sOf (tOf d.pt))).re
    - Real.sin (phiOf d.pt Λ) * (riemannZeta (ArbEcon.sOf (tOf d.pt))).im with hS
  have hKpos : (0 : ℝ) < 2 ^ 64 * (zW d.pt : ℝ) := by positivity
  have eK : S * 2 ^ 64 * (zW d.pt : ℝ) = S * (2 ^ 64 * (zW d.pt : ℝ)) := by ring
  rw [abs_le] at hSW
  constructor
  · intro hp
    have hs' : ((sRad d.pt : ℤ) : ℝ) < ((sCtr d.pt : ℤ) : ℝ) := by exact_mod_cast hpos hp
    have hSpos : 0 * (2 ^ 64 * (zW d.pt : ℝ)) < S * (2 ^ 64 * (zW d.pt : ℝ)) := by
      rw [zero_mul, ← eK]; linarith [hSW.1]
    have : 0 < S := lt_of_mul_lt_mul_right hSpos hKpos.le
    rw [hgl]; exact mul_pos hMpos this
  · intro hp
    have hs' : ((sCtr d.pt : ℤ) : ℝ) + ((sRad d.pt : ℤ) : ℝ) < 0 := by exact_mod_cast hneg hp
    have hSneg : S * (2 ^ 64 * (zW d.pt : ℝ)) < 0 * (2 ^ 64 * (zW d.pt : ℝ)) := by
      rw [zero_mul, ← eK]; linarith [hSW.2]
    have : S < 0 := lt_of_mul_lt_mul_right hSneg hKpos.le
    rw [hgl]; exact mul_neg_of_pos_of_neg hMpos this

/-- **The band checker** (states computed once per point). -/
noncomputable def bandC (T0n T0d T1n T1d n : ℕ) (ds : List PtD) : Bool :=
  ds.all (fun d => ptCheckC d.pt) && H1000Line.bandOk T0n T0d T1n T1d n (ds.map PtD.pt)

/-- Chunks of a band are checked separately (one `decide +kernel` each) and appended. -/
theorem allC_append {l1 l2 : List PtD} (h1 : l1.all (fun d => ptCheckC d.pt) = true)
    (h2 : l2.all (fun d => ptCheckC d.pt) = true) : (l1 ++ l2).all (fun d => ptCheckC d.pt) = true := by
  rw [List.all_append, h1, h2]; rfl

theorem bandC_of {T0n T0d T1n T1d n : ℕ} {ds : List PtD} (h1 : ds.all (fun d => ptCheckC d.pt) = true)
    (h2 : H1000Line.bandOk T0n T0d T1n T1d n (ds.map PtD.pt) = true) : bandC T0n T0d T1n T1d n ds = true := by
  unfold bandC; rw [h1, h2]; rfl

open H1000Line in
/-- **Soundness of the band checker**: the band's verbatim `hLine` (as `H1000Line.band_sound`). -/
theorem bandC_sound (T0 T1 : ℝ) (T0n T0d T1n T1d n : ℕ) (hT0 : T0 = (T0n : ℝ) / T0d)
    (hT1 : T1 = (T1n : ℝ) / T1d) (ds : List PtD) (h : bandC T0n T0d T1n T1d n ds = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  have h' : (ds.all (fun d => ptCheckC d.pt) && bandOk T0n T0d T1n T1d n (ds.map PtD.pt)) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨hall, hb⟩ := h'
  set ps := ds.map PtD.pt with hps
  have hsgn : ∀ (i : ℕ) (hi : i < ps.length),
      ((ps[i]'hi).pos = true → 0 < XiLineZeros.gLine (tOf (ps[i]'hi))) ∧
        ((ps[i]'hi).pos = false → XiLineZeros.gLine (tOf (ps[i]'hi)) < 0) := by
    intro i hi
    have hi' : i < ds.length := by rw [hps, List.length_map] at hi; exact hi
    have hd := List.all_eq_true.mp hall (ds[i]'hi') (List.getElem_mem hi')
    have e : ps[i]'hi = (ds[i]'hi').pt := by simp [hps]
    rw [e]
    exact ptCheckC_sound (ds[i]'hi') hd
  have hb' : (((((decide (ps.length = n + 1) && chainOk ps) && decide (0 < T0d)) && decide (0 < T1d))
      && firstGe T0n T0d ps) && lastLe T1n T1d ps) = true := hb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb'
  obtain ⟨⟨⟨⟨⟨hlen, hch⟩, hd0⟩, hd1⟩, hfirst⟩, hlast⟩ := hb'
  have hlen' : decide (ps.length = n + 1) = true := hlen
  have hd0' : decide (0 < T0d) = true := hd0
  have hd1' : decide (0 < T1d) = true := hd1
  have hL := of_decide_eq_true hlen'
  have hD0 := of_decide_eq_true hd0'
  have hD1 := of_decide_eq_true hd1'
  let pt : Fin (n + 1) → ℝ := fun i => tOf (ps[i.1]'(by rw [hL]; exact i.2))
  apply ZetaReflection.alternating_signs_chain T0 T1 n pt
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    have h := chainOk_get ps hch i.1 (by rw [hL]; omega)
    exact tlt_sound h.1
  · rw [hT0]
    exact firstGe_sound T0n T0d hD0 ps (by rw [hL]; omega) hfirst
  · rw [hT1]
    exact lastLe_sound T1n T1d hD1 ps hlast n hL.symm
  · intro i
    have hc := chainOk_get ps hch i.1 (by rw [hL]; omega)
    have hA := hsgn i.1 (by rw [hL]; omega)
    have hB := hsgn (i.1 + 1) (by rw [hL]; omega)
    show XiLineZeros.gLine (tOf (ps[i.1]'(by rw [hL]; omega)))
        * XiLineZeros.gLine (tOf (ps[i.1 + 1]'(by rw [hL]; omega))) < 0
    rcases Bool.eq_false_or_eq_true (ps[i.1]'(by rw [hL]; omega)).pos with ha | ha
    · have hb2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos = false := by
        have := hc.2; rw [ha] at this; cases h2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos
        · rfl
        · rw [h2] at this; exact absurd rfl this
      exact mul_neg_of_pos_of_neg (hA.1 ha) (hB.2 hb2)
    · have hb2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos = true := by
        have := hc.2; rw [ha] at this; cases h2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos
        · rw [h2] at this; exact absurd rfl this
        · rfl
      exact mul_neg_of_neg_of_pos (hA.2 ha) (hB.1 hb2)

end Arb4
