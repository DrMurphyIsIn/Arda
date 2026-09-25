/-  Arb4_Side.lean -- lane Arb4 (h1000 compaction): Boolean kernel checkers, with soundness proved
    once, for the per-piece side conditions of an octant certificate (brick K6c, `H1000Octant`).

    The generated edge modules `H1000Edge_*` of lane h1000-integrate close, per octant piece, an error
    budget, a horizontal remainder bound, a `G` certificate and six scalar conditions by `norm_num`
    (about 400 KB of olean per piece).  Here all of them are ONE Boolean `pieceOK`, run by
    `decide +kernel` on exact rationals (`Arb4_Q`), together with the off-line evaluator run itself
    (the states after `N - 1` and `N` terms are recomputed in the kernel, not stored):

      * `CpQ betaQ emcBQ corrVarQ budgetQ` (+ `val_*`) -- the error budget of
                           `H1000Oct.piece_octX_pos` as a rational, EQUAL to the real one;
      * `pochQ`, `val_pochQ` -- `pochNormSq` as a rational;
      * `PieceD`         -- the certificate data of one piece (center `(a - b)/q`, radius `rn/rd`,
                           octant `kk`, budget `FN/FD`, and the rationals of the side conditions);
      * `gOK remOK geomOK budgetOK` and their soundness -- the `G` bound, the order-13 remainder on the
                           piece, the scalar geometry, the budget;
      * `pieceOK`, `pieceOK_sound` -- THE PIECE: `pieceOK tn tq N L P = true` gives
                           `0 < octX kk (ζ(x + i t))` for every `x` with `|x - σ| ≤ r`, `t = tn / 2^tq`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic along finitely many segments; nothing here bears on the Riemann Hypothesis.
-/
import Arb4_Q
import H1000Octant

open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The error budget as a rational -/

/-- `C_p = (p + 2) / ((p + 1)! (p + 1))`. -/
def CpQ (p : ℕ) : Q := frac ((p + 2 : ℕ) : ℤ) ((p + 1)! * (p + 1))

theorem val_CpQ (p : ℕ) : (CpQ p).val = ArbEcon.Off.Cp p := by
  have hd : 1 ≤ (p + 1)! * (p + 1) := Nat.mul_pos (Nat.factorial_pos _) (Nat.succ_pos _)
  rw [CpQ, val_frac _ hd]
  unfold ArbEcon.Off.Cp
  push_cast
  ring

/-- `|B_{i+2}| / (i+2)! = |betaN i| / Lβ` as a rational. -/
def betaQ (i : ℕ) : Q := frac ((ArbEcon.OrderK.betaN i).natAbs : ℤ) ArbEcon.OrderK.Lbeta

theorem val_betaQ (i : ℕ) :
    (betaQ i).val = |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) := by
  have hL : 1 ≤ ArbEcon.OrderK.Lbeta := by unfold ArbEcon.OrderK.Lbeta; norm_num
  rw [betaQ, val_frac _ hL, Int.natCast_natAbs, Int.cast_abs]

/-- `N / a + 1/2 + Σ_{i < 2K-1} |B_{i+2}|/(i+2)! U^(i+1) / N^(i+1)` (the bound `emcB`). -/
def emcBQ (K N : ℕ) (a U : Q) : Q :=
  add (add (div (ofNat N) a) (frac 1 2))
    (sumQ (fun i => mul (betaQ i) (div (npow U (i + 1)) (ofNat (N ^ (i + 1))))) (2 * K - 1))

theorem val_emcBQ (K N : ℕ) (hK : K ≤ 6) (hN : 0 < N) (a U : Q) (ha : 0 < a.n) :
    (emcBQ K N a U).val = ArbEcon.Off.emcB K N a.val U.val := by
  rw [H1000Oct.emcB_betaN K N hK]
  unfold emcBQ
  rw [val_add, val_add, val_div _ ha, val_ofNat, val_frac _ (by norm_num), val_sumQ]
  congr 1
  · norm_num
  · apply Finset.sum_congr rfl
    intro i _
    have hNp : (0 : ℤ) < ((N ^ (i + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hN _
    rw [val_mul, val_betaQ, val_div _ hNp, val_npow, val_ofNat]
    push_cast
    ring

/-- `N r / a² + Σ_{i < 2K-1} |B_{i+2}|/(i+2)! ((U + r)^(i+1) - U^(i+1)) / N^(i+1)` (`corrVar`). -/
def corrVarQ (K N : ℕ) (r a U : Q) : Q :=
  add (div (mul (ofNat N) r) (npow a 2))
    (sumQ (fun i => mul (betaQ i) (div (sub (npow (add U r) (i + 1)) (npow U (i + 1)))
      (ofNat (N ^ (i + 1))))) (2 * K - 1))

theorem npow_two_n_pos {a : Q} (ha : 0 < a.n) : 0 < (npow a 2).n := by
  show 0 < 1 * a.n * a.n
  rw [one_mul]
  exact mul_pos ha ha

theorem val_corrVarQ (K N : ℕ) (hK : K ≤ 6) (hN : 0 < N) (r a U : Q) (ha : 0 < a.n) :
    (corrVarQ K N r a U).val = ArbEcon.Off.corrVar K N r.val a.val U.val := by
  rw [H1000Oct.corrVar_betaN K N hK]
  unfold corrVarQ
  rw [val_add, val_div _ (npow_two_n_pos ha), val_mul, val_ofNat, val_npow, val_sumQ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hNp : (0 : ℤ) < ((N ^ (i + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hN _
  rw [val_mul, val_betaQ, val_div _ hNp, val_sub, val_npow, val_npow, val_add, val_ofNat]
  push_cast
  ring

/-- The error budget of `H1000Oct.piece_octX_pos` (order `2K + 1`, Taylor order `p`):
    `G (C_p (R L)^(p+1) ((N - 1) + emcB) + 3 corrVar) + E`. -/
def budgetQ (K N p : ℕ) (G R L a U E : Q) : Q :=
  add (mul G (add (mul (mul (CpQ p) (npow (mul R L) (p + 1)))
      (add (sub (ofNat N) (ofNat 1)) (emcBQ K N a U)))
    (mul (ofNat 3) (corrVarQ K N R a U)))) E

theorem val_budgetQ (K N p : ℕ) (hK : K ≤ 6) (hN : 0 < N) (G R L a U E : Q) (ha : 0 < a.n) :
    (budgetQ K N p G R L a U E).val
      = G.val * (ArbEcon.Off.Cp p * (R.val * L.val) ^ (p + 1)
          * (((N : ℝ) - 1) + ArbEcon.Off.emcB K N a.val U.val)
          + 3 * ArbEcon.Off.corrVar K N R.val a.val U.val) + E.val := by
  unfold budgetQ
  rw [val_add, val_mul, val_add, val_mul, val_mul, val_CpQ, val_npow, val_mul, val_add, val_sub,
    val_ofNat, val_ofNat, val_emcBQ K N hK hN a U ha, val_mul, val_ofNat,
    val_corrVarQ K N hK hN R a U ha]
  push_cast
  ring

/-! ## B. `pochNormSq` as a rational -/

/-- `Π_{j < k} ((σ + j)² + t²)`. -/
def pochQ (σ t : Q) : ℕ → Q
  | 0 => ofNat 1
  | k + 1 => mul (pochQ σ t k) (add (npow (add σ (ofNat k)) 2) (npow t 2))

theorem val_pochQ (σ t : Q) : ∀ k, (pochQ σ t k).val = pochNormSq σ.val t.val k
  | 0 => by simp [pochQ, pochNormSq]
  | k + 1 => by
    rw [pochQ, val_mul, val_pochQ σ t k, val_add, val_npow, val_npow, val_add, val_ofNat,
      pochNormSq]

/-! ## C. The certificate data of one octant piece -/

/-- The height `t = tn / 2^tq` as a rational. -/
def tQ (tn tq : ℕ) : Q := frac (tn : ℤ) (2 ^ tq)

theorem val_tQ (tn tq : ℕ) : (tQ tn tq).val = (tn : ℝ) / 2 ^ tq := by
  rw [tQ, val_frac _ (Nat.one_le_two_pow)]
  push_cast
  ring

/-- The certificate data of ONE octant piece `[σ - r, σ + r]` of a horizontal edge.  Every field is
    an exact integer or rational; nothing is trusted: `pieceOK` re-checks every relation. -/
structure PieceD where
  /-- center `σ = (a - b) / q` -/
  a : ℕ
  b : ℕ
  q : ℕ
  /-- radius `r = rn / rd` -/
  rn : ℕ
  rd : ℕ
  /-- octant label (a continuous lift of the argument, in units of `π/4`) -/
  kk : ℤ
  /-- error budget `F = FN / FD` of the kernel check `checkOct` -/
  FN : ℕ
  FD : ℕ
  /-- distance parameter: `a + r ≤ ‖c - 1‖` -/
  aQ : Q
  /-- `‖c + j‖ ≤ U` for `j < 12` -/
  U : Q
  /-- `G = Gn / Gd ≥ ‖n^(-c)‖`: `Gd^gq N^gb ≤ Gn^gq N^ga`, `ga ≤ gb`, `(ga - gb)/gq ≤ σ` -/
  ga : ℕ
  gb : ℕ
  gq : ℕ
  Gn : ℕ
  Gd : ℕ
  /-- remainder range `[xlo, xhi]`, `xlo = (ea - eb)/eqd`, `|x| ≤ sigs` on it,
      `N^(-xlo) ≤ Rn/Rd` from `Rd^eqd N^eb ≤ Rn^eqd N^ea`, `pochNormSq sigs t 13 ≤ Qr²`,
      and the resulting remainder bound `E` -/
  ea : ℕ
  eb : ℕ
  eqd : ℕ
  Rn : ℕ
  Rd : ℕ
  xhi : Q
  sigs : Q
  Qr : ℕ
  E : Q

namespace PieceD

/-- The center `σ = (a - b) / q`. -/
noncomputable def σ (P : PieceD) : ℝ := ((P.a : ℝ) - P.b) / P.q

def σQ (P : PieceD) : Q := frac ((P.a : ℤ) - P.b) P.q

def rQ (P : PieceD) : Q := frac (P.rn : ℤ) P.rd

def GQ (P : PieceD) : Q := frac (P.Gn : ℤ) P.Gd

def FQ (P : PieceD) : Q := frac (P.FN : ℤ) P.FD

def xloQ (P : PieceD) : Q := frac ((P.ea : ℤ) - P.eb) P.eqd

/-- The off-line evaluator configuration of the piece center (`oneQ = 2^(q P)`, `P = 64`; Newton fuel
    256: `rootLoop` stops at convergence, and centers with `q = 64` need about 66 steps at `m = 2`). -/
def oc (P : PieceD) : ArbEcon.Off.OCfg := ⟨P.a, P.b, P.q, 2 ^ (P.q * 64), 256⟩

theorem val_σQ (P : PieceD) (hq : 1 ≤ P.q) : P.σQ.val = P.σ := by
  rw [σQ, val_frac _ hq, σ]
  push_cast
  ring

theorem val_rQ (P : PieceD) (hrd : 1 ≤ P.rd) : P.rQ.val = (P.rn : ℝ) / P.rd := by
  rw [rQ, val_frac _ hrd]
  push_cast
  ring

theorem val_GQ (P : PieceD) (hGd : 1 ≤ P.Gd) : P.GQ.val = (P.Gn : ℝ) / P.Gd := by
  rw [GQ, val_frac _ hGd]
  push_cast
  ring

theorem val_FQ (P : PieceD) (hFD : 1 ≤ P.FD) : P.FQ.val = (P.FN : ℝ) / P.FD := by
  rw [FQ, val_frac _ hFD]
  push_cast
  ring

theorem val_xloQ (P : PieceD) (he : 1 ≤ P.eqd) : P.xloQ.val = ((P.ea : ℝ) - P.eb) / P.eqd := by
  rw [xloQ, val_frac _ he]
  push_cast
  ring

end PieceD

/-! ## D. The side conditions as Booleans -/

/-- The `G` certificate: `Gd^gq N^gb ≤ Gn^gq N^ga`, `ga ≤ gb`, `(ga - gb)/gq ≤ σ`. -/
def gOK (N : ℕ) (P : PieceD) : Bool :=
  Nat.ble 1 P.gq && Nat.ble 1 P.Gd && Nat.ble P.ga P.gb &&
    Nat.ble (P.Gd ^ P.gq * N ^ P.gb) (P.Gn ^ P.gq * N ^ P.ga) &&
    Q.le (frac ((P.ga : ℤ) - P.gb) P.gq) P.σQ

theorem gOK_sound (N : ℕ) (hN : 1 ≤ N) (P : PieceD) (hq : 1 ≤ P.q) (h : gOK N P = true) (t : ℝ) :
    ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖(n : ℂ) ^ (-ArbEcon.Off.sOfG P.σ t)‖ ≤ P.GQ.val := by
  simp only [gOK, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨hgq, hGd⟩, hab⟩, hpow⟩, hle⟩ := h
  have hσ := le_sound hle
  rw [val_frac _ hgq, P.val_σQ hq] at hσ
  push_cast at hσ
  rw [P.val_GQ hGd]
  exact H1000Oct.natCpow_norm_le_of_pow N hN P.ga P.gb P.gq hgq P.Gn P.Gd hGd hpow hab P.σ t hσ

/-- The order-13 remainder on the piece: `[σ - r, σ + r] ⊆ [xlo, xhi]`, `xlo > -12`, `|x| ≤ sigs`,
    `pochNormSq sigs t 13 ≤ Qr²`, `N^(-xlo) ≤ Rn/Rd`, and `C_6 Qr (Rn/Rd) / N^12 / (xlo + 12) ≤ E`
    (with `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`). -/
def remOK (tn tq N : ℕ) (P : PieceD) : Bool :=
  Nat.ble 1 P.eqd && Nat.ble 1 P.Rd && Nat.ble 1 tn &&
    Q.le P.xloQ (sub P.σQ P.rQ) && Q.le (add P.σQ P.rQ) P.xhi &&
    decide (0 < (add P.xloQ (ofNat 12)).n) &&
    Q.le P.xhi P.sigs && Q.le (neg P.xloQ) P.sigs &&
    Q.le (pochQ P.sigs (tQ tn tq) 13) (ofNat (P.Qr * P.Qr)) &&
    Nat.ble (P.Rd ^ P.eqd * N ^ P.eb) (P.Rn ^ P.eqd * N ^ P.ea) &&
    Q.le (div (div (mul (mul (frac 84107 (10 ^ 15)) (ofNat P.Qr)) (frac (P.Rn : ℤ) P.Rd))
      (ofNat (N ^ 12))) (add P.xloQ (ofNat 12))) P.E

theorem remOK_sound (tn tq N : ℕ) (hN : 1 ≤ N) (P : PieceD) (hq : 1 ≤ P.q) (hrd : 1 ≤ P.rd)
    (h : remOK tn tq N P = true) :
    ∀ x : ℝ, |x - P.σ| ≤ (P.rn : ℝ) / P.rd →
      ‖riemannZeta (ArbEcon.Off.sOfG x ((tn : ℝ) / 2 ^ tq))
        - emFinite 6 (ArbEcon.Off.sOfG x ((tn : ℝ) / 2 ^ tq)) N‖ ≤ P.E.val := by
  simp only [remOK, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he, hRd⟩, htn⟩, hlo⟩, hhi⟩, hpos⟩, hs1⟩, hs2⟩, hQ⟩, hpow⟩, hE⟩ := h
  have hlo' := le_sound hlo
  have hhi' := le_sound hhi
  have hs1' := le_sound hs1
  have hs2' := le_sound hs2
  have hQ' := le_sound hQ
  have hE' := le_sound hE
  rw [val_sub, P.val_σQ hq, P.val_rQ hrd] at hlo'
  rw [val_add, P.val_σQ hq, P.val_rQ hrd] at hhi'
  rw [val_neg] at hs2'
  rw [val_pochQ, val_tQ, val_ofNat] at hQ'
  have hNp : (0 : ℤ) < ((N ^ 12 : ℕ) : ℤ) := by exact_mod_cast pow_pos (by omega : 0 < N) _
  rw [val_div _ hpos, val_div _ hNp, val_mul, val_mul, val_frac _ (by norm_num),
    val_frac _ hRd, val_ofNat, val_ofNat, val_add, val_ofNat] at hE'
  have hposR : 0 < P.xloQ.val + 12 := by
    have := val_pos hpos
    rw [val_add, val_ofNat] at this
    exact_mod_cast this
  have htR : (tn : ℝ) / 2 ^ tq ≠ 0 := by
    have : (0 : ℝ) < tn := by exact_mod_cast htn
    positivity
  have hR := H1000Oct.rpow_cert N hN P.ea P.eb P.eqd he P.Rn P.Rd hRd hpow P.xloQ.val
    (P.val_xloQ he)
  have hrem := H1000Oct.em_remainder_horiz6 N hN ((tn : ℝ) / 2 ^ tq) htR P.xloQ.val P.xhi.val
    P.sigs.val (by linarith) hs1' hs2' (P.Qr : ℝ) (Nat.cast_nonneg _)
    (by rw [sq]; push_cast at hQ' ⊢; exact hQ') ((P.Rn : ℝ) / P.Rd) hR P.E.val
    (by push_cast at hE' ⊢; norm_num at hE' ⊢; linarith)
  exact H1000Oct.hE_of_range 6 N ((tn : ℝ) / 2 ^ tq) P.σ ((P.rn : ℝ) / P.rd) P.xloQ.val P.xhi.val
    P.E.val hlo' hhi' hrem

/-- The scalar geometry of the piece: the log bracket `lhi ≤ L 2^64`, `r L ≤ 1`, `0 < a`,
    `(a + r)² ≤ (σ - 1)² + t²`, `0 ≤ U`, `(|σ| + 11)² + t² ≤ U²`. -/
def geomOK (tn tq : ℕ) (L : Q) (lhi : ℕ) (P : PieceD) : Bool :=
  Q.le (ofNat lhi) (mul L (ofNat (2 ^ 64))) && Q.le (mul P.rQ L) (ofNat 1) &&
    decide (0 < P.aQ.n) &&
    Q.le (npow (add P.aQ P.rQ) 2) (add (npow (sub P.σQ (ofNat 1)) 2) (npow (tQ tn tq) 2)) &&
    decide (0 ≤ P.U.n) &&
    Q.le (add (npow (add (qabs P.σQ) (ofNat 11)) 2) (npow (tQ tn tq) 2)) (npow P.U 2)

/-- The error budget of the piece. -/
def budgetOK (N : ℕ) (L : Q) (P : PieceD) : Bool :=
  Q.le (budgetQ 6 N 5 P.GQ P.rQ L P.aQ P.U P.E) P.FQ

/-! ## E. THE PIECE -/

/-- **The piece checker**: the off-line evaluator run at the center (states after `N - 1` and `N`
    terms, 6 accumulators, recomputed here), the kernel check `H1000Oct.checkOct`, and every side
    condition of `H1000Oct.piece_octX_pos`. -/
noncomputable def pieceOK (tn tq N : ℕ) (L : Q) (P : PieceD) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD &&
    H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk &&
    geomOK tn tq L sN.lhi P && gOK N P && remOK tn tq N P && budgetOK N L P

set_option maxHeartbeats 1000000 in
/-- **Soundness of the piece checker**: `0 < octX kk (ζ(x + i t))` on the whole piece. -/
theorem pieceOK_sound (tn tq N : ℕ) (L : Q) (P : PieceD) (h : pieceOK tn tq N L P = true) :
    ∀ x : ℝ, |x - P.σ| ≤ (P.rn : ℝ) / P.rd →
      0 < ArgHoriz.octX P.kk (riemannZeta ((x : ℂ) + (((tn : ℝ) / 2 ^ tq : ℝ) : ℂ) * I)) := by
  simp only [pieceOK, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hN2, hq⟩, hrd⟩, hFD⟩, hchk⟩, hgeom⟩, hg⟩, hrem⟩, hbud⟩ := h
  set c := ArbEcon.OrderK.cfg64 tn tq with hc
  set t : ℝ := (tn : ℝ) / 2 ^ tq with ht
  set s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5) with hs1
  set sN := ArbEcon.Off.runO c P.oc 1 s1 with hsN
  have hv : ArbEcon.Valid c t 9 := ArbEcon.OrderK.valid64 tn tq t rfl
  have ho : ArbEcon.Off.OValid c P.oc P.σ := ⟨rfl, hq, rfl⟩
  have i0 := ArbEcon.Off.initO_sound c P.σ t 5 hv.one_eq
  have i1 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho (N - 2) 1 _ i0
  rw [show 1 + (N - 2) = N - 1 by omega] at i1
  have i2 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho 1 (N - 1) _ i1
  rw [show N - 1 + 1 = N by omega] at i2
  -- the scalar geometry
  simp only [geomOK, Bool.and_eq_true, decide_eq_true_eq] at hgeom
  obtain ⟨⟨⟨⟨⟨hL, hRL⟩, ha⟩, hA⟩, hU0⟩, hU⟩ := hgeom
  have hL' := le_sound hL
  have hRL' := le_sound hRL
  have hA' := le_sound hA
  have hU' := le_sound hU
  rw [val_ofNat, val_mul, val_ofNat] at hL'
  rw [val_mul, val_ofNat, P.val_rQ hrd, Nat.cast_one] at hRL'
  rw [val_npow, val_add, P.val_rQ hrd, val_add, val_npow, val_npow, val_sub, P.val_σQ hq, val_ofNat,
    val_tQ, Nat.cast_one] at hA'
  rw [val_add, val_npow, val_add, val_qabs, P.val_σQ hq, val_ofNat, val_npow, val_tQ,
    val_npow] at hU'
  have hG := gOK_sound N (by omega) P hq hg t
  have hE := remOK_sound tn tq N (by omega) P hq hrd hrem
  have hB := le_sound hbud
  rw [val_budgetQ 6 N 5 (by norm_num) (by omega) _ _ _ _ _ _ ha, P.val_rQ hrd, P.val_FQ hFD] at hB
  refine H1000Oct.piece_octX_pos c P.oc P.σ t rfl rfl 6 N 5 hN2 s1 sN i1 i2 P.rn P.rd P.FN P.FD
    P.kk hchk ((P.rn : ℝ) / P.rd) L.val P.aQ.val P.U.val P.GQ.val P.E.val le_rfl ?_ hRL' (val_pos ha)
    hA' (val_nonneg hU0) ?_ hG hE hB
  · have hP64 : c.P = 64 := rfl
    have e : ((2 ^ 64 : ℕ) : ℝ) = (2 : ℝ) ^ (64 : ℕ) := by push_cast; ring
    rw [hP64, ← e]
    exact hL'
  · have e : (2 * ((6 : ℕ) : ℝ) - 1 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
    rw [e]; exact hU'

end Arb4
