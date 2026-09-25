import CF_Num

/-!
# CF_Cert: the counterfeit-ladder separation at x = e^{18 pi/17} ~ 27.84 (kernel-checked)

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  The Riemann Hypothesis is open.  This is a barrier / calibration
certificate: one explicit test function at one window.  It is not a positivity mechanism and not a
step towards RH.

## The instance
Window `A = 9 pi/17` (`x = e^{2A} = e^{18 pi/17} = 27.84`), nine Dirichlet cosines
`k_i = (2i + 1) 17/18` (`k_i A = (2i+1) pi/2`, `s_i = (-1)^i`), and the rational test
`v = sum_i c_i cos(k_i u)` on `[-A, A]` with
`c = (-33/100, -1/50, -37/100, 23/100, -3/10, 3/25, -37/100, 1, -1/4)`
(the least eigenvector of E's form on the nine-mode span, rounded to 1/100).

## What is proved (all axiom-clean)
* `epstein_window_negative`: for ANY weights `w` satisfying E's defining identity
  `aE(n) log n = sum_{d|n} w(d) aE(n/d)` on `[1, 27]` (`aE` = half the lattice count of `x^2 + 5y^2`),
  `Re weilFormGC w (v * v~) <= -(3/20) ||v||^2`.  (Computed: `-0.1714 ||v||^2`.)
* `zetaK_window_pos`: with zeta_K's weights `Lambda(n)(1 + chi_-20(n))`,
  `Re weilFormGC cK (v * v~) >= 3 ||v||^2`.  (Computed: `+5.032 ||v||^2`.)
* `window_separation`: both, on the same nonzero test; `window_separation_cE`: at `w = cE` (non-vacuous,
  `cE_conv`).
* Negative controls: `tabM_tamper` (a shifted log enclosure is rejected by the checker),
  `certE_tamper` / `certK_tamper` (the final rational certificates FAIL when the E weights and the
  zeta_K weights are swapped).

Both functionals share the SAME arch side `archSideGC` (pole terms kept, `Gamma_C`, conductor 20);
they differ only in the prime weights.  The identification of `weilFormGC` with the zero sum is the
classical explicit formula (not formalized); it is checked numerically in telperion/docs/CF_COUNTERFEIT_LADDER_2026-09-25.md
(arithmetic side vs a sum over E's zeros, off-line quadruples included).
No `sorry`.
-/

open MeasureTheory Complex Set Filter Crux3

noncomputable section

namespace CF

/-! ## A. The data -/

/-- The nine coefficients (E's least eigenvector on the span, rounded to `1/100`). -/
def cS : ℕ → ℚ
  | 0 => -33 / 100 | 1 => -1 / 50 | 2 => -37 / 100 | 3 => 23 / 100 | 4 => -3 / 10 | 5 => 3 / 25
  | 6 => -37 / 100 | 7 => 1 | 8 => -1 / 4 | _ => 0

/-- `A = (9/17) pi`, `k_i = (2i + 1) 17/18`, `s_i = (-1)^i`. -/
def D0 : MData := ⟨9 / 17, 9, fun i => (2 * i + 1) * 17 / 18, fun i => if i % 2 = 0 then 1 else -1, cS⟩

def cfA : ℝ := ((D0.Q : ℚ) : ℝ) * Real.pi
def kR (i : ℕ) : ℝ := ((D0.k i : ℚ) : ℝ)
def sR (i : ℕ) : ℝ := ((D0.s i : ℚ) : ℝ)
def cR (i : ℕ) : ℝ := ((D0.c i : ℚ) : ℝ)

/-- **The test function** `v = sum_{i<9} c_i cos(k_i u)` on `[-9pi/17, 9pi/17]`, `0` outside. -/
def vStar : ℝ → ℝ := bandM cfA 9 kR cR

lemma kR_eq (i : ℕ) : kR i = (2 * (i : ℝ) + 1) * 17 / 18 := by
  unfold kR D0; push_cast; ring

lemma cfA_eq : cfA = 9 / 17 * Real.pi := by unfold cfA D0; push_cast; ring

lemma kR_mul_A (i : ℕ) : kR i * cfA = (i : ℝ) * Real.pi + Real.pi / 2 := by
  rw [kR_eq, cfA_eq]; ring

theorem modeHyp0 : ModeHyp cfA 9 kR sR where
  A0 := by rw [cfA_eq]; positivity
  kpos := fun i _ => by rw [kR_eq]; positivity
  cosk := fun i _ => by rw [kR_mul_A, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  sink := fun i hi => by
    rw [kR_mul_A, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    unfold sR D0
    interval_cases i <;> norm_num
  kinj := fun i _ j _ hij => by
    rw [kR_eq, kR_eq]
    intro h
    apply hij
    have : (i : ℝ) = j := by linarith
    exact_mod_cast this

lemma kR_sq_ne (i j : ℕ) (hij : i ≠ j) : kR i ^ 2 - kR j ^ 2 ≠ 0 := by
  rw [kR_eq, kR_eq]
  intro h
  apply hij
  have h1 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have : ((i : ℝ) - j) * ((i : ℝ) + j + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h3 | h3
  · have : (i : ℝ) = j := by linarith
    exact_mod_cast this
  · linarith

lemma alphaR_eq (m : ℕ) : alphaR 9 kR sR cR m = ((alphaQ D0 m : ℚ) : ℝ) := by
  unfold alphaR alphaQ kR sR cR
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sum, Rat.cast_sub,
    Rat.cast_ofNat, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero]
  rfl

/-- The autocorrelation of the test on `[0, 2A]` is the collapsed form `gstar D0`. -/
theorem acR_vStar {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 2 * cfA) : acR vStar y = gstar D0 y := by
  unfold vStar
  rw [acR_bandM modeHyp0 cR hy0 hy1,
    blk_sum_eq cfA 9 kR sR cR (fun i hi => (modeHyp0.kpos i hi).ne') (fun i _ j _ hij => kR_sq_ne i j hij) y]
  unfold gstar
  simp only [alphaR_eq]
  rfl

lemma norm_vStar : ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2 = acR vStar 0 := by
  unfold acR
  congr 1
  funext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, sq]

/-- `||v||^2 = g(0) = A * 16029/10000`. -/
lemma acR_vStar_zero : acR vStar 0 = cfA * (16029 / 10000) := by
  unfold vStar
  rw [acR_bandM_zero modeHyp0 cR]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cR, D0, cS]
  norm_num

/-! ## B. The prime-side table (n = 1..27) -/

def tabM : ℕ → MEntry
  | 1 => ⟨(0 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), [0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
  | 2 => ⟨((1732867951399863 : ℚ) / 2500000000000000), ((1386294361119891 : ℚ) / 2000000000000000), ((707106781186547523 : ℚ) / 1000000000000000000), ((353553390593273763 : ℚ) / 500000000000000000), [0, 0, 1, 1, 1, 1, 1, 2, 2]⟩
  | 3 => ⟨((2197224577336219 : ℚ) / 2000000000000000), ((5493061443340549 : ℚ) / 5000000000000000), ((577350269189625763 : ℚ) / 1000000000000000000), ((288675134594812883 : ℚ) / 500000000000000000), [0, 0, 1, 1, 1, 2, 2, 2, 3]⟩
  | 4 => ⟨((2772588722239781 : ℚ) / 2000000000000000), ((3465735902799727 : ℚ) / 2500000000000000), ((499999999999999999 : ℚ) / 1000000000000000000), ((500000000000000001 : ℚ) / 1000000000000000000), [0, 1, 1, 1, 2, 2, 3, 3, 4]⟩
  | 5 => ⟨((8047189562170501 : ℚ) / 5000000000000000), ((3218875824868201 : ℚ) / 2000000000000000), ((223606797749978969 : ℚ) / 500000000000000000), ((447213595499957941 : ℚ) / 1000000000000000000), [0, 1, 1, 2, 2, 3, 3, 4, 4]⟩
  | 6 => ⟨((17917594692280549 : ℚ) / 10000000000000000), ((2239699336535069 : ℚ) / 1250000000000000), ((81649658092772603 : ℚ) / 200000000000000000), ((204124145231931509 : ℚ) / 500000000000000000), [0, 1, 1, 2, 2, 3, 4, 4, 5]⟩
  | 7 => ⟨((4864775372638283 : ℚ) / 2500000000000000), ((3891820298110627 : ℚ) / 2000000000000000), ((188982236504613613 : ℚ) / 500000000000000000), ((377964473009227229 : ℚ) / 1000000000000000000), [0, 1, 1, 2, 3, 3, 4, 4, 5]⟩
  | 8 => ⟨((10397207708399179 : ℚ) / 5000000000000000), ((20794415416798361 : ℚ) / 10000000000000000), ((353553390593273761 : ℚ) / 1000000000000000000), ((88388347648318441 : ℚ) / 250000000000000000), [0, 1, 2, 2, 3, 3, 4, 5, 5]⟩
  | 9 => ⟨((1373265360835137 : ℚ) / 625000000000000), ((4394449154672439 : ℚ) / 2000000000000000), ((83333333333333333 : ℚ) / 250000000000000000), ((66666666666666667 : ℚ) / 200000000000000000), [0, 1, 2, 2, 3, 4, 4, 5, 6]⟩
  | 10 => ⟨((4605170185988091 : ℚ) / 2000000000000000), ((11512925464970229 : ℚ) / 5000000000000000), ((79056941504209483 : ℚ) / 250000000000000000), ((63245553203367587 : ℚ) / 200000000000000000), [0, 1, 2, 2, 3, 4, 4, 5, 6]⟩
  | 11 => ⟨((2997369090997963 : ℚ) / 1250000000000000), ((23978952727983707 : ℚ) / 10000000000000000), ((301511344577763621 : ℚ) / 1000000000000000000), ((37688918072220453 : ℚ) / 125000000000000000), [0, 1, 2, 3, 3, 4, 5, 5, 6]⟩
  | 12 => ⟨((12424533248940001 : ℚ) / 5000000000000000), ((4969813299576001 : ℚ) / 2000000000000000), ((288675134594812881 : ℚ) / 1000000000000000000), ((72168783648703221 : ℚ) / 250000000000000000), [0, 1, 2, 3, 3, 4, 5, 6, 6]⟩
  | 13 => ⟨((12824746787307683 : ℚ) / 5000000000000000), ((25649493574615369 : ℚ) / 10000000000000000), ((1733438113203841 : ℚ) / 6250000000000000), ((277350098112614563 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 3, 4, 5, 6, 7]⟩
  | 14 => ⟨((5278114659230517 : ℚ) / 2000000000000000), ((6597643324038147 : ℚ) / 2500000000000000), ((267261241912424383 : ℚ) / 1000000000000000000), ((133630620956212193 : ℚ) / 500000000000000000), [0, 1, 2, 3, 4, 4, 5, 6, 7]⟩
  | 15 => ⟨((27080502011022099 : ℚ) / 10000000000000000), ((13540251005511051 : ℚ) / 5000000000000000), ((64549722436790281 : ℚ) / 250000000000000000), ((258198889747161127 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 4, 5, 6, 7]⟩
  | 16 => ⟨((27725887222397811 : ℚ) / 10000000000000000), ((13862943611198907 : ℚ) / 5000000000000000), ((249999999999999999 : ℚ) / 1000000000000000000), ((250000000000000001 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 5, 6, 7]⟩
  | 17 => ⟨((28332133440562159 : ℚ) / 10000000000000000), ((14166066720281081 : ℚ) / 5000000000000000), ((60633906259083243 : ℚ) / 250000000000000000), ((9701425001453319 : ℚ) / 40000000000000000), [0, 1, 2, 3, 4, 5, 6, 6, 7]⟩
  | 18 => ⟨((5780743515792329 : ℚ) / 2000000000000000), ((1806482348685103 : ℚ) / 625000000000000), ((736569563735987 : ℚ) / 3125000000000000), ((235702260395515843 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 7]⟩
  | 19 => ⟨((29444389791664403 : ℚ) / 10000000000000000), ((14722194895832203 : ℚ) / 5000000000000000), ((57353933467640441 : ℚ) / 250000000000000000), ((229415733870561767 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 20 => ⟨((7489330683884977 : ℚ) / 2500000000000000), ((29957322735539911 : ℚ) / 10000000000000000), ((27950849718747371 : ℚ) / 125000000000000000), ((223606797749978971 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 21 => ⟨((7611306094308557 : ℚ) / 2500000000000000), ((30445224377234231 : ℚ) / 10000000000000000), ((10910894511799619 : ℚ) / 50000000000000000), ((218217890235992383 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 22 => ⟨((30910424533583157 : ℚ) / 10000000000000000), ((772760613339579 : ℚ) / 250000000000000), ((213200716355610433 : ℚ) / 1000000000000000000), ((53300179088902609 : ℚ) / 250000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 23 => ⟨((6270988431858299 : ℚ) / 2000000000000000), ((15677471079645749 : ℚ) / 5000000000000000), ((208514414057074761 : ℚ) / 1000000000000000000), ((52128603514268691 : ℚ) / 250000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 24 => ⟨((6356107660695891 : ℚ) / 2000000000000000), ((15890269151739729 : ℚ) / 5000000000000000), ((204124145231931507 : ℚ) / 1000000000000000000), ((20412414523193151 : ℚ) / 100000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 25 => ⟨((16094379124341003 : ℚ) / 5000000000000000), ((32188758248682009 : ℚ) / 10000000000000000), ((199999999999999999 : ℚ) / 1000000000000000000), ((200000000000000001 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 26 => ⟨((32580965380214819 : ℚ) / 10000000000000000), ((16290482690107411 : ℚ) / 5000000000000000), ((19611613513818403 : ℚ) / 100000000000000000), ((196116135138184033 : ℚ) / 1000000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | 27 => ⟨((32958368660043289 : ℚ) / 10000000000000000), ((8239592165010823 : ℚ) / 2500000000000000), ((192450089729875253 : ℚ) / 1000000000000000000), ((24056261216234407 : ℚ) / 125000000000000000), [0, 1, 2, 3, 4, 5, 6, 7, 8]⟩
  | _ => ⟨0, 0, 0, 0, []⟩

set_option maxRecDepth 100000 in
/-- Every table entry passes the checker (`decide +kernel`). -/
theorem tabM_ok : (List.range 27).all (fun i => mEntryOK D0 (i + 1) (tabM (i + 1))) = true := by
  decide +kernel

/-- Negative control: the `n = 7` entry with its log enclosure shifted up by `10^-6` is rejected. -/
theorem tabM_tamper :
    mEntryOK D0 7 ⟨(tabM 7).lo + 1 / 10 ^ 6, (tabM 7).hi + 1 / 10 ^ 6, (tabM 7).q0, (tabM 7).q1, (tabM 7).ms⟩
      = false := by
  decide +kernel

lemma tabM_entry (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 27) : mEntryOK D0 n (tabM n) = true := by
  have h := tabM_ok
  rw [List.all_eq_true] at h
  have := h (n - 1) (List.mem_range.mpr (by omega))
  rwa [Nat.sub_add_cancel h1] at this

lemma D0_Q_nonneg : (0 : ℚ) ≤ D0.Q := by unfold D0; norm_num

lemma log_lt_twoA (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 27) : Real.log n < 2 * cfA :=
  (mEntry_sound D0 D0_Q_nonneg n (tabM n) (tabM_entry n h1 h2) 0).2

/-- The weighted prime sum over `n <= 27` for a weight `rho n log n`. -/
def Pr (rho : ℕ → ℚ) : ℝ :=
  ∑ n ∈ Finset.range 28, 2 * (((rho n : ℚ) : ℝ) * Real.log n) / Real.sqrt n * gstar D0 (Real.log n)

/-- The ball of `Pr rho`. -/
def PrB (rho : ℕ → ℚ) : ℚ × ℚ := ∑ i ∈ Finset.range 27, outM D0 (rho (i + 1)) (tabM (i + 1))

theorem Pr_ball (rho : ℕ → ℚ) : InB (Pr rho) (PrB rho).1 (PrB rho).2 := by
  unfold Pr PrB
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.log_zero, mul_zero, zero_div, zero_mul, add_zero]
  refine InB.fst_sum _ _ _ fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have := (mEntry_sound D0 D0_Q_nonneg (i + 1) (tabM (i + 1)) (tabM_entry (i + 1) (by omega) (by omega))
    (rho (i + 1))).1
  push_cast at this ⊢
  exact this


/-! ## C. The two prime sides -/

lemma lo28 : ((3332204510175203 / 10 ^ 15 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) :=
  le_log_of KX (by unfold KX; norm_num) 28 (by norm_num) (by norm_num) (by unfold KX; decide +kernel)

lemma twoA_lt_log28 : 2 * cfA < Real.log 28 := by
  have h1 := lo28
  have hpi := Real.pi_lt_d20
  rw [cfA_eq]
  push_cast at h1
  linarith

/-- The prime side of `v * v~` for any weight that equals `rho n log n` on `[1, 27]`. -/
lemma primeSide_vStar (w : ℕ → ℝ) (rho : ℕ → ℚ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → w n = ((rho n : ℚ) : ℝ) * Real.log n) :
    (primeSideD w (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re = Pr rho := by
  have hv := bandM_freqData modeHyp0 cR
  have hp := hv.primeD_eq w
  unfold vStar
  rw [hp, Complex.ofReal_re]
  have hA0 := modeHyp0.A0
  set f : ℕ → ℝ := fun n => if Real.log n < 2 * cfA then
      2 * w n / Real.sqrt n * acR (bandM cfA 9 kR cR) (Real.log n) else 0 with hf
  have hfN0 : ∀ n, ⌈Real.exp (2 * cfA)⌉₊ + 1 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.exp (2 * cfA) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * cfA))
      have h2 : ((⌈Real.exp (2 * cfA)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have h3 : 2 * cfA < Real.log n := by
      rw [← Real.log_exp (2 * cfA)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hf28 : ∀ n, 28 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.log 28 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith [twoA_lt_log28]
  rw [sum_range_eq_of_vanish f _ _ hfN0 hf28]
  unfold Pr
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.mp hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [hf]
  · have hlt := log_lt_twoA n hpos (by omega)
    rw [hf]; simp only
    rw [if_pos hlt, hw n hpos (by omega)]
    rw [show (bandM cfA 9 kR cR) = vStar from rfl, acR_vStar (Real.log_natCast_nonneg n) hlt.le]

/-- E's prime side, for ANY weights with E's defining identity on `[1, 27]`. -/
theorem primeE_eq (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    (primeSideD w (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re = Pr rhoE :=
  primeSide_vStar w rhoE (fun n h1 h2 => by rw [eq_cE_of_conv w hw n h1 h2]; rfl)

/-- zeta_K's prime side, weights `Lambda(n)(1 + chi_-20(n))`. -/
theorem primeK_eq : (primeSideD cK (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re = Pr rhoK :=
  primeSide_vStar cK rhoK (fun n _ h2 => cK_eq n h2)

/-- The rational weight balls, kernel-evaluated. -/
theorem q_PE : (13498116 / 10 ^ 6 : ℚ) ≤ (PrB rhoE).1 - (PrB rhoE).2 := by decide +kernel
theorem q_PK : (PrB rhoK).1 + (PrB rhoK).2 ≤ (-37393 / 100000 : ℚ) := by decide +kernel

lemma PE_ge : (13498116 / 10 ^ 6 : ℝ) ≤ Pr rhoE := by
  have h := (Pr_ball rhoE).ge
  have q := Rat.cast_le (K := ℝ) |>.mpr q_PE
  push_cast at h q
  linarith

lemma PK_le : Pr rhoK ≤ (-37393 / 100000 : ℝ) := by
  have h := (Pr_ball rhoK).le
  have q := Rat.cast_le (K := ℝ) |>.mpr q_PK
  push_cast at h q
  linarith

/-! ## D. The arch side of the test -/

/-- `sum_i c_i 2 k_i s_i/(k_i^2 + 1/4)`. -/
def rhoPQ : ℚ := ∑ i ∈ Finset.range 9, cS i * (2 * D0.k i * D0.s i / (D0.k i ^ 2 + 1 / 4))

lemma pole_vStar : ∫ u, vStar u * Real.exp (-(1 / 2) * u) = Real.cosh (cfA / 2) * ((rhoPQ : ℚ) : ℝ) := by
  unfold vStar
  rw [integral_bandM_exp_half modeHyp0 cR]
  unfold poleVal rhoPQ
  rw [Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cR kR sR
  push_cast
  simp only [D0]
  ring

/-- `4 b sum_i c_i^2/(4b^2 + k_i^2)`. -/
def tauQ (b : ℚ) : ℚ := 4 * b * ∑ i ∈ Finset.range 9, cS i ^ 2 / (4 * b ^ 2 + D0.k i ^ 2)

/-- `sum_i c_i s_i k_i/(4b^2 + k_i^2)`. -/
def SQ (b : ℚ) : ℚ := ∑ i ∈ Finset.range 9, cS i * D0.s i * D0.k i / (4 * b ^ 2 + D0.k i ^ 2)

lemma lor_vStar (q : ℚ) (hq : 0 < q) :
    lorTermB vStar (q : ℝ) = cfA * ((tauQ q : ℚ) : ℝ)
      + 2 * (1 + Real.exp (-(2 * (q : ℝ)) * (2 * cfA))) * ((SQ q : ℚ) : ℝ) ^ 2 := by
  unfold vStar
  rw [lorTermB_bandM modeHyp0 cR _ (by exact_mod_cast hq)]
  unfold tauQ SQ
  push_cast
  unfold cR kR sR
  simp only [D0]
  ring

lemma lorSum_vStar (b : ℚ) (hb : 0 < b) :
    ∑ j ∈ Finset.range 301, lorTermB vStar (((j : ℚ) + b : ℚ) : ℝ)
      = cfA * (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + b)) : ℚ) : ℝ)
        + 2 * ∑ j ∈ Finset.range 301, (1 + Real.exp (-(2 * ((((j : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)))
            * ((SQ ((j : ℚ) + b) : ℚ) : ℝ) ^ 2 := by
  rw [Rat.cast_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lor_vStar _ (by positivity)]
  ring

/-- The exponential factors are at most `1`, and at least `0`. -/
lemma lorS_le (b : ℚ) (_hb : 0 < b) :
    ∑ j ∈ Finset.range 301, (1 + Real.exp (-(2 * ((((j : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)))
        * ((SQ ((j : ℚ) + b) : ℚ) : ℝ) ^ 2
      ≤ 2 * (((∑ j ∈ Finset.range 301, SQ ((j : ℚ) + b) ^ 2) : ℚ) : ℝ) := by
  rw [Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hA := modeHyp0.A0
  have hj : (0 : ℝ) < (((j : ℚ) + b : ℚ) : ℝ) := by
    have : (0 : ℚ) < (j : ℚ) + b := by positivity
    exact_mod_cast this
  have he : Real.exp (-(2 * ((((j : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos two_pos hj) (mul_pos two_pos hA)
    linarith
  push_cast at he ⊢
  nlinarith [sq_nonneg ((SQ ((j : ℚ) + b) : ℚ) : ℝ)]

lemma lorS_ge (b : ℚ) (_hb : 0 < b) :
    (((∑ j ∈ Finset.range 301, SQ ((j : ℚ) + b) ^ 2) : ℚ) : ℝ)
        + Real.exp (-(2 * (b : ℝ)) * (2 * cfA)) * ((SQ b : ℚ) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range 301, (1 + Real.exp (-(2 * ((((j : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)))
        * ((SQ ((j : ℚ) + b) : ℚ) : ℝ) ^ 2 := by
  rw [Rat.cast_sum]
  rw [Finset.sum_range_succ' (fun j => (1 + Real.exp (-(2 * ((((j : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)))
        * ((SQ ((j : ℚ) + b) : ℚ) : ℝ) ^ 2),
    Finset.sum_range_succ' (fun j => (((SQ ((j : ℚ) + b) ^ 2 : ℚ)) : ℝ))]
  simp only [Nat.cast_zero, zero_add]
  have hterm : ∀ j ∈ Finset.range 300, ((SQ (((j + 1 : ℕ) : ℚ) + b) ^ 2 : ℚ) : ℝ)
      ≤ (1 + Real.exp (-(2 * (((((j + 1 : ℕ) : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA)))
        * ((SQ (((j + 1 : ℕ) : ℚ) + b) : ℚ) : ℝ) ^ 2 := by
    intro j _
    have he := (Real.exp_pos (-(2 * (((((j + 1 : ℕ) : ℚ) + b : ℚ)) : ℝ)) * (2 * cfA))).le
    push_cast at he ⊢
    nlinarith [sq_nonneg ((SQ (((j + 1 : ℕ) : ℚ) + b) : ℚ) : ℝ)]
  have := Finset.sum_le_sum hterm
  push_cast at this ⊢
  linarith

/-! ## E. Constants -/

lemma cfA_bounds : (9 / 17 : ℝ) * (314159265358979323846 / 10 ^ 20) ≤ cfA
    ∧ cfA ≤ (9 / 17 : ℝ) * (314159265358979323847 / 10 ^ 20) := by
  have hpil := Real.pi_gt_d20
  have hpih := Real.pi_lt_d20
  rw [cfA_eq]
  constructor <;> norm_num at hpil hpih ⊢ <;> linarith

lemma log20_bounds : ((299573227355399 / 10 ^ 14 : ℚ) : ℝ) ≤ Real.log (20 : ℕ)
    ∧ Real.log (20 : ℕ) ≤ ((2995732273553991 / 10 ^ 15 : ℚ) : ℝ) :=
  ⟨le_log_of KX (by unfold KX; norm_num) 20 (by norm_num) (by norm_num) (by unfold KX; decide +kernel),
   log_le_of KX (by unfold KX; norm_num) 20 (by norm_num) (by norm_num) (by unfold KX; decide +kernel)
     (by unfold KX; decide +kernel)⟩

lemma logL_bounds : (299573227355399 / 10 ^ 14 : ℝ) - 2 * (11448 / 10000) ≤ Real.log (20 / Real.pi ^ 2)
    ∧ Real.log (20 / Real.pi ^ 2) ≤ (2995732273553991 / 10 ^ 15 : ℝ) - 2 * (11447 / 10000) := by
  obtain ⟨h1, h2⟩ := log20_bounds
  have h3 := log_pi_le'
  have h4 := log_pi_ge'
  rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]
  push_cast at h1 h2
  constructor <;> linarith

lemma log101_le : Real.log (101 : ℕ) ≤ ((230756025842063 / (5 * 10 ^ 13) : ℚ) : ℝ) :=
  log_le_of KX (by unfold KX; norm_num) 101 (by norm_num) (by norm_num) (by unfold KX; decide +kernel)
    (by unfold KX; decide +kernel)

theorem q_H100 : (5187377517639 / 10 ^ 12 : ℚ) ≤ harmonic 100 := by decide +kernel

/-- `gamma >= H_100 - log 101 >= 0.572257` (Mathlib: `eulerMascheroniSeq n < gamma`). -/
lemma gamma_ge : (5187377517639 / 10 ^ 12 : ℝ) - 230756025842063 / (5 * 10 ^ 13) ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 100
  unfold Real.eulerMascheroniSeq at h
  have hq := Rat.cast_le (K := ℝ) |>.mpr q_H100
  have hl := log101_le
  push_cast at hq hl h
  have e : ((100 : ℕ) : ℝ) + 1 = (101 : ℝ) := by norm_num
  norm_num at h hl
  linarith

theorem q_H300lo : (6282663880299 / 10 ^ 12 : ℚ) ≤ ∑ n ∈ Finset.range 300, (1 : ℚ) / ((n : ℚ) + 1) := by
  decide +kernel

lemma H300_bounds : (6282663880299 / 10 ^ 12 : ℝ) ≤ ∑ n ∈ Finset.range 300, (1 : ℝ) / ((n : ℝ) + 1)
    ∧ ∑ n ∈ Finset.range 300, (1 : ℝ) / ((n : ℝ) + 1) ≤ 3141331941 / 500000000 := by
  have h1 := Rat.cast_le (K := ℝ) |>.mpr q_H300lo
  have h2 := Rat.cast_le (K := ℝ) |>.mpr q_H300
  push_cast at h1 h2
  exact ⟨h1, h2⟩

/-- `cosh(A/2) <= 1.36617`. -/
theorem q_coshHi : ((expSQ KX ((166319611072401 / (2 * 10 ^ 14) : ℚ) / 8)
      + expRQ KX ((166319611072401 / (2 * 10 ^ 14) : ℚ) / 8)) ^ 8
    + (expSQ KX ((-(207899513840501 / (25 * 10 ^ 13)) : ℚ) / 8)
      + expRQ KX ((-(207899513840501 / (25 * 10 ^ 13)) : ℚ) / 8)) ^ 8) / 2 ≤ (136617 / 100000 : ℚ) := by
  unfold KX; decide +kernel

lemma cosh_le : Real.cosh (cfA / 2) ≤ 136617 / 100000 := by
  obtain ⟨hA1, hA2⟩ := cfA_bounds
  have e1 := exp_le_Q (q := 166319611072401 / (2 * 10 ^ 14)) (by norm_num)
  have e2 := exp_le_Q (q := -(207899513840501 / (25 * 10 ^ 13))) (by norm_num)
  have m1 : Real.exp (cfA / 2) ≤ Real.exp (((166319611072401 / (2 * 10 ^ 14) : ℚ)) : ℝ) := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  have m2 : Real.exp (-(cfA / 2)) ≤ Real.exp (((-(207899513840501 / (25 * 10 ^ 13)) : ℚ)) : ℝ) := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  have q := Rat.cast_le (K := ℝ) |>.mpr q_coshHi
  rw [Real.cosh_eq]
  push_cast at q e1 e2
  linarith

/-- `e^{-A} >= 0.189532` and `e^{-3A} >= 0.006808`. -/
theorem q_Em1 : (189532 / 10 ^ 6 : ℚ) ≤ (expSQ KX ((-(1663196110724009 / 10 ^ 15)) / 8)
    - expRQ KX ((-(1663196110724009 / 10 ^ 15)) / 8)) ^ 8 := by unfold KX; decide +kernel
theorem q_Em1pos : (0 : ℚ) ≤ expSQ KX ((-(1663196110724009 / 10 ^ 15)) / 8)
    - expRQ KX ((-(1663196110724009 / 10 ^ 15)) / 8) := by unfold KX; decide +kernel
theorem q_Em3 : (6808 / 10 ^ 6 : ℚ) ≤ (expSQ KX ((-(199583533286881 / (4 * 10 ^ 13))) / 8)
    - expRQ KX ((-(199583533286881 / (4 * 10 ^ 13))) / 8)) ^ 8 := by unfold KX; decide +kernel
theorem q_Em3pos : (0 : ℚ) ≤ expSQ KX ((-(199583533286881 / (4 * 10 ^ 13))) / 8)
    - expRQ KX ((-(199583533286881 / (4 * 10 ^ 13))) / 8) := by unfold KX; decide +kernel

lemma Em1_ge : (189532 / 10 ^ 6 : ℝ) ≤ Real.exp (-(2 * ((1 / 4 : ℚ) : ℝ)) * (2 * cfA)) := by
  obtain ⟨hA1, hA2⟩ := cfA_bounds
  have e := exp_ge_Q (q := -(1663196110724009 / 10 ^ 15)) (by norm_num) q_Em1pos
  have q := Rat.cast_le (K := ℝ) |>.mpr q_Em1
  have m : Real.exp (((-(1663196110724009 / 10 ^ 15)) : ℚ) : ℝ) ≤ Real.exp (-(2 * ((1 / 4 : ℚ) : ℝ)) * (2 * cfA)) := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  push_cast at q e
  linarith

lemma Em3_ge : (6808 / 10 ^ 6 : ℝ) ≤ Real.exp (-(2 * ((3 / 4 : ℚ) : ℝ)) * (2 * cfA)) := by
  obtain ⟨hA1, hA2⟩ := cfA_bounds
  have e := exp_ge_Q (q := -(199583533286881 / (4 * 10 ^ 13))) (by norm_num) q_Em3pos
  have q := Rat.cast_le (K := ℝ) |>.mpr q_Em3
  have m : Real.exp (((-(199583533286881 / (4 * 10 ^ 13))) : ℚ) : ℝ) ≤ Real.exp (-(2 * ((3 / 4 : ℚ) : ℝ)) * (2 * cfA)) := by
    apply Real.exp_le_exp.mpr; push_cast; linarith
  push_cast at q e
  linarith

/-- The rounded Lorentzian sums (`decide +kernel`, every term rounded to `10^-25`). -/
theorem q_t14 : (6581939035062 / 10 ^ 12 : ℚ) ≤ sumLo (fun j => tauQ ((j : ℚ) + 1 / 4)) 301 25
    ∧ sumHi (fun j => tauQ ((j : ℚ) + 1 / 4)) 301 25 ≤ 6581939035063 / 10 ^ 12 := by decide +kernel
theorem q_t34 : (6549485735694 / 10 ^ 12 : ℚ) ≤ sumLo (fun j => tauQ ((j : ℚ) + 3 / 4)) 301 25
    ∧ sumHi (fun j => tauQ ((j : ℚ) + 3 / 4)) 301 25 ≤ 6549485735695 / 10 ^ 12 := by decide +kernel
theorem q_s14 : (52838100521 / 10 ^ 11 : ℚ) ≤ sumLo (fun j => SQ ((j : ℚ) + 1 / 4) ^ 2) 301 25
    ∧ sumHi (fun j => SQ ((j : ℚ) + 1 / 4) ^ 2) 301 25 ≤ 528381005211 / 10 ^ 12 := by decide +kernel
theorem q_s34 : (316402782326 / 10 ^ 12 : ℚ) ≤ sumLo (fun j => SQ ((j : ℚ) + 3 / 4) ^ 2) 301 25
    ∧ sumHi (fun j => SQ ((j : ℚ) + 3 / 4) ^ 2) 301 25 ≤ 316402782327 / 10 ^ 12 := by decide +kernel
theorem q_S0 : (292668 / 10 ^ 6 : ℚ) ≤ SQ (1 / 4) ^ 2 ∧ (128462 / 10 ^ 6 : ℚ) ≤ SQ (3 / 4) ^ 2 := by
  decide +kernel
theorem q_rhoP : (1170673 / 10 ^ 6 : ℚ) ≤ rhoPQ ^ 2 ∧ rhoPQ ^ 2 ≤ 1170674 / 10 ^ 6 := by decide +kernel

/-- `K' = (8/3) sum |c_i| k_i = 54281/675`. -/
lemma Kp_eq : (8 / 3 : ℝ) * ∑ i ∈ Finset.range 9, |cR i| * kR i = 54281 / 675 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cR, kR, D0, cS]
  norm_num [abs_of_neg, abs_of_pos]


/-! ## F. The final rational certificates (and their weight-swap negative controls) -/

/-- `A` from above. -/
def AhiQ : ℚ := 9 / 17 * (314159265358979323847 / 10 ^ 20)
/-- `A` from below. -/
def AloQ : ℚ := 9 / 17 * (314159265358979323846 / 10 ^ 20)
/-- `||v||^2 / A`. -/
def C2Q : ℚ := 16029 / 10000

/-- E-side coefficient of `A` (upper bound; includes the target `+(3/20)||v||^2`). -/
def XEQ : ℚ :=
  C2Q * (((2995732273553991 / 10 ^ 15) - 2 * (11447 / 10000))
      - 2 * ((5187377517639 / 10 ^ 12) - 230756025842063 / (5 * 10 ^ 13))
      + 2 * (3141331941 / 500000000) + 1 / 300 + 3 / 20 + 33 ^ 2 / (4 * 300 ^ 2))
    - 6581939035062 / 10 ^ 12 - 6549485735694 / 10 ^ 12

/-- E-side constant part (upper bound), without the prime sum. -/
def YEQ : ℚ :=
  2 * (136617 / 100000) ^ 2 * (1170674 / 10 ^ 6)
    - 2 * (52838100521 / 10 ^ 11 + 316402782326 / 10 ^ 12)
    - 2 * ((189532 / 10 ^ 6) * (292668 / 10 ^ 6) + (6808 / 10 ^ 6) * (128462 / 10 ^ 6))
    + (54281 / 675) ^ 2 / (33 * (4 * 300 ^ 2))

/-- **The E certificate**, as a function of the weight table: `A X + Y - P <= 0`. -/
def certE (rho : ℕ → ℚ) : Bool := decide (AhiQ * XEQ + YEQ - ((PrB rho).1 - (PrB rho).2) ≤ 0)

/-- zeta_K-side coefficient of `A` (lower bound; includes the target `-3 ||v||^2`). -/
def XKQ : ℚ :=
  C2Q * (((299573227355399 / 10 ^ 14) - 2 * (11448 / 10000)) - 2 * (58112 / 100000)
      + 2 * (6282663880299 / 10 ^ 12) - 3)
    - 6581939035063 / 10 ^ 12 - 6549485735695 / 10 ^ 12

/-- zeta_K-side constant part (lower bound), without the prime sum. -/
def YKQ : ℚ := 2 * (1170673 / 10 ^ 6) - 4 * (528381005211 / 10 ^ 12 + 316402782327 / 10 ^ 12)

/-- **The zeta_K certificate**: `A X + Y - P >= 0`. -/
def certK (rho : ℕ → ℚ) : Bool := decide (0 ≤ AloQ * XKQ + YKQ - ((PrB rho).1 + (PrB rho).2))

theorem certE_ok : certE rhoE = true := by decide +kernel
theorem certK_ok : certK rhoK = true := by decide +kernel
/-- **Negative control**: the SAME E certificate with zeta_K's weights `Lambda(n)(1 + chi_-20(n))` fails. -/
theorem certE_tamper : certE rhoK = false := by decide +kernel
/-- **Negative control**: the SAME zeta_K certificate with E's weights fails. -/
theorem certK_tamper : certK rhoE = false := by decide +kernel

lemma XEQ_pos : 0 ≤ XEQ := by unfold XEQ C2Q; norm_num
lemma XKQ_pos : 0 ≤ XKQ := by unfold XKQ C2Q; norm_num

/-! ## G. The theorems -/

lemma lor_cast (b : ℚ) :
    ∑ j ∈ Finset.range 301, lorTermB vStar ((j : ℝ) + (b : ℝ))
      = ∑ j ∈ Finset.range 301, lorTermB vStar ((((j : ℚ) + b : ℚ)) : ℝ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rfl

lemma tau_bounds (b : ℚ) (lo hi : ℚ) (h : lo ≤ sumLo (fun j => tauQ ((j : ℚ) + b)) 301 25
      ∧ sumHi (fun j => tauQ ((j : ℚ) + b)) 301 25 ≤ hi) :
    (lo : ℝ) ≤ (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + b)) : ℚ) : ℝ)
      ∧ (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + b)) : ℚ) : ℝ) ≤ (hi : ℝ) := by
  have h1 := h.1.trans (sumLo_le _ 301 25)
  have h2 := (le_sumHi _ 301 25).trans h.2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma S_bounds (b : ℚ) (lo hi : ℚ) (h : lo ≤ sumLo (fun j => SQ ((j : ℚ) + b) ^ 2) 301 25
      ∧ sumHi (fun j => SQ ((j : ℚ) + b) ^ 2) 301 25 ≤ hi) :
    (lo : ℝ) ≤ (((∑ j ∈ Finset.range 301, SQ ((j : ℚ) + b) ^ 2) : ℚ) : ℝ)
      ∧ (((∑ j ∈ Finset.range 301, SQ ((j : ℚ) + b) ^ 2) : ℚ) : ℝ) ≤ (hi : ℝ) := by
  have h1 := h.1.trans (sumLo_le _ 301 25)
  have h2 := (le_sumHi _ 301 25).trans h.2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The moment term simplifies (`pi` cancels). -/
lemma mom_eq (g : ℝ) :
    2 * ((1 / (2 * Real.pi)) * ((1 / (8 * ((300 : ℕ) : ℝ) ^ 2))
      * ((33 : ℝ) ^ 2 * (2 * Real.pi * g) + 2 * (54281 / 675 : ℝ) ^ 2 * (Real.pi / 33))))
      = 33 ^ 2 * g / (4 * 300 ^ 2) + (54281 / 675) ^ 2 / (33 * (4 * 300 ^ 2)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **THE EPSTEIN WINDOW IS NEGATIVE (kernel-checked).**  At `x = e^{18 pi/17} ~ 27.84`, on the nine-mode
test `v`, the Gamma_C (conductor 20) Weil functional with pole terms kept and with ANY prime weights `w`
satisfying the defining identity of `-E'/E` on `[1, 27]` (`E = (1/2) sum' (x^2 + 5y^2)^{-s}`) is
at most `-(3/20) ||v||^2`.  (Computed: `-0.1714 ||v||^2`.) -/
theorem epstein_window_negative (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    (weilFormGC w (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re
      ≤ -(3 / 20 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2 := by
  have hv := bandM_freqData modeHyp0 cR
  obtain ⟨hIsq, hT⟩ := bandM_moment modeHyp0 cR (R := 33) (by norm_num)
    (fun i hi => by rw [kR_eq]; interval_cases i <;> norm_num)
  have hup := hv.archGC_re_le 300 (by norm_num) hIsq _ hT
  rw [show bandM cfA 9 kR cR = vStar from rfl] at hup
  rw [pole_vStar, acR_vStar_zero, Kp_eq, mom_eq,
    show ((1 / 4 : ℝ)) = (((1 / 4 : ℚ)) : ℝ) by norm_num, show ((3 / 4 : ℝ)) = (((3 / 4 : ℚ)) : ℝ) by norm_num,
    lor_cast, lor_cast, lorSum_vStar _ (by norm_num), lorSum_vStar _ (by norm_num)] at hup
  simp only [Nat.cast_ofNat] at hup
  unfold weilFormGC
  rw [Complex.sub_re, primeE_eq w hw, norm_vStar, acR_vStar_zero]
  -- the numerical inputs, all as real numerals
  obtain ⟨hA1, hA2⟩ := cfA_bounds
  have hA0 : 0 ≤ cfA := modeHyp0.A0.le
  obtain ⟨hL1, hL2⟩ := logL_bounds
  have hg := gamma_ge
  obtain ⟨hH1, hH2⟩ := H300_bounds
  have ht14 := (tau_bounds _ _ _ q_t14).1
  have ht34 := (tau_bounds _ _ _ q_t34).1
  have hs14 := (S_bounds _ _ _ q_s14).1
  have hs34 := (S_bounds _ _ _ q_s34).1
  rw [show ((6581939035062 / 10 ^ 12 : ℚ) : ℝ) = (6581939035062 / 10 ^ 12 : ℝ) by norm_num] at ht14
  rw [show ((6549485735694 / 10 ^ 12 : ℚ) : ℝ) = (6549485735694 / 10 ^ 12 : ℝ) by norm_num] at ht34
  rw [show ((52838100521 / 10 ^ 11 : ℚ) : ℝ) = (52838100521 / 10 ^ 11 : ℝ) by norm_num] at hs14
  rw [show ((316402782326 / 10 ^ 12 : ℚ) : ℝ) = (316402782326 / 10 ^ 12 : ℝ) by norm_num] at hs34
  have hge14 := lorS_ge (1 / 4) (by norm_num)
  have hge34 := lorS_ge (3 / 4) (by norm_num)
  have hE1 := Em1_ge
  have hE3 := Em3_ge
  have hS1R : (292668 / 10 ^ 6 : ℝ) ≤ ((SQ (1 / 4) : ℚ) : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr q_S0.1; push_cast at h; exact h
  have hS3R : (128462 / 10 ^ 6 : ℝ) ≤ ((SQ (3 / 4) : ℚ) : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr q_S0.2; push_cast at h; exact h
  have hrhoR : ((rhoPQ : ℚ) : ℝ) ^ 2 ≤ (1170674 / 10 ^ 6 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr q_rhoP.2; push_cast at h; exact h
  have hch := cosh_le
  have hch0 : 0 ≤ Real.cosh (cfA / 2) := (Real.cosh_pos _).le
  have hcert := certE_ok
  unfold certE at hcert
  rw [decide_eq_true_eq] at hcert
  have hcertR := (Rat.cast_le (K := ℝ)).mpr hcert
  unfold AhiQ XEQ YEQ C2Q at hcertR
  push_cast at hcertR
  have hP := (Pr_ball rhoE).ge
  push_cast at hP
  -- products
  have hpole : (Real.cosh (cfA / 2) * ((rhoPQ : ℚ) : ℝ)) ^ 2 ≤ (136617 / 100000) ^ 2 * (1170674 / 10 ^ 6) := by
    rw [mul_pow]
    have h1 : Real.cosh (cfA / 2) ^ 2 ≤ (136617 / 100000) ^ 2 := pow_le_pow_left₀ hch0 hch 2
    exact mul_le_mul h1 hrhoR (sq_nonneg _) (by positivity)
  have hES1 : (189532 / 10 ^ 6) * (292668 / 10 ^ 6)
      ≤ Real.exp (-(2 * ((1 / 4 : ℚ) : ℝ)) * (2 * cfA)) * ((SQ (1 / 4) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul hE1 hS1R (by norm_num) (Real.exp_pos _).le
  have hES3 : (6808 / 10 ^ 6) * (128462 / 10 ^ 6)
      ≤ Real.exp (-(2 * ((3 / 4 : ℚ) : ℝ)) * (2 * cfA)) * ((SQ (3 / 4) : ℚ) : ℝ) ^ 2 :=
    mul_le_mul hE3 hS3R (by norm_num) (Real.exp_pos _).le
  have hXle : (16029 / 10000) * (Real.log (20 / Real.pi ^ 2) - 2 * Real.eulerMascheroniConstant
        + 2 * (∑ n ∈ Finset.range 300, (1 : ℝ) / ((n : ℝ) + 1)) + 1 / 300 + 3 / 20 + 33 ^ 2 / (4 * 300 ^ 2))
        - (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + 1 / 4)) : ℚ) : ℝ)
        - (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + 3 / 4)) : ℚ) : ℝ)
      ≤ (16029 / 10000) * (((2995732273553991 / 10 ^ 15) - 2 * (11447 / 10000))
        - 2 * ((5187377517639 / 10 ^ 12) - 230756025842063 / (5 * 10 ^ 13))
        + 2 * (3141331941 / 500000000) + 1 / 300 + 3 / 20 + 33 ^ 2 / (4 * 300 ^ 2))
        - 6581939035062 / 10 ^ 12 - 6549485735694 / 10 ^ 12 := by
    linarith
  have hXpos : (0 : ℝ) ≤ (16029 / 10000) * (((2995732273553991 / 10 ^ 15) - 2 * (11447 / 10000))
        - 2 * ((5187377517639 / 10 ^ 12) - 230756025842063 / (5 * 10 ^ 13))
        + 2 * (3141331941 / 500000000) + 1 / 300 + 3 / 20 + 33 ^ 2 / (4 * 300 ^ 2))
        - 6581939035062 / 10 ^ 12 - 6549485735694 / 10 ^ 12 := by norm_num
  have hAX := mul_le_mul_of_nonneg_left hXle hA0
  have hAX2 := mul_le_mul_of_nonneg_right hA2 hXpos
  push_cast at hup hge14 hge34 hAX hES1 hES3 hs14 hs34 ⊢
  linarith

/-- **ZETA_K PASSES THE SAME WINDOW (kernel-checked).**  With zeta_K's prime weights
`Lambda(n)(1 + chi_-20(n))` (supported on prime powers), the same functional on the same test is at least
`3 ||v||^2`.  (Computed: `+5.032 ||v||^2`.) -/
theorem zetaK_window_pos :
    (3 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2
      ≤ (weilFormGC cK (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re := by
  have hv := bandM_freqData modeHyp0 cR
  have hlow := hv.archGC_re_ge 300
  rw [show bandM cfA 9 kR cR = vStar from rfl] at hlow
  rw [pole_vStar, acR_vStar_zero,
    show ((1 / 4 : ℝ)) = (((1 / 4 : ℚ)) : ℝ) by norm_num, show ((3 / 4 : ℝ)) = (((3 / 4 : ℚ)) : ℝ) by norm_num,
    lor_cast, lor_cast, lorSum_vStar _ (by norm_num), lorSum_vStar _ (by norm_num)] at hlow
  unfold weilFormGC
  rw [Complex.sub_re, primeK_eq, norm_vStar, acR_vStar_zero]
  obtain ⟨hA1, hA2⟩ := cfA_bounds
  have hA0 : 0 ≤ cfA := modeHyp0.A0.le
  obtain ⟨hL1, hL2⟩ := logL_bounds
  have hg : Real.eulerMascheroniConstant ≤ 58112 / 100000 := by
    have := RvMBridge30.eulerMascheroni_le; norm_num at this ⊢; linarith
  obtain ⟨hH1, hH2⟩ := H300_bounds
  have ht14 := (tau_bounds _ _ _ q_t14).2
  have ht34 := (tau_bounds _ _ _ q_t34).2
  have hs14 := (S_bounds _ _ _ q_s14).2
  have hs34 := (S_bounds _ _ _ q_s34).2
  rw [show ((6581939035063 / 10 ^ 12 : ℚ) : ℝ) = (6581939035063 / 10 ^ 12 : ℝ) by norm_num] at ht14
  rw [show ((6549485735695 / 10 ^ 12 : ℚ) : ℝ) = (6549485735695 / 10 ^ 12 : ℝ) by norm_num] at ht34
  rw [show ((528381005211 / 10 ^ 12 : ℚ) : ℝ) = (528381005211 / 10 ^ 12 : ℝ) by norm_num] at hs14
  rw [show ((316402782327 / 10 ^ 12 : ℚ) : ℝ) = (316402782327 / 10 ^ 12 : ℝ) by norm_num] at hs34
  have hle14 := lorS_le (1 / 4) (by norm_num)
  have hle34 := lorS_le (3 / 4) (by norm_num)
  have hrhoR : (1170673 / 10 ^ 6 : ℝ) ≤ ((rhoPQ : ℚ) : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr q_rhoP.1; push_cast at h; exact h
  have hch : 1 ≤ Real.cosh (cfA / 2) := Real.one_le_cosh _
  have hcert := certK_ok
  unfold certK at hcert
  rw [decide_eq_true_eq] at hcert
  have hcertR := (Rat.cast_le (K := ℝ)).mpr hcert
  unfold AloQ XKQ YKQ C2Q at hcertR
  push_cast at hcertR
  have hP := (Pr_ball rhoK).le
  push_cast at hP
  have hpole : 1170673 / 10 ^ 6 ≤ (Real.cosh (cfA / 2) * ((rhoPQ : ℚ) : ℝ)) ^ 2 := by
    rw [mul_pow]
    have h1 : 1 ≤ Real.cosh (cfA / 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((rhoPQ : ℚ) : ℝ)]
  have hXge : (16029 / 10000) * (((299573227355399 / 10 ^ 14) - 2 * (11448 / 10000)) - 2 * (58112 / 100000)
        + 2 * (6282663880299 / 10 ^ 12) - 3) - 6581939035063 / 10 ^ 12 - 6549485735695 / 10 ^ 12
      ≤ (16029 / 10000) * (Real.log (20 / Real.pi ^ 2) - 2 * Real.eulerMascheroniConstant
        + 2 * (∑ n ∈ Finset.range 300, (1 : ℝ) / ((n : ℝ) + 1)) - 3)
        - (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + 1 / 4)) : ℚ) : ℝ)
        - (((∑ j ∈ Finset.range 301, tauQ ((j : ℚ) + 3 / 4)) : ℚ) : ℝ) := by
    linarith
  have hXpos : (0 : ℝ) ≤ (16029 / 10000) * (((299573227355399 / 10 ^ 14) - 2 * (11448 / 10000))
        - 2 * (58112 / 100000) + 2 * (6282663880299 / 10 ^ 12) - 3)
        - 6581939035063 / 10 ^ 12 - 6549485735695 / 10 ^ 12 := by norm_num
  have hAX := mul_le_mul_of_nonneg_left hXge hA0
  have hAX2 := mul_le_mul_of_nonneg_right hA1 hXpos
  push_cast at hlow hle14 hle34 hAX hs14 hs34 ⊢
  linarith

/-- **THE SEPARATION** on one nonzero test: zeta_K `>= 3 ||v||^2`, the Epstein counterfeit (any weights
with E's defining identity) `<= -(3/20) ||v||^2`.  Same arch side, same pole terms, same window. -/
theorem window_separation (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    0 < ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2
      ∧ (3 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2
          ≤ (weilFormGC cK (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re
      ∧ (weilFormGC w (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re
          ≤ -(3 / 20 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2 := by
  refine ⟨?_, zetaK_window_pos, epstein_window_negative w hw⟩
  rw [norm_vStar, acR_vStar_zero]
  have := modeHyp0.A0
  positivity

/-- Non-vacuity: E's closed-form weights `cE` satisfy the hypothesis (`cE_conv`). -/
theorem window_separation_cE :
    0 < ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2
      ∧ (3 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2
          ≤ (weilFormGC cK (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re
      ∧ (weilFormGC cE (WeilForm.autocorr (fun u => ((vStar u : ℝ) : ℂ)))).re
          ≤ -(3 / 20 : ℝ) * ∫ x, ‖((vStar x : ℝ) : ℂ)‖ ^ 2 :=
  window_separation cE cE_conv

end CF
