/-  ForgeLogBracket.lean -- ANDÚRIL cert-forge: a reusable, fully-general rational bracket for
    `Real.log n` at ANY positive natural `n` (no prime-factor table, no per-prime Mathlib lemma).

    The trig climb's θ-enclosure needs `|t·log n − c| ≤ w`, hence a tight rational bracket for
    `Real.log n`.  Mathlib supplies d9 brackets only for log 2/3/5; this file gives a bracket for
    every `n` via the exp route (`CertVerify.ln_of_exp_bracket`):

        lo ≤ log n ≤ hi   ⇐   exp lo ≤ n  ∧  n ≤ exp hi,

    and bounds `exp` of a (possibly > 1) rational `q = k + f` (`k : ℕ`, `f ∈ [0,1)`) by
    `exp q = (exp 1)^k · exp f`, with `exp 1` boxed by the Mathlib d9 constant and `exp f`
    (`|f| ≤ 1`) boxed by the order-`N` Taylor bracket (`TaylorKernels.exp_lower/upper`).  All
    endpoints are rationals the emitter chooses; the proof is a fixed tactic script.

    conjecture1_proved = False.  A numerical log enclosure, a building block.
-/
import CertVerify
import TaylorKernels
import Mathlib.Analysis.Complex.ExponentialBounds

open Real

namespace ForgeLogBracket

/-- `exp q ≤ (E1hi)^k * (expSeries f N + expRem f N)` when `q = k + f`, `|f| ≤ 1`, `exp 1 ≤ E1hi`
    (rational upper), `0 ≤ E1hi`, `N > 0`.  A rational UPPER bound for `exp q`. -/
theorem exp_le_rat {q f E1hi seriesUp : ℝ} {k N : ℕ}
    (hq : q = (k : ℝ) + f) (hf : |f| ≤ 1) (hN : 0 < N)
    (hE1 : Real.exp 1 ≤ E1hi) (hE1nn : 0 ≤ E1hi)
    (hser : TaylorKernels.expSeries f N + TaylorKernels.expRem f N ≤ seriesUp) :
    Real.exp q ≤ E1hi ^ k * seriesUp := by
  have hfexp : Real.exp f ≤ seriesUp := le_trans (TaylorKernels.exp_upper hf hN) hser
  have hkexp : Real.exp ((k : ℝ)) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hsplit : Real.exp q = Real.exp ((k : ℝ)) * Real.exp f := by
    rw [hq, Real.exp_add]
  rw [hsplit, hkexp]
  have hkle : (Real.exp 1) ^ k ≤ E1hi ^ k := by
    apply pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) hE1
  have hkpos : 0 ≤ (Real.exp 1) ^ k := by positivity
  have hfpos : 0 ≤ Real.exp f := le_of_lt (Real.exp_pos f)
  calc (Real.exp 1) ^ k * Real.exp f
      ≤ E1hi ^ k * Real.exp f := by gcongr
    _ ≤ E1hi ^ k * seriesUp := by gcongr

/-- `(E1lo)^k * (expSeries f N − expRem f N) ≤ exp q` when `q = k + f`, `|f| ≤ 1`,
    `E1lo ≤ exp 1` (rational lower), `0 ≤ E1lo`, `0 ≤ seriesLo`, `N > 0`.  A rational LOWER bound. -/
theorem rat_le_exp {q f E1lo seriesLo : ℝ} {k N : ℕ}
    (hq : q = (k : ℝ) + f) (hf : |f| ≤ 1) (hN : 0 < N)
    (hE1 : E1lo ≤ Real.exp 1) (hE1nn : 0 ≤ E1lo) (hserlo : 0 ≤ seriesLo)
    (hser : seriesLo ≤ TaylorKernels.expSeries f N - TaylorKernels.expRem f N) :
    E1lo ^ k * seriesLo ≤ Real.exp q := by
  have hfexp : seriesLo ≤ Real.exp f := le_trans hser (TaylorKernels.exp_lower hf hN)
  have hkexp : Real.exp ((k : ℝ)) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hsplit : Real.exp q = Real.exp ((k : ℝ)) * Real.exp f := by rw [hq, Real.exp_add]
  rw [hsplit, hkexp]
  have hkle : E1lo ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ hE1nn hE1 k
  calc E1lo ^ k * seriesLo
      ≤ (Real.exp 1) ^ k * seriesLo := by gcongr
    _ ≤ (Real.exp 1) ^ k * Real.exp f := by gcongr

/-- **The reusable nat-log bracket.**  `lo ≤ log n ≤ hi` for `n > 0`, given the two rational exp
    bounds assembled from `rat_le_exp` (`exp lo ≤ n`) and `exp_le_rat` (`n ≤ exp hi`).  The emitter
    supplies the decompositions `lo = klo + flo`, `hi = khi + fhi` and the rational `n`-comparisons. -/
theorem log_nat_bracket {n lo hi : ℝ} (hn : 0 < n)
    (hExpLo : Real.exp lo ≤ n) (hExpHi : n ≤ Real.exp hi) :
    lo ≤ Real.log n ∧ Real.log n ≤ hi :=
  CertVerify.ln_of_exp_bracket hn hExpLo hExpHi

/-- **Interval product with a nonneg left factor.**  If `0 ≤ xlo ≤ x ≤ xhi`, `ylo ≤ y ≤ yhi`, and
    rationals `plo, phi` bound the four corner products, then `x*y ∈ [plo,phi]`.  The forge's ζ-term
    amplitude `n^{-1/2}` is nonneg, so this covers Re/Im term boxes (trig factor of either sign). -/
theorem mul_encl {x y xlo xhi ylo yhi plo phi : ℝ} (hxlo0 : 0 ≤ xlo)
    (hx : xlo ≤ x ∧ x ≤ xhi) (hy : ylo ≤ y ∧ y ≤ yhi)
    (hL1 : plo ≤ xlo * ylo) (hL2 : plo ≤ xlo * yhi) (hL3 : plo ≤ xhi * ylo) (hL4 : plo ≤ xhi * yhi)
    (hU1 : xlo * ylo ≤ phi) (hU2 : xlo * yhi ≤ phi) (hU3 : xhi * ylo ≤ phi) (hU4 : xhi * yhi ≤ phi) :
    plo ≤ x * y ∧ x * y ≤ phi := by
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  have hx0 : 0 ≤ x := le_trans hxlo0 hxlo
  constructor
  · rcases le_total 0 y with hy0 | hy0
    · -- y ≥ 0: x*y ≥ xlo*y ≥ xlo*ylo (all nonneg)
      nlinarith [mul_le_mul_of_nonneg_right hxlo hy0, mul_le_mul_of_nonneg_left hylo hxlo0, hL1]
    · -- y ≤ 0: x*y ≥ xhi*y ≥ xhi*ylo
      nlinarith [mul_le_mul_of_nonpos_right hxhi hy0, mul_le_mul_of_nonneg_left hylo (le_trans hxlo0 hxlo), hL3]
  · rcases le_total 0 y with hy0 | hy0
    · -- y ≥ 0: x*y ≤ xhi*y ≤ xhi*yhi
      nlinarith [mul_le_mul_of_nonneg_right hxhi hy0, mul_le_mul_of_nonneg_left hyhi (le_trans hxlo0 hxlo), hU4]
    · -- y ≤ 0: x*y ≤ xlo*y ≤ xlo*yhi
      nlinarith [mul_le_mul_of_nonpos_right hxlo hy0, mul_le_mul_of_nonneg_left hyhi hxlo0, hU2]


end ForgeLogBracket