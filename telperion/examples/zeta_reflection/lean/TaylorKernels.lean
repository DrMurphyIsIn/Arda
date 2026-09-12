/-  TaylorKernels.lean -- computable truncated-series enclosures on DIntv (A1).

    Transcendental enclosures for the reflection evaluators: exp, cos, sin.  The design is
    VERIFY-NOT-COMPUTE at the top (an untrusted Arb pipeline supplies dyadic candidate
    brackets; the kernel checks them), but the once-proven Real remainder bounds live HERE,
    stated so that a candidate dyadic bracket that passes the checker denotes a true
    enclosure of the transcendental value.

    The Real backbone is Mathlib's:
      * `Real.exp_bound`  : |exp x − Σ_{m<n} xᵐ/m!| ≤ |x|ⁿ·(n+1)/(n!·n)   for |x| ≤ 1
      * `Real.cos_bound`  : |cos x − (1 − x²/2)|      ≤ |x|⁴·(5/96)         for |x| ≤ 1
      * `Real.sin_bound`  : |sin x − (x − x³/6)|      ≤ |x|⁵/100            for |x| ≤ 1
    plus monotonicity (`Real.exp_le_exp`) for argument-endpoint enclosure of exp.

    What is PROVEN sound here (no sorry):
      * `expSeries`/`expRem` two-sided bracket around `Real.exp` for `|x| ≤ 1`
        (`exp_lower` / `exp_upper`).
      * exp argument reduction by monotonicity: an enclosure of `exp` on an interval follows
        from enclosures of `exp` at the two endpoints (`expD_sound_of_endpoints`).
      * cos/sin reduced-argument two-sided brackets for `|x| ≤ 1`
        (`cos_lower`/`cos_upper`, `sin_lower`/`sin_upper`).

    PENDING (see the UNSOUND-pending section, EXCLUDED from the axiom guard): the
    DIntv-level term-by-term evaluation of the truncated polynomial `Σ xᵐ/m!` (division by
    factorials has no DIntv primitive — it is a CertVerify reciprocal-certificate job, and
    the exp/cos/sin candidate brackets are produced there).  The Real brackets below are the
    soundness contract those checkers discharge against.

    conjecture1_proved = False.
-/
import DIntvCorrect

open Real Finset

namespace TaylorKernels

/-! ### exp : two-sided series bracket for `|x| ≤ 1` -/

/-- The order-`n` Taylor partial sum of `exp` at `x`. -/
noncomputable def expSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)

/-- The Lagrange-style remainder majorant used by `Real.exp_bound`. -/
noncomputable def expRem (x : ℝ) (n : ℕ) : ℝ :=
  |x| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * (n : ℝ)))

/-- Lower bound: `exp x ≥ expSeries x n − expRem x n` for `|x| ≤ 1`, `0 < n`. -/
theorem exp_lower {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    expSeries x n - expRem x n ≤ Real.exp x := by
  have hb := Real.exp_bound hx hn
  have h2 := abs_le.mp hb
  unfold expSeries expRem
  linarith [h2.1]

/-- Upper bound: `exp x ≤ expSeries x n + expRem x n` for `|x| ≤ 1`, `0 < n`. -/
theorem exp_upper {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ expSeries x n + expRem x n := by
  have hb := Real.exp_bound hx hn
  have h2 := abs_le.mp hb
  unfold expSeries expRem
  linarith [h2.2]

/-- exp argument reduction by MONOTONICITY: if `[a, b]` contains `x` and the reals `lo, hi`
    satisfy `lo ≤ exp a` and `exp b ≤ hi`, then `lo ≤ exp x ≤ hi`.  This is the bridge that
    turns an interval-argument exp enclosure into two endpoint evaluations. -/
theorem exp_encl_of_endpoints {x a b lo hi : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hlo : lo ≤ Real.exp a) (hhi : Real.exp b ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  refine ⟨?_, ?_⟩
  · exact le_trans hlo (Real.exp_le_exp.mpr hax)
  · exact le_trans (Real.exp_le_exp.mpr hxb) hhi

/-- DIntv form of exp enclosure via endpoints: if a DIntv `R` has real endpoints `a = lo·2^e`
    and `b = hi·2^e` bracketing `x`, and dyadic candidates `E : DIntv` satisfy
    `E.lo·2^E.e ≤ exp a` and `exp b ≤ E.hi·2^E.e`, then `exp x ∈ᵣ E`.  The candidate `E`
    comes from the untrusted pipeline; this lemma is its soundness contract. -/
theorem expD_sound_of_endpoints {x : ℝ} {R E : DIntvProd.DIntv}
    (hx : R.memR x)
    (hlo : (E.lo : ℝ) * (2:ℝ) ^ E.e ≤ Real.exp ((R.lo : ℝ) * (2:ℝ) ^ R.e))
    (hhi : Real.exp ((R.hi : ℝ) * (2:ℝ) ^ R.e) ≤ (E.hi : ℝ) * (2:ℝ) ^ E.e) :
    E.memR (Real.exp x) := by
  obtain ⟨hax, hxb⟩ := hx
  exact exp_encl_of_endpoints hax hxb hlo hhi

/-! ### cos : two-sided reduced-argument bracket for `|x| ≤ 1`

    Mathlib's `cos_bound` centers on the 2-term series `1 − x²/2` with remainder `|x|⁴·5/96`.
    (Full argument reduction mod 2π is DEFERRED to CertVerify's π enclosure per the plan; we
    state the reduced-argument versions here.) -/

/-- The 2-term cos series `1 − x²/2`. -/
noncomputable def cosSeries (x : ℝ) : ℝ := 1 - x ^ 2 / 2

/-- cos remainder majorant `|x|⁴·(5/96)`. -/
noncomputable def cosRem (x : ℝ) : ℝ := |x| ^ 4 * (5 / 96)

/-- Lower bound for cos, reduced arg `|x| ≤ 1`. -/
theorem cos_lower {x : ℝ} (hx : |x| ≤ 1) : cosSeries x - cosRem x ≤ Real.cos x := by
  have hb := Real.cos_bound hx
  have h2 := abs_le.mp hb
  unfold cosSeries cosRem
  linarith [h2.1]

/-- Upper bound for cos, reduced arg `|x| ≤ 1`. -/
theorem cos_upper {x : ℝ} (hx : |x| ≤ 1) : Real.cos x ≤ cosSeries x + cosRem x := by
  have hb := Real.cos_bound hx
  have h2 := abs_le.mp hb
  unfold cosSeries cosRem
  linarith [h2.2]

/-! ### sin : two-sided reduced-argument bracket for `|x| ≤ 1` -/

/-- The 2-term sin series `x − x³/6`. -/
noncomputable def sinSeries (x : ℝ) : ℝ := x - x ^ 3 / 6

/-- sin remainder majorant `|x|⁵/100`. -/
noncomputable def sinRem (x : ℝ) : ℝ := |x| ^ 5 / 100

/-- Lower bound for sin, reduced arg `|x| ≤ 1`. -/
theorem sin_lower {x : ℝ} (hx : |x| ≤ 1) : sinSeries x - sinRem x ≤ Real.sin x := by
  have hb := Real.sin_bound hx
  have h2 := abs_le.mp hb
  unfold sinSeries sinRem
  linarith [h2.1]

/-- Upper bound for sin, reduced arg `|x| ≤ 1`. -/
theorem sin_upper {x : ℝ} (hx : |x| ≤ 1) : Real.sin x ≤ sinSeries x + sinRem x := by
  have hb := Real.sin_bound hx
  have h2 := abs_le.mp hb
  unfold sinSeries sinRem
  linarith [h2.2]

/-- DIntv soundness contract for cos on a reduced-argument box: a candidate `C : DIntv`
    whose real endpoints bracket `cosSeries ∓ cosRem` at the argument-box endpoints encloses
    `cos x`.  Because `cosSeries`/`cosRem` are polynomial in `x`, the box evaluation of these
    is pure DIntv arithmetic (add/mul/abs from `DIntvCorrect`); the reciprocal `/2`, `/6`,
    `5/96`, `/100` are dyadic-exact-enough and enter as CertVerify reciprocal certificates.
    Here `sLo ≤ cosSeries x − cosRem x` and `cosSeries x + cosRem x ≤ sHi` are the hypotheses
    the checker supplies, and monotone containment gives `cos x ∈ [sLo, sHi]`. -/
theorem cosD_sound_of_bracket {x sLo sHi : ℝ} (hx : |x| ≤ 1)
    (hlo : sLo ≤ cosSeries x - cosRem x) (hhi : cosSeries x + cosRem x ≤ sHi) :
    sLo ≤ Real.cos x ∧ Real.cos x ≤ sHi :=
  ⟨le_trans hlo (cos_lower hx), le_trans (cos_upper hx) hhi⟩

/-- DIntv soundness contract for sin on a reduced-argument box (see `cosD_sound_of_bracket`). -/
theorem sinD_sound_of_bracket {x sLo sHi : ℝ} (hx : |x| ≤ 1)
    (hlo : sLo ≤ sinSeries x - sinRem x) (hhi : sinSeries x + sinRem x ≤ sHi) :
    sLo ≤ Real.sin x ∧ Real.sin x ≤ sHi :=
  ⟨le_trans hlo (sin_lower hx), le_trans (sin_upper hx) hhi⟩

/-! ### Computable DIntv Horner kernel (benchmark target)

    Division-free Horner evaluation of `Σ cₖ·xᵏ` where the reciprocal-factorial coefficients
    `cₖ` are supplied as pre-enclosed dyadic DIntv constants (the untrusted pipeline pins them;
    CertVerify's reciprocal certificates discharge `1/k! ∈ cₖ`).  This is the pure-Int,
    structural, kernel-hot-path object measured by the A1 micro-benchmark.  It carries no
    soundness proof itself -- soundness is `expD_sound_of_endpoints` against the checker. -/

open DIntvProd DIntvProd.DIntv

/-- Force a DIntv to a target exponent `eT` by outward rounding when coarsening (`eT ≥ e`);
    when refining (`eT < e`) it is an exact left-shift of the mantissas.  Pure Int, structural.
    Used to align Horner accumulands to a common per-band exponent. -/
def forceExp (I : DIntv) (eT : Int) : DIntv :=
  if I.e ≤ eT then
    I.roundTo (eT - I.e).toNat            -- coarsen outward (roundTo raises e to eT; d=0 keeps)
  else
    ⟨I.lo <<< (I.e - eT).toNat, I.hi <<< (I.e - eT).toNat, eT⟩   -- refine (exact shift)

/-- `forceExp` always lands at the target exponent. -/
@[simp] theorem forceExp_e (I : DIntv) (eT : Int) : (forceExp I eT).e = eT := by
  unfold forceExp
  split <;> rename_i h
  · simp only [DIntvProd.DIntv.roundTo]
    omega
  · rfl

/-- Horner fold at a FIXED per-band accumulator exponent `eA`: `(…(cₙ·x + cₙ₋₁)·x + …) + c₀`,
    coeffs high-degree first.  Each product is `roundTo`'d then forced to `eA` and added to the
    next (pinned) coefficient.  Structural recursion over the coeff list; the whole thing is
    pure-Int `mul`/`add`/shift -- the kernel-hot-path object the A1 micro-benchmark measures. -/
def hornerD (x : DIntv) (eA : Int) (dropBits : Nat) : List DIntv → DIntv
  | []       => ofInt 0
  | [c]      => forceExp c eA
  | c :: cs  =>
      let tail := hornerD x eA dropBits cs
      let prod := forceExp ((tail.mul x).roundTo dropBits) eA
      let c'   := forceExp c eA
      add prod c' (by simp only [prod, c', forceExp_e])

end TaylorKernels
