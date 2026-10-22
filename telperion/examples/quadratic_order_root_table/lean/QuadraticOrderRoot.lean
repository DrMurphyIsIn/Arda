/-
QuadraticOrderRoot -- the prelude behind Telperion's `quadratic_order_root_table` emitter.

Ported to Lean v4.32.0 / Mathlib v4.32.0 from the kernel-checked CN-1 formalization of the
class-number-one theorem (DrMurphyIsIn/tenth-discriminant, formalization/CN1: Finite/Elementary,
Finite/SplitPrime, Finite/Converse, Foundations/Splitting, Foundations/Ramified; Lean v4.34.1,
Mathlib d13f23b).  The CN-1 files work with the specific orders `ℤ[ω]` of `ℚ(√-m)`; here the
order is abstract, through the `QuadInt` interface of SplitPrime.lean: `𝓞 K = ℤ[θ]`,
`minpoly θ = X² - t·X + c`, norm form `x² + t·x·y + c·y²`, `d = 4c - t²`, with `t, c : ℕ`.

Decidable faces (pure `ℕ`, closed by `decide`; primality by `norm_num`):

* ROOT      `IsRootMod t c p y`: `y² - t·y + c ≡ 0 (mod p)`, written without truncated subtraction;
* NO-ROOT   `∀ z : ZMod p, z ^ 2 - t * z + c ≠ 0` (a raw quantifier over the `p`-element field);
* RAMIFIED  `p ∣ 4 * c - t ^ 2` with `t ^ 2 < 4 * c`;
* WITNESS   `IsWitness t c p y`: `p` prime, ROOT, `4p ≤ d`, `p ≠ c` (the Rabinowitsch input).

Consumers (Mathlib's Kummer-Dedekind `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`):
`QuadInt.split_of_isRootMod` (two primes over `p`, inertia degree 1, when `p ∤ d`),
`QuadInt.inert_of_no_root` (one prime, inertia degree 2), `QuadInt.ramified_of_dvd` (one prime,
inertia degree 1, ramification index 2), `QuadInt.not_absNorm_eq_of_no_root` (no prime of norm
`p`, the Minkowski-side form), and `classNumber_ne_one_of_isWitness` (`h ≠ 1`).

The hypothesis `p ≠ c` in `IsWitness` is load-bearing: for `t = 0` the ramified prime `p = c = d/4`
IS represented by the principal form (`Q(0, 1) = c`), so without it `IsWitness 0 2 2 0` would
hold while `h(-8) = 1`.  See `not_isWitness_two_two` below.

Every proof is complete and kernel-checked; no `decide` is replaced by its native variant, no
proof is left open, and no axiom is added.  conjecture1_proved = False.
-/
import Mathlib

namespace QuadraticOrderRoot

open NumberField Ideal Module Polynomial

/-! ## The principal form `Q(x, y) = x² + t·x·y + c·y²` (pure integer arithmetic) -/

theorem four_mul_form (t c x y : ℤ) :
    4 * (x ^ 2 + t * x * y + c * y ^ 2) = (2 * x + t * y) ^ 2 + (4 * c - t ^ 2) * y ^ 2 := by
  ring

theorem form_nonneg {t c : ℤ} (hd : 0 ≤ 4 * c - t ^ 2) (x y : ℤ) :
    0 ≤ x ^ 2 + t * x * y + c * y ^ 2 := by
  have h := four_mul_form t c x y
  nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd (sq_nonneg y)]

/-- A prime is not a perfect square. -/
theorem not_prime_eq_sq {p : ℕ} (hp : p.Prime) (x : ℤ) : (p : ℤ) ≠ x ^ 2 := by
  intro h
  have h' : p = x.natAbs ^ 2 := by
    have : (p : ℤ) = (x.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq]; exact h
    exact_mod_cast this
  have hdvd : x.natAbs ∣ p := ⟨x.natAbs, by rw [h']; ring⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1] at h'; exact hp.one_lt.ne' (by simpa using h')
  · rw [h1] at h'
    have := hp.two_le
    nlinarith

/-- **The representation bound.** If `t ∈ {0, 1}`, `p` is prime, `4p ≤ d = 4c - t²` and `p ≠ c`,
then `Q(x, y) = x² + t·x·y + c·y² ≠ p` for all integers `x, y`. -/
theorem not_form_eq_prime {t c : ℤ} (ht : t = 0 ∨ t = 1) {p : ℕ} (hp : p.Prime)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) (x y : ℤ)
    (h : x ^ 2 + t * x * y + c * y ^ 2 = p) : False := by
  have h4 := four_mul_form t c x y
  rw [h] at h4
  have hp0 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    exact not_prime_eq_sq hp x (by linarith)
  · have hy1 : 1 ≤ y ^ 2 := by
      have := Int.one_le_abs hy
      nlinarith [sq_abs y]
    have hd0 : 0 ≤ 4 * c - t ^ 2 := by linarith
    -- 4p = (2x + ty)² + d·y² ≥ d ≥ 4p forces (2x + ty)² = 0 and d·(y² - 1) = 0
    have hsq : (2 * x + t * y) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * x + t * y), mul_nonneg hd0 (sub_nonneg.mpr hy1)]
    have hy2 : y ^ 2 = 1 := by
      have hdpos : 0 < 4 * c - t ^ 2 := by linarith
      have : (4 * c - t ^ 2) * (y ^ 2 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hdpos.ne'
      · linarith
    have hlin : 2 * x + t * y = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
    have hy' : y = 1 ∨ y = -1 :=
      Int.eq_one_or_neg_one_of_mul_eq_one (by rw [← sq]; exact hy2)
    rcases ht with rfl | rfl
    · -- t = 0: x = 0 and p = c·y² = c
      have hx : x = 0 := by linarith
      subst hx
      rw [hy2] at h
      apply hpc
      linarith
    · -- t = 1: 2x + y = 0 with y = ±1 is a parity contradiction
      rcases hy' with rfl | rfl <;> omega

/-! ## The decidable faces -/

/-- ROOT face: `y` is a root of `X² - t·X + c` modulo `p`, stated over `ℕ` so that `decide`
closes it (the first conjunct keeps the subtraction honest). -/
def IsRootMod (t c p y : ℕ) : Prop := t * y ≤ y ^ 2 + c ∧ p ∣ y ^ 2 + c - t * y

instance (t c p y : ℕ) : Decidable (IsRootMod t c p y) :=
  inferInstanceAs (Decidable (t * y ≤ y ^ 2 + c ∧ p ∣ y ^ 2 + c - t * y))

/-- The `ℕ` root is a root in `ZMod p`. -/
theorem IsRootMod.zmod_eq_zero {t c p y : ℕ} (h : IsRootMod t c p y) :
    (y : ZMod p) ^ 2 - (t : ZMod p) * y + c = 0 := by
  have h0 : ((y ^ 2 + c - t * y : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h.2
  rw [Nat.cast_sub h.1] at h0
  push_cast at h0
  linear_combination h0

/-- WITNESS face: `p` prime, `y² - t·y + c ≡ 0 (mod p)`, `4p ≤ d = 4c - t²`, `p ≠ c`.
This is CN-1's `IsWitness m p y` with `(tOf m, cOf m, dOf m)` replaced by `(t, c, 4c - t²)`. -/
def IsWitness (t c p y : ℕ) : Prop :=
  p.Prime ∧ t * y ≤ y ^ 2 + c ∧ p ∣ y ^ 2 + c - t * y ∧ 4 * p ≤ 4 * c - t ^ 2 ∧ p ≠ c

theorem IsWitness.isRootMod {t c p y : ℕ} (h : IsWitness t c p y) : IsRootMod t c p y :=
  ⟨h.2.1, h.2.2.1⟩

/-- The structural control (REVIEW_E C2): for `d = 8` (`t = 0`, `c = 2`) and `p = 2 = c`, `y = 0`,
every conjunct of `IsWitness` except `p ≠ c` holds, and `h(-8) = 1`.  So `p ≠ c` cannot be
dropped from the predicate; it is the only conjunct that refuses this instance. -/
theorem not_isWitness_two_two : ¬ IsWitness 0 2 2 0 := fun h => h.2.2.2.2 rfl

theorem isWitness_two_two_other_conjuncts :
    Nat.Prime 2 ∧ 0 * 0 ≤ 0 ^ 2 + 2 ∧ 2 ∣ 0 ^ 2 + 2 - 0 * 0 ∧ 4 * 2 ≤ 4 * 2 - 0 ^ 2 :=
  ⟨by norm_num, by decide, by decide, by decide⟩

/-! ## The order `𝓞 K = ℤ[θ]`, `θ² = t·θ - c` -/

variable {K : Type*} [Field K] [NumberField K]

/-- The algebraic data of a monogenic quadratic ring of integers `𝓞 K = ℤ[θ]`,
`minpoly θ = X² - t·X + c`.  Every field is a hypothesis: the consumer theorems are conditional
on it, and a project that builds `𝓞 K` (CN-1's `quadIntOfFoundations`) discharges it. -/
structure QuadInt (K : Type*) [Field K] [NumberField K] (t c : ℕ) where
  /-- a generator of the ring of integers -/
  θ : 𝓞 K
  /-- `𝓞 K = ℤ[θ]`; equivalently `RingOfIntegers.exponent θ = 1` -/
  adjoin_eq_top : Algebra.adjoin ℤ {θ} = ⊤
  /-- the minimal polynomial of `θ` over `ℤ` -/
  minpoly_eq : minpoly ℤ θ = X ^ 2 - C (t : ℤ) * X + C (c : ℤ)
  /-- the norm form -/
  norm_eq : ∀ x y : ℤ,
    Algebra.norm ℤ ((x : 𝓞 K) + (y : 𝓞 K) * θ) = x ^ 2 + t * x * y + c * y ^ 2

namespace QuadInt

variable {t c : ℕ} (D : QuadInt K t c)

/-- Every element of `𝓞 K = ℤ[θ]` with `deg (minpoly θ) = 2` is `x + y·θ`, `x, y ∈ ℤ`. -/
theorem exists_eq_add_mul (β : 𝓞 K) : ∃ x y : ℤ, β = (x : 𝓞 K) + (y : 𝓞 K) * D.θ := by
  have hβmem : β ∈ Algebra.adjoin ℤ {D.θ} := by rw [D.adjoin_eq_top]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβmem
  obtain ⟨f, hf⟩ := hβmem
  set g := minpoly ℤ D.θ with hg
  have hgm : g.Monic := minpoly.monic D.θ.isIntegral
  have h2 : g.natDegree = 2 := by rw [hg, D.minpoly_eq]; compute_degree!
  have hg1 : g ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hdeg : (f %ₘ g).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f hgm hg1
    omega
  obtain ⟨a, b, hr⟩ : ∃ a b : ℤ, f %ₘ g = C b * X + C a :=
    ⟨_, _, eq_X_add_C_of_natDegree_le_one hdeg⟩
  refine ⟨a, b, ?_⟩
  change (aeval D.θ) f = β at hf
  have hg0 : aeval D.θ g = 0 := by rw [hg]; exact minpoly.aeval ℤ D.θ
  rw [← hf]
  conv_lhs => rw [← modByMonic_add_div f g]
  rw [map_add, map_mul, hg0, zero_mul, add_zero, hr]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  simp only [algebraMap_int_eq, eq_intCast]
  ring

/-- `θ² = t·θ - c` in `𝓞 K`. -/
theorem theta_sq : D.θ ^ 2 = (t : 𝓞 K) * D.θ - (c : 𝓞 K) := by
  have h := minpoly.aeval ℤ D.θ
  rw [D.minpoly_eq] at h
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, aeval_X] at h
  linear_combination h

theorem exponent_eq_one : RingOfIntegers.exponent D.θ = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top

theorem not_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ p ∣ RingOfIntegers.exponent D.θ := by
  rw [D.exponent_eq_one]; exact hp.out.not_dvd_one

/-- `minpoly θ` reduced modulo `p`. -/
theorem minpoly_map (p : ℕ) :
    (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) =
      X ^ 2 - C (t : ZMod p) * X + C (c : ZMod p) := by
  rw [D.minpoly_eq]
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

end QuadInt

/-! ## Monic quadratics over `ZMod p` -/

section Quad

variable (p : ℕ) [hp : Fact p.Prime]

/-- A monic quadratic with a root `r` factors as `(X - r)(X - (a - r))`. -/
lemma quad_eq_mul_of_root (a b r : ZMod p) (hr : r ^ 2 - a * r + b = 0) :
    X ^ 2 - C a * X + C b = (X - C r) * (X - C (a - r)) := by
  have hb : b = a * r - r ^ 2 := by linear_combination hr
  rw [hb]
  simp only [map_sub, map_mul, map_pow]
  ring

lemma natDegree_quad (a b : ZMod p) : (X ^ 2 - C a * X + C b).natDegree = 2 := by
  compute_degree!

lemma monic_quad (a b : ZMod p) : (X ^ 2 - C a * X + C b).Monic := by
  monicity!

/-- A monic quadratic without roots is irreducible. -/
lemma irreducible_quad_of_no_root (a b : ZMod p) (h : ∀ x : ZMod p, x ^ 2 - a * x + b ≠ 0) :
    Irreducible (X ^ 2 - C a * X + C b) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_quad]; decide
  · intro x hx
    apply h x
    rw [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
    exact hx

lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

end Quad

/-! ## Kummer-Dedekind at the order: the three faces -/

namespace QuadInt

section KDHelpers

variable {t c : ℕ} (D : QuadInt K t c) (p : ℕ) [hp : Fact p.Prime]

/-- If `X² - tX + c` has a root `r` mod `p`, the Kummer-Dedekind factor set is
`{X - r, X - (t - r)}`. -/
theorem monicFactorsMod_of_root {r : ZMod p} (hr : r ^ 2 - (t : ZMod p) * r + c = 0) :
    RingOfIntegers.monicFactorsMod D.θ p = {X - C r, X - C ((t : ZMod p) - r)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [D.minpoly_map p, quad_eq_mul_of_root p _ _ r hr,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, (monic_X_sub_C _).normalize_eq_self,
    Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]

/-- If `X² - tX + c` has no root mod `p`, the Kummer-Dedekind factor set is `{X² - tX + c}`. -/
theorem monicFactorsMod_of_no_root
    (h : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + c ≠ 0) :
    RingOfIntegers.monicFactorsMod D.θ p = {X ^ 2 - C (t : ZMod p) * X + C (c : ZMod p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [D.minpoly_map p,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_quad_of_no_root p _ _ h),
    (monic_quad p _ _).normalize_eq_self, Multiset.toFinset_singleton]

/-- The number of primes over `p` is the number of monic irreducible factors of `minpoly θ`
mod `p` (Kummer-Dedekind). -/
theorem ncard_primesOver_eq_card_monicFactorsMod :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = (RingOfIntegers.monicFactorsMod D.θ p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p)),
    Nat.card_eq_finsetCard]

/-- The inertia degree of a prime over `p` is the degree of its Kummer-Dedekind factor. -/
theorem inertiaDeg_eq_natDegree {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    P.inertiaDeg ℤ =
      ((Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p) ⟨P, hP⟩ :
        (ZMod p)[X])).natDegree := by
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p)
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (D.not_dvd_exponent p) (e ⟨P, hP⟩).2
  rwa [Subtype.coe_eta, e.symm_apply_apply] at this

end KDHelpers

section Consumers

variable {t c : ℕ} (D : QuadInt K t c) (p : ℕ)

include D in
/-- **SPLIT.**  A root `y` of `X² - tX + c` mod `p` with `p ∤ d = 4c - t²`: exactly two primes of
`𝓞 K` over `p`, each of inertia degree `1`. -/
theorem split_of_isRootMod (hp : p.Prime) (hpd : ¬ p ∣ 4 * c - t ^ 2) {y : ℕ}
    (hy : IsRootMod t c p y) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 := by
  haveI := Fact.mk hp
  have hr := hy.zmod_eq_zero (p := p)
  have hF := monicFactorsMod_of_root D p hr
  have hle : t ^ 2 ≤ 4 * c := by
    by_contra hlt
    apply hpd
    rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hlt))]
    exact dvd_zero p
  have hne : X - C (y : ZMod p) ≠ X - C ((t : ZMod p) - y) := by
    intro h
    have h2 : (y : ZMod p) = (t : ZMod p) - y := C_inj.mp (sub_right_injective h)
    have h2' : 2 * (y : ZMod p) - t = 0 := by linear_combination h2
    apply hpd
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hle]
    push_cast
    linear_combination 4 * hr - (2 * (y : ZMod p) - t) * h2'
  refine ⟨?_, fun P hP => ?_⟩
  · rw [D.ncard_primesOver_eq_card_monicFactorsMod p, hF]
    exact Finset.card_pair hne
  · rw [D.inertiaDeg_eq_natDegree p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p) ⟨P, hP⟩).2
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h, natDegree_X_sub_C]

include D in
/-- **INERT.**  No root of `X² - tX + c` mod `p`: exactly one prime of `𝓞 K` over `p`, of inertia
degree `2`. -/
theorem inert_of_no_root (hp : p.Prime)
    (h : ∀ z : ZMod p, z ^ 2 - (t : ZMod p) * z + (c : ZMod p) ≠ 0) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 := by
  haveI := Fact.mk hp
  have hF := monicFactorsMod_of_no_root D p h
  refine ⟨?_, fun P hP => ?_⟩
  · rw [D.ncard_primesOver_eq_card_monicFactorsMod p, hF, Finset.card_singleton]
  · rw [D.inertiaDeg_eq_natDegree p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p) ⟨P, hP⟩).2
    rw [Finset.mem_singleton] at hmem
    rw [hmem, natDegree_quad]

end Consumers

end QuadInt

/-! ## The ramified face `p ∣ d` -/

section Ramified

variable (t c p : ℕ)

/-- The double root of `X² - tX + c` mod `p ∣ d`: `t/2` for odd `p`, `c` for `p = 2`. -/
noncomputable def doubleRoot : ZMod p :=
  if p = 2 then (c : ZMod p) else (t : ZMod p) * 2⁻¹

lemma zmod_two_aux₁ : ∀ c : ZMod 2, 2 * c = 0 := by decide

lemma zmod_two_aux₂ : ∀ c : ZMod 2, c ^ 2 - 0 * c + c = 0 := by decide

lemma two_dvd_of_dvd_disc (hd : t ^ 2 < 4 * c) (hpd : 2 ∣ 4 * c - t ^ 2) : 2 ∣ t := by
  have h4 : 2 ∣ 4 * c := ⟨2 * c, by ring⟩
  have h2 : 2 ∣ 4 * c - (4 * c - t ^ 2) := Nat.dvd_sub h4 hpd
  rw [Nat.sub_sub_self hd.le] at h2
  exact Nat.prime_two.dvd_of_dvd_pow h2

lemma disc_cast_eq_zero (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    (4 : ZMod p) * c - (t : ZMod p) ^ 2 = 0 := by
  have h0 : ((4 * c - t ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
  rw [Nat.cast_sub hd.le] at h0
  push_cast at h0
  exact h0

lemma two_mul_doubleRoot [hp : Fact p.Prime] (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    2 * doubleRoot t c p = (t : ZMod p) := by
  unfold doubleRoot
  split_ifs with h2
  · subst h2
    have ht : (t : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (two_dvd_of_dvd_disc t c hd hpd)
    rw [ht]
    exact zmod_two_aux₁ _
  · have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ (two_ne_zero_of_ne_two p h2)
    linear_combination (t : ZMod p) * hi

lemma doubleRoot_isRoot [hp : Fact p.Prime] (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    doubleRoot t c p ^ 2 - (t : ZMod p) * doubleRoot t c p + c = 0 := by
  have hd0 := disc_cast_eq_zero t c p hd hpd
  unfold doubleRoot
  split_ifs with h2
  · subst h2
    have ht : (t : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (two_dvd_of_dvd_disc t c hd hpd)
    rw [ht]
    exact zmod_two_aux₂ _
  · have h2' := two_ne_zero_of_ne_two p h2
    have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2'
    have h4 : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2' h2'
    have key : (4 : ZMod p) * (((t : ZMod p) * 2⁻¹) ^ 2 - t * ((t : ZMod p) * 2⁻¹) + c) = 0 := by
      linear_combination hd0 + (t : ZMod p) ^ 2 * (2 * 2⁻¹ - 1) * hi
    exact (mul_eq_zero.mp key).resolve_left h4

end Ramified

namespace QuadInt

section RamifiedHelpers

variable {t c : ℕ} (D : QuadInt K t c) (p : ℕ) [hp : Fact p.Prime]

/-- For `p ∣ d`, `minpoly θ ≡ (X - r)²` mod `p`. -/
theorem minpoly_map_of_dvd (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) = (X - C (doubleRoot t c p)) ^ 2 := by
  have hr : (t : ZMod p) - doubleRoot t c p = doubleRoot t c p := by
    linear_combination (-1 : ZMod p) * two_mul_doubleRoot t c p hd hpd
  rw [D.minpoly_map p, quad_eq_mul_of_root p _ _ _ (doubleRoot_isRoot t c p hd hpd), hr, sq]

/-- For `p ∣ d`, the Kummer-Dedekind factor set is `{X - r}`. -/
theorem monicFactorsMod_of_dvd (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    RingOfIntegers.monicFactorsMod D.θ p = {X - C (doubleRoot t c p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [D.minpoly_map_of_dvd p hd hpd, sq,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, Multiset.singleton_add, Multiset.toFinset_cons,
    Multiset.toFinset_singleton, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]

end RamifiedHelpers

section Consumers

variable {t c : ℕ} (D : QuadInt K t c) (p : ℕ)

include D in
/-- **RAMIFIED.**  For `p ∣ d = 4c - t²` (with `d > 0`) there is exactly one prime of `𝓞 K` over
`p`, with inertia degree `1` and ramification index `2`. -/
theorem ramified_of_dvd (hp : p.Prime) (hd : t ^ 2 < 4 * c) (hpd : p ∣ 4 * c - t ^ 2) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 := by
  haveI := Fact.mk hp
  have hF := monicFactorsMod_of_dvd D p hd hpd
  refine ⟨by rw [D.ncard_primesOver_eq_card_monicFactorsMod p, hF, Finset.card_singleton],
    fun P hP => ?_⟩
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (D.not_dvd_exponent p)
  have hmem := (Finset.ext_iff.mp hF _).mp (e ⟨P, hP⟩).2
  rw [Finset.mem_singleton] at hmem
  constructor
  · rw [D.inertiaDeg_eq_natDegree p hP, hmem, natDegree_X_sub_C]
  · have := Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
      (D.not_dvd_exponent p) (e ⟨P, hP⟩).2
    rw [Subtype.coe_eta, e.symm_apply_apply, hmem, D.minpoly_map_of_dvd p hd hpd,
      multiplicity_pow_self (X_sub_C_ne_zero _) (not_isUnit_X_sub_C _)] at this
    exact this

end Consumers

end QuadInt

/-! ## The Minkowski-side form of NO-ROOT: no prime of norm `p` -/

/-- If `θ ∈ 𝓞 K` satisfies `θ² = t·θ - c` and the polynomial `z² - t·z + c` has no root in
`ZMod q`, then no maximal ideal of `𝓞 K` has norm `q` (such an ideal would have residue field
`ZMod q` containing the image of `θ`). -/
theorem not_absNorm_eq_of_no_root (θ : 𝓞 K) (t c : ℤ)
    (hθ : θ ^ 2 = (t : 𝓞 K) * θ - (c : 𝓞 K))
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (q : ℕ) (hq : q.Prime) (hN : absNorm P = q)
    (hroot : ∀ z : ZMod q, z ^ 2 - (t : ZMod q) * z + (c : ZMod q) ≠ 0) : False := by
  haveI := Fact.mk hq
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = q := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← absNorm_apply, hN]
  haveI : CharP (𝓞 K ⧸ P) q := charP_of_card_eq_prime hcard
  let f : ZMod q →+* 𝓞 K ⧸ P := ZMod.castHom dvd_rfl _
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P θ)
  apply hroot z
  apply f.injective
  have hθ' := congrArg (Ideal.Quotient.mk P) hθ
  simp only [map_pow, map_sub, map_mul, map_intCast] at hθ'
  rw [map_add, map_sub, map_mul, map_pow, map_zero, hz, map_intCast, map_intCast, hθ']
  ring

/-- The same for a `QuadInt`, from the NO-ROOT face. -/
theorem QuadInt.not_absNorm_eq_of_no_root {t c : ℕ} (D : QuadInt K t c)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (q : ℕ) (hq : q.Prime) (hN : absNorm P = q)
    (hroot : ∀ z : ZMod q, z ^ 2 - (t : ZMod q) * z + (c : ZMod q) ≠ 0) : False :=
  QuadraticOrderRoot.not_absNorm_eq_of_no_root D.θ t c (by rw [D.theta_sq]; push_cast; ring)
    P q hq hN (fun z => by have := hroot z; push_cast; exact this)

/-! ## The Rabinowitsch step: a small degree-one prime forces `h ≠ 1` -/

/-- **The finite-part lemma** (CN-1 `classNumber_ne_one_of_witness`).  If `y² - t·y + c ≡ 0 (mod p)`,
`4p ≤ d = 4c - t²` and `p ≠ c`, then `classNumber K ≠ 1`.  By Kummer-Dedekind the ideal
`P = (p, θ - y)` is a prime of residue degree one, so `absNorm P = p`; if `𝓞 K` were a PID,
`P = (β)` and `|N(β)| = p`, i.e. `Q(x, y) = p`, which `not_form_eq_prime` rules out. -/
theorem classNumber_ne_one_of_witness {t c : ℕ} (D : QuadInt K t c) (ht : t = 0 ∨ t = 1)
    (p : ℕ) (hp : p.Prime) (y : ℤ) (hy : (p : ℤ) ∣ y ^ 2 - t * y + c)
    (hb : 4 * (p : ℤ) ≤ 4 * c - t ^ 2) (hpc : (p : ℤ) ≠ c) : classNumber K ≠ 1 := by
  intro h1
  haveI := Fact.mk hp
  haveI hpid : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  -- Kummer-Dedekind applies: `p ∤ exponent θ = 1`
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := D.not_dvd_exponent p
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  -- `X - y` is a monic irreducible factor of `minpoly θ` mod `p`
  have hQ : (X - C y).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod D.θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff hmap0, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, D.minpoly_eq]
    have hy' : ((y ^ 2 - t * y + c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
    simp only [IsRoot.def, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    push_cast at hy'
    linear_combination hy'
  -- the corresponding prime `P` has residue degree one, so `absNorm P = p`
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  haveI hPprime : P.IsPrime := hPmem.1
  haveI hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  have hPnorm : absNorm P = p := by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]
  -- in a PID, `P = (β)` with `|N β| = p`, and `β = x + y·θ`
  obtain ⟨β, hβ⟩ := Submodule.IsPrincipal.principal P
  rw [hβ, Ideal.submodule_span_eq, absNorm_span_singleton] at hPnorm
  obtain ⟨x, y', hxy⟩ := D.exists_eq_add_mul β
  rw [hxy, D.norm_eq] at hPnorm
  have hd0 : 0 ≤ 4 * (c : ℤ) - t ^ 2 := by
    have : (0 : ℤ) ≤ p := by positivity
    linarith
  have hQnn := form_nonneg hd0 x y'
  have hform : x ^ 2 + t * x * y' + c * y' ^ 2 = p := by
    rcases Int.natAbs_eq_iff.mp hPnorm with h | h
    · exact h
    · have : (0 : ℤ) < p := by exact_mod_cast hp.pos
      linarith
  have ht' : (t : ℤ) = 0 ∨ (t : ℤ) = 1 := by
    rcases ht with h | h <;> simp [h]
  exact not_form_eq_prime ht' hp hb hpc x y' hform

/-- The witness face consumed: `IsWitness t c p y` (pure `ℕ`, kernel-decided) gives `h ≠ 1`. -/
theorem classNumber_ne_one_of_isWitness {t c : ℕ} (D : QuadInt K t c) (ht : t = 0 ∨ t = 1)
    {p y : ℕ} (hw : IsWitness t c p y) : classNumber K ≠ 1 := by
  obtain ⟨hp, hle, hdvd, hb, hpc⟩ := hw
  have hd : t ^ 2 ≤ 4 * c := by
    have := hp.two_le
    omega
  have hb' : 4 * (p : ℤ) ≤ 4 * c - t ^ 2 := by
    have h := (Nat.cast_le (α := ℤ)).mpr hb
    rw [Nat.cast_sub hd] at h
    push_cast at h
    exact h
  refine classNumber_ne_one_of_witness D ht p hp y ?_ hb' (by exact_mod_cast hpc)
  have := Int.natCast_dvd_natCast.mpr hdvd
  rw [Nat.cast_sub hle] at this
  push_cast at this
  convert this using 1
  ring

end QuadraticOrderRoot
