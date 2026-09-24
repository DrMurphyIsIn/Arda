# Assemble telperion/examples/rvm_bridge/lean/Crux/Crux2_verified_window.lean from
#   header.lean.part   (module docstring: status, establishes / does not)
#   generic_part.lean  (imports; sections B, C, D-generic)
#   instance part      (generated from a certificate JSON)
#   gluing part        (Theorem 2 skeleton on the E8 explicit formula)
import json, sys, math
from fractions import Fraction as Fr
from emit_instance import emit_instance, frac_lean
from logbounds import compute as log_compute

def nonpp(nmax=99):
    out = []
    for n in range(0, nmax + 1):
        if n < 2:
            out.append((n, None, None)); continue
        m = n; p = None
        for d in range(2, n + 1):
            if m % d == 0:
                p = d; break
        a = 1
        while m % p == 0:
            m //= p; a *= p
        if m != 1:
            out.append((n, a, n // a))
    return out

INSTANCE_HEAD = r'''
section Instance

open ArithmeticFunction

/-- Per-entry facts for a prime power `n = p^k` from an enclosure of `log p` and a lower bound `s ≤ √n`. -/
lemma entryOK_of {q S : ℝ} {n p k C A B : ℕ} {lo hi s : ℝ}
    (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (hlog : lo < Real.log p ∧ Real.log p < hi)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ (n : ℝ))
    (hA : (A : ℝ) * q ≤ k * lo) (hB : (k : ℝ) * hi ≤ (B : ℝ) * q) (hC : hi / s ≤ (C : ℝ) / S) :
    EntryOK q S (n, C, A, B) := by
  subst hn
  have hΛ : Λ (p ^ k) = Real.log p := by rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  have hlogn : Real.log (((p ^ k : ℕ) : ℝ)) = k * Real.log p := by push_cast; rw [Real.log_pow]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hlogp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (A : ℝ) * q ≤ Real.log (((p ^ k : ℕ) : ℝ))
    rw [hlogn]; nlinarith [hlog.1]
  · show Real.log (((p ^ k : ℕ) : ℝ)) ≤ (B : ℝ) * q
    rw [hlogn]; nlinarith [hlog.2]
  · show Λ (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ (C : ℝ) / S
    rw [hΛ]
    have hsq : s ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.le_sqrt_of_sq_le hs
    have hsqrt0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := lt_of_lt_of_le hs0 hsq
    have hhi0 : 0 ≤ hi := le_trans hlogp0.le hlog.2.le
    calc Real.log p / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ hi / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlog.2.le hsqrt0.le
      _ ≤ hi / s := div_le_div_of_nonneg_left hhi0 hs0 hsq
      _ ≤ (C : ℝ) / S := hC

/-- Lower bound `D / S ≤ 2 Λ(n) / √n` for a prime power `n = p^k` (used only for the comparison with
the pointwise comb mass). -/
lemma entryLow_of {S : ℝ} {n p k D : ℕ} {lo s : ℝ}
    (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (hlog : lo < Real.log p) (hlo : 0 ≤ lo) (hs0 : 0 < s) (hs : (n : ℝ) ≤ s ^ 2)
    (hD : (D : ℝ) / S ≤ 2 * lo / s) :
    (D : ℝ) / S ≤ 2 * Λ n / Real.sqrt n := by
  subst hn
  rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  have hsq : Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ s := by
    rw [Real.sqrt_le_left hs0.le]; exact hs
  have hsqrt0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr; exact_mod_cast pow_pos hp.pos k
  calc (D : ℝ) / S ≤ 2 * lo / s := hD
    _ ≤ 2 * lo / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hsqrt0 hsq
    _ ≤ 2 * Real.log p / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hsqrt0.le

/-- `Λ n = 0` when `n = a b` with coprime `a, b > 1` (so `n` is not a prime power). -/
lemma vonMangoldt_eq_zero_of_coprime {n : ℕ} (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hab : Nat.Coprime a b) (hn : n = a * b) : Λ n = 0 := by
  rw [vonMangoldt_eq_zero_iff]
  intro hpp
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, k, hp, -, hpk⟩ := hpp
  have hadvd : a ∣ p ^ k := by rw [hpk, hn]; exact Dvd.intro b rfl
  have hbdvd : b ∣ p ^ k := by rw [hpk, hn]; exact Dvd.intro_left a rfl
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hadvd
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hbdvd
  have hi0 : i ≠ 0 := by rintro rfl; simp at ha
  have hj0 : j ≠ 0 := by rintro rfl; simp at hb
  have hdvd : p ∣ Nat.gcd (p ^ i) (p ^ j) := Nat.dvd_gcd (dvd_pow_self p hi0) (dvd_pow_self p hj0)
  have hg : Nat.gcd (p ^ i) (p ^ j) = 1 := hab
  rw [hg] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
'''

def instance_tail(tag, meta, cert, lo, hi):
    N, H, S, Lam, Wmax, depth = meta['N'], meta['H'], meta['S'], meta['Lam'], meta['Wmax'], meta['depth']
    h, q, Lp = meta['h'], meta['q'], meta['Lp']
    lam = Fr(Lam, S)
    parts = []
    # non prime powers
    npp = nonpp(99)
    vms = []
    for (n, a, b) in npp:
        if n == 0:
            vms.append("lemma vm_0 : Λ 0 = 0 := ArithmeticFunction.map_zero")
        elif n == 1:
            vms.append("lemma vm_1 : Λ 1 = 0 := vonMangoldt_apply_one")
        else:
            vms.append(f"lemma vm_{n} : Λ {n} = 0 :=\n  vonMangoldt_eq_zero_of_coprime {a} {b} (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    parts.append("\n".join(vms))
    lst = ", ".join(str(n) for (n, _, _) in npp)
    conj = ", ".join(f"vm_{n}" for (n, _, _) in npp)
    parts.append(f"""/-- The integers `n < 100` that are not prime powers (`Λ n = 0`). -/
def nonPP100 : List ℕ := [{lst}]

lemma nonPP100_vm : ∀ n ∈ nonPP100, Λ n = 0 :=
  List.forall_iff_forall_mem.mp (show List.Forall (fun n => Λ n = 0) nonPP100 from ⟨{conj}⟩)

lemma {tag}_cover : ∀ n < 100, n ∉ {tag}Shifts.map Prod.fst → n ∈ nonPP100 := by
  decide

lemma {tag}_zero : ∀ n < 100, n ∉ {tag}Shifts.map Prod.fst → Λ n = 0 :=
  fun n hn hnot => nonPP100_vm n ({tag}_cover n hn hnot)

lemma log100_gt : 2 * {frac_lean(Lp)} < Real.log ((100 : ℕ) : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log ((100 : ℕ) : ℝ) = 2 * Real.log 2 + 2 * Real.log 5 := by
    rw [show ((100 : ℕ) : ℝ) = ((2 : ℝ) ^ 2) * ((5 : ℝ) ^ 2) by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hm]; linarith""")
    lam_s = f"(({Lam} : ℝ) / {S})"
    Lp_s = frac_lean(Lp)
    parts.append(f"""/-- **Certified form-level comb constant at `L' = {float(Lp)}`** (THEOREM, kernel-checked): for every
continuous compactly supported `g` vanishing off `[-L', L']`,
`‖Σ_n Λ(n)/√n (g⋆g~(log n) + g⋆g~(-log n))‖ ≤ {float(lam):.9f} ‖g‖²`.
(The pointwise comb constant of the same window is `Σ_{{n<100}} 2Λ(n)/√n ≈ 33.79`; see `combMass_gt_three_lam`.) -/
theorem primeSide_autocorr_le_cert {{g : ℝ → ℂ}} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-{Lp_s}) {Lp_s} → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ {lam_s} * ∫ x, ‖g x‖ ^ 2 := by
  have := primeSide_autocorr_le_of_check (L := {Lp_s}) (h := {frac_lean(h)}) (q := {frac_lean(q)})
    (S := {S}) (WTree.get {depth} {tag}Tree) {N} {H} {Lam} {Wmax} 100 {tag}Shifts
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    {tag}_check {tag}_entries (by decide) (by decide) {tag}_zero log100_gt hgc hgs hgW
  exact_mod_cast this

/-- The certified constant on the E8 test class. -/
theorem primeSide_autocorr_le_cert_weil {{g : ℝ → ℂ}} (hg : IsWeilTest g)
    (hgW : ∀ x, x ∉ Set.Icc (-{Lp_s}) {Lp_s} → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ {lam_s} * ∫ x, ‖g x‖ ^ 2 :=
  primeSide_autocorr_le_cert hg.1.continuous hg.2 hgW

/-- **Twist invariance at the certified constant**: every frequency twist `g ↦ e^{{irx}} g` (the comb
symbol `P(t + r)`) obeys the same bound; this is where `Λ ≥ 0` is used. -/
theorem primeSide_autocorr_twist_le_cert {{g : ℝ → ℂ}} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-{Lp_s}) {Lp_s} → g x = 0) (r : ℝ) :
    ‖primeSide (autocorr (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x))‖
      ≤ {lam_s} * ∫ x, ‖g x‖ ^ 2 := by
  have hn : ∀ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ = ‖g x‖ := by
    intro x; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hc : Continuous (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x) := by fun_prop
  have hW : ∀ x, x ∉ Set.Icc (-{Lp_s}) {Lp_s} → Complex.exp (((r * x : ℝ) : ℂ) * I) * g x = 0 := by
    intro x hx; simp [hgW x hx]
  have h := primeSide_autocorr_le_cert hc hgs.mul_left hW
  have hint : (∫ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ ^ 2) = ∫ x, ‖g x‖ ^ 2 := by
    congr 1; funext x; rw [hn x]
  rw [hint] at h
  exact h

/-- **Form-level envelope on the Weil functional** (Theorem 1 with `ω ≡ 1`, kernel-checked):
`Re W(g ⋆ g~) ≥ Re Arch(g ⋆ g~) - {float(lam):.6f} ‖g‖²` for every smooth test supported in `[-L', L']`. -/
theorem weilForm_autocorr_ge_cert {{g : ℝ → ℂ}} (hg : IsWeilTest g)
    (hgW : ∀ x, x ∉ Set.Icc (-{Lp_s}) {Lp_s} → g x = 0) :
    (archSide (autocorr g)).re - {lam_s} * ∫ x, ‖g x‖ ^ 2 ≤ (weilForm (autocorr g)).re := by
  have h := primeSide_autocorr_le_cert_weil hg hgW
  have hre : (primeSide (autocorr g)).re ≤ ‖primeSide (autocorr g)‖ := Complex.re_le_norm _
  unfold weilForm
  rw [Complex.sub_re]
  linarith""")
    # comparison with pointwise comb mass
    lo_, hi_, _ = log_compute()
    lows = []
    Dsum = 0
    for d in cert['ds']:
        n, p, k = d['n'], d['p'], d['k']
        r = math.isqrt(n)
        if r * r == n:
            s_up = Fr(r)
        else:
            s_up = Fr(math.isqrt(n * 10 ** 18) + 1, 10 ** 9)
        assert s_up * s_up >= n
        D = math.floor(Fr(S) * 2 * lo_[p] / s_up)
        Dsum += D
        lows.append((n, p, k, D, s_up))
    items = ", ".join(f"({n}, {D})" for (n, p, k, D, s) in lows)
    lowlem = []
    for (n, p, k, D, s) in lows:
        lowlem.append(f"""lemma low_{n} : (({D} : ℕ) : ℝ) / {S} ≤ 2 * Λ {n} / Real.sqrt (({n} : ℕ) : ℝ) := by
  have := entryLow_of (S := {S}) (n := {n}) (p := {p}) (k := {k}) (D := {D}) (lo := {frac_lean(lo_[p])}) (s := {frac_lean(s)})
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log{p}_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this""")
    assert 3 * Lam < Dsum, (3 * Lam, Dsum)
    parts.append("\n\n".join(lowlem))
    conj = ", ".join(f"low_{n}" for (n, p, k, D, s) in lows)
    parts.append(f"""/-- Lower-bound data `(n, D)`: `D / S ≤ 2 Λ(n)/√n` for the prime powers `n < 100`. -/
def lowData : List (ℕ × ℕ) := [{items}]

lemma lowData_ok : ∀ e ∈ lowData, ((e.2 : ℕ) : ℝ) / {S} ≤ 2 * Λ e.1 / Real.sqrt e.1 :=
  List.forall_iff_forall_mem.mp (show List.Forall (fun e : ℕ × ℕ => ((e.2 : ℕ) : ℝ) / {S} ≤
    2 * Λ e.1 / Real.sqrt e.1) lowData from ⟨{conj}⟩)

lemma listSum_low : ∀ ds : List (ℕ × ℕ), (∀ e ∈ ds, ((e.2 : ℕ) : ℝ) / {S} ≤ 2 * Λ e.1 / Real.sqrt e.1) →
    ((ds.map Prod.snd).sum : ℝ) / {S} ≤ (ds.map (fun e => 2 * Λ e.1 / Real.sqrt e.1)).sum
  | [], _ => by simp
  | e :: ds, h => by
    have h1 := h e List.mem_cons_self
    have h2 := listSum_low ds (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
    linarith

/-- **The certified form-level constant is below one third of the pointwise comb mass of the same
window** (kernel-checked): `3 · {float(lam):.6f} < Σ_{{n<100}} 2Λ(n)/√n` (the latter is `A_{{L'}} = sup_t P_{{L'}}(t)`,
the constant of every pointwise-envelope certificate, Zhu's Lemma 3.2). -/
theorem combMass_gt_three_lam : 3 * {lam_s} < ∑ n ∈ range 100, 2 * Λ n / Real.sqrt n := by
  have hsubset : (lowData.map Prod.fst).toFinset ⊆ range 100 := by
    intro n hn; rw [List.mem_toFinset] at hn; exact Finset.mem_range.mpr (by revert n hn; decide)
  have hmap : lowData.map Prod.fst = {tag}Shifts.map Prod.fst := by decide
  have h1 : ∑ n ∈ range 100, 2 * Λ n / Real.sqrt n
      = ∑ n ∈ (lowData.map Prod.fst).toFinset, 2 * Λ n / Real.sqrt n := by
    refine (Finset.sum_subset hsubset fun n hn hnot => ?_).symm
    rw [List.mem_toFinset, hmap] at hnot
    simp [{tag}_zero n (Finset.mem_range.mp hn) hnot]
  have hnd : (lowData.map Prod.fst).Nodup := by decide
  rw [h1, List.sum_toFinset _ hnd, List.map_map]
  have := listSum_low lowData lowData_ok
  have hsum : ((lowData.map Prod.snd).sum : ℝ) = ({Dsum} : ℝ) := by
    have : (lowData.map Prod.snd).sum = {Dsum} := by decide
    exact_mod_cast this
  rw [hsum] at this
  have hlt : 3 * {lam_s} < ({Dsum} : ℝ) / {S} := by norm_num
  exact lt_of_lt_of_le hlt (le_of_le_of_eq this rfl)

end Instance""")
    return "\n\n".join(parts), Dsum

GLUE = r'''
/-! ## F. The gluing of Theorem 2 on the E8 explicit formula (skeleton; analytic inputs named)

`Gφ := g⋆g~ - gH⋆gH~`.  In the paper `gH = μ * g` with `μ̂ = ω = 1 - K`; the pointwise split
`|F|² = (1 - |ω|²)|F|² + |ωF|²` is the split of the test `g⋆g~ = Gφ + gH⋆gH~`, so there are no cross
terms.  The zero side is used for `Gφ` (verified zeros contribute `≥ 0` because `|ω| ≤ 1`), the prime
side (form-level constant) for `gH⋆gH~`.  The three analytic inputs of the paper proof enter as
hypotheses: `hcontr` (`|ω| ≤ 1` on the line), `htail` (explicit tail over unverified zeros; paper:
`|φ| ≤ 3|K|`, `|F F*| ≤ 2 L e^L`, Trudgian's `S(t)`), `harch` (archimedean envelope; paper: digamma
lower bound, pole terms, leakage below `R = 2π e^{A⁺}`). -/

section Gluing

open ArithmeticFunction

lemma integrable_weilKernel_integrand {G : ℝ → ℂ} (hG : IsWeilTest G) (s : ℂ) :
    Integrable (fun u : ℝ => G u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := by
  have hc : Continuous (fun u : ℝ => G u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := by
    have := hG.1.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport hG.2.mul_right

lemma weilKernel_sub {G₁ G₂ : ℝ → ℂ} (h₁ : IsWeilTest G₁) (h₂ : IsWeilTest G₂) (s : ℂ) :
    weilKernel (fun u => G₁ u - G₂ u) s = weilKernel G₁ s - weilKernel G₂ s := by
  unfold weilKernel
  rw [← integral_sub (integrable_weilKernel_integrand h₁ s) (integrable_weilKernel_integrand h₂ s)]
  congr 1; funext u; ring

lemma isWeilTest_sub {G₁ G₂ : ℝ → ℂ} (h₁ : IsWeilTest G₁) (h₂ : IsWeilTest G₂) :
    IsWeilTest (fun u => G₁ u - G₂ u) :=
  ⟨h₁.1.sub h₂.1, h₁.2.sub h₂.2⟩

/-- **Theorem 2, gluing skeleton** (THEOREM, kernel-checked, conditional on the named inputs):
verified zeros up to `T` plus the form-level comb bound give almost-positivity. -/
theorem weil_almost_pos_of_glue {g gH : ℝ → ℂ} (hg : IsWeilTest g) (hgH : IsWeilTest gH)
    (T lam E₁ E₂ : ℝ)
    (hPB : ‖primeSide (autocorr gH)‖ ≤ lam * ∫ x, ‖gH x‖ ^ 2)
    (hcontr : ∀ t : ℝ, ‖Zeta23.paperFT gH t‖ ≤ ‖Zeta23.paperFT g t‖)
    (hzeros : ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (htail : Summable (fun ρ : ℂ => if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0))
    (htailE : (∑' ρ : ℂ, if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0) ≤ E₁)
    (harch : lam * (∫ x, ‖gH x‖ ^ 2) - E₂ ≤ (archSide (autocorr gH)).re) :
    -(E₁ + E₂) ≤ (weilForm (autocorr g)).re := by
  have hA := RvMBridge5.isWeilTest_autocorr hg
  have hAH := RvMBridge5.isWeilTest_autocorr hgH
  have hφ := isWeilTest_sub hA hAH
  set Gφ : ℝ → ℂ := fun u => autocorr g u - autocorr gH u with hGφ
  -- explicit formula for the three tests
  have EF := (RvMBridge4.limit_explicit_formula _ hA).2
  have EFH := (RvMBridge4.limit_explicit_formula _ hAH).2
  have EFφ := (RvMBridge4.limit_explicit_formula _ hφ).2
  -- additivity of the zero side: W(g⋆g~) = W(Gφ) + W(gH⋆gH~)
  have hsplit : weilForm (autocorr g) = (archSide Gφ - primeSide Gφ) + weilForm (autocorr gH) := by
    have hadd := EFφ.add EFH
    have hfun : (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel Gφ ρ
        + (zeroMult ρ : ℂ) * weilKernel (autocorr gH) ρ)
        = fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ := by
      funext ρ
      rw [hGφ, weilKernel_sub hA hAH]
      ring
    rw [hfun] at hadd
    unfold weilForm
    exact EF.unique hadd
  -- zero side of Gφ: verified zeros contribute ≥ 0, unverified ones are in the tail
  have hzero_side : -E₁ ≤ (archSide Gφ - primeSide Gφ).re := by
    have hre := Complex.hasSum_re EFφ
    have hneg := htail.hasSum.neg
    refine le_trans (neg_le_neg htailE) (hasSum_le (fun ρ => ?_) hneg hre)
    by_cases hT : T < |ρ.im|
    · simp only [hT, if_true]
      have := Complex.re_le_norm (-( (zeroMult ρ : ℂ) * weilKernel Gφ ρ))
      rw [norm_neg, Complex.neg_re] at this
      linarith
    · simp only [hT, if_false, neg_zero]
      by_cases hz : Zeta23.IsNontrivialZero ρ
      · have hre12 := hzeros ρ hz (le_of_not_gt hT)
        have hρ : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
          apply Complex.ext <;> simp [hre12]
        have hk : weilKernel Gφ ρ = weilKernel Gφ (1 / 2 + (ρ.im : ℂ) * I) := by rw [← hρ]
        rw [hk, hGφ, weilKernel_sub hA hAH, RvMBridge5.weilKernel_autocorr_line hg,
          RvMBridge5.weilKernel_autocorr_line hgH]
        have hmono : ‖Zeta23.paperFT gH ρ.im‖ ^ 2 ≤ ‖Zeta23.paperFT g ρ.im‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hcontr ρ.im) 2
        have hcast : (zeroMult ρ : ℂ) * ((‖Zeta23.paperFT g ρ.im‖ : ℂ) ^ 2 - (‖Zeta23.paperFT gH ρ.im‖ : ℂ) ^ 2)
            = (((zeroMult ρ : ℝ) * (‖Zeta23.paperFT g ρ.im‖ ^ 2 - ‖Zeta23.paperFT gH ρ.im‖ ^ 2) : ℝ) : ℂ) := by
          push_cast; ring
        rw [hcast, Complex.ofReal_re]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz]
        simp
  -- arithmetic side of gH⋆gH~: form-level comb bound
  have harith : -E₂ ≤ (weilForm (autocorr gH)).re := by
    have hre : (primeSide (autocorr gH)).re ≤ ‖primeSide (autocorr gH)‖ := Complex.re_le_norm _
    unfold weilForm
    rw [Complex.sub_re]
    linarith
  rw [hsplit, Complex.add_re]
  linarith

/-- Theorem 2 skeleton with the kernel-certified constant: `gH` supported in `[-L', L']`. -/
theorem weil_almost_pos_cert {g gH : ℝ → ℂ} (hg : IsWeilTest g) (hgH : IsWeilTest gH)
    (hgHW : ∀ x, x ∉ Set.Icc (-LPRIME) LPRIME → gH x = 0) (T E₁ E₂ : ℝ)
    (hcontr : ∀ t : ℝ, ‖Zeta23.paperFT gH t‖ ≤ ‖Zeta23.paperFT g t‖)
    (hzeros : ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (htail : Summable (fun ρ : ℂ => if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0))
    (htailE : (∑' ρ : ℂ, if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0) ≤ E₁)
    (harch : LAMCERT * (∫ x, ‖gH x‖ ^ 2) - E₂ ≤ (archSide (autocorr gH)).re) :
    -(E₁ + E₂) ≤ (weilForm (autocorr g)).re :=
  weil_almost_pos_of_glue hg hgH T _ E₁ E₂ (primeSide_autocorr_le_cert_weil hgH hgHW) hcontr hzeros
    htail htailE harch

end Gluing
'''

def build(cert_path, out_path, header_path, tag='cw'):
    cert = json.load(open(cert_path))
    inst, meta = emit_instance(cert, tag)
    lo, hi, _ = log_compute()
    tail, Dsum = instance_tail(tag, meta, cert, lo, hi)
    generic = open('generic_part.lean').read()
    header = open(header_path).read()
    lam_s = f"(({meta['Lam']} : ℝ) / {meta['S']})"
    glue = GLUE.replace('LPRIME', frac_lean(meta['Lp'])).replace('LAMCERT', lam_s)
    axioms = [
        'amgm_weighted', 'schur_twist_bound', 'amgm_window', 'schur_comb', 'primeSide_autocorr_le', 'autocorr_modulate',
        'primeSide_autocorr_modulate', 'primeSide_autocorr_twist_le', 'weilForm_autocorr_ge',
        'checkRows_sound', 'mMinus_sound', 'mPlus_sound', 'schur_of_check', 'primeSide_autocorr_le_of_check',
        f'{tag}_check', 'primeSide_autocorr_le_cert', 'primeSide_autocorr_le_cert_weil',
        'primeSide_autocorr_twist_le_cert', 'weilForm_autocorr_ge_cert', 'combMass_gt_three_lam',
        'weil_almost_pos_of_glue', 'weil_almost_pos_cert']
    pa = "\n".join(f"#print axioms Crux2VerifiedWindow.{a}" for a in axioms)
    body = header + generic.replace('import Mathlib\nimport E6Bridge5\n', '', 1) + "\n" + INSTANCE_HEAD + "\n" + inst + "\n\n" + tail + "\n" + glue + "\nend Crux2VerifiedWindow\n\n" + pa + "\n"
    open(out_path, 'w').write(body)
    print("wrote", out_path, len(body), "bytes; Dsum", Dsum, "3*Lam", 3 * meta['Lam'])

if __name__ == "__main__":
    build(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else 'cw')
