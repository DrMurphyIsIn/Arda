from fractions import Fraction as Fr
from cf_core import lattice_aE, aK, aG, chi_m20, chi_m4, chi_5, divisors
import sympy
NMAX=27
fac = lambda n: sympy.factorint(n)
def rho_from(a):
    c={1:{}}
    for n in range(2,NMAX+1):
        acc={}
        for p,e in fac(n).items(): acc[p]=acc.get(p,0)+a(n)*e
        for d in divisors(n):
            if d<n:
                for p,v in c[d].items(): acc[p]=acc.get(p,0)-v*a(n//d)
        c[n]={p:v for p,v in acc.items() if v!=0}
    rho={}
    for n in range(1,NMAX+1):
        if not c[n]: rho[n]=Fr(0); continue
        f=fac(n)
        # check proportional to log n
        r=None
        for p,e in f.items():
            rr=Fr(c[n].get(p,0),e)
            assert r is None or rr==r, (n,c[n])
            r=rr
        assert set(c[n])<=set(f)
        rho[n]=r
    return rho
rhoE=rho_from(lattice_aE)
rhoK=rho_from(aK)
# check rhoK = (1+chi) mu
for n in range(2,NMAX+1):
    f=fac(n)
    mu = Fr(1,list(f.values())[0]) if len(f)==1 else Fr(0)
    assert rhoK[n]==(1+chi_m20(n))*mu, n
print("rhoE", {n:str(v) for n,v in rhoE.items() if v})
print("rhoK", {n:str(v) for n,v in rhoK.items() if v})
def q(x):
    x=Fr(x); return f"({x.numerator} : ℚ)" if x.denominator==1 else f"(({x.numerator} : ℚ) / {x.denominator})"
L=[]
L.append("""import Crux3_BandTable

/-!
# CF_EData: the Epstein counterfeit E and zeta_K for K = Q(sqrt -5) -- coefficients and log-derivative weights

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Bookkeeping for the counterfeit ladder; nothing here bears on RH.

## The two functions (normalized so that `a(1) = 1`)
* `E(s) = (1/2) sum_{(x,y) != (0,0)} (x^2 + 5 y^2)^{-s} = sum_n aE(n) n^{-s}`,
  `aE(n) = (1/2) #{(x, y) in Z^2 : x^2 + 5 y^2 = n}` (`aE`, defined by the lattice count itself).
  Classically `E = (zeta_K + L(s, chi_-4) L(s, chi_5))/2` (`aE_eq_half_sum` checks the coefficients on
  `[1, 27]`); `E` has NO Euler product.
* `zeta_K(s) = zeta(s) L(s, chi_-20) = sum_n aK(n) n^{-s}`, `aK = 1 * chi_-20` (`aKint`), with
  `-zeta_K'/zeta_K = sum_n Lambda(n) (1 + chi_-20(n)) n^{-s}` (`cK`).

## The weights
`-F'/F = sum_n c(n) n^{-s}` is equivalent to the Dirichlet-convolution identity
`a(n) log n = sum_{d | n} c(d) a(n/d)` (with `a(1) = 1`, so `c(1) = 0` and the identity is triangular).
* `cE n = rhoE n * log n` on `[1, 27]` (generated from the recursion; every `c_E(n)`, `n <= 27`, happens to
  be a rational multiple of `log n`), and `cE_conv` proves the identity for `n <= 27`; `eq_cE_of_conv`: any
  `w` satisfying it on `[1, 27]` equals `cE` there.
* `cK n = Lambda(n) (1 + chi_-20(n))`; `cK_conv` proves the identity with `aK` for `n <= 27`.
* Lemma-O witnesses: `cE 6 = 2 log 6 != 0` while `Lambda(6) = 0` (`cE_six`, `cE_six_ne_zero`).
No `sorry`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace CF

/-! ## A. The Epstein counterfeit's coefficients (lattice count) -/

/-- `#{(x, y) in Z^2 : x^2 + 5 y^2 = n}`, enumerated as `x = a - n`, `y = b - n` with `a, b in [0, 2n]`
(every representation has `|x|, |y| <= n`). -/
def aEcount (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun p : ℕ × ℕ => ((p.1 : ℤ) - n) ^ 2 + 5 * ((p.2 : ℤ) - n) ^ 2 = n)).card

/-- `aE(n) = (1/2) #{(x, y) : x^2 + 5 y^2 = n}`: the coefficients of `E = (1/2) sum' (x^2 + 5y^2)^{-s}`. -/
def aE (n : ℕ) : ℝ := (aEcount n : ℝ) / 2
""")
cnt = {n: 2*lattice_aE(n) for n in range(0,NMAX+1)}
cnt[0]=1
L.append("/-- The lattice counts for `n <= 27` (table). -/\ndef aEcnt : ℕ → ℕ")
for n in range(0,NMAX+1):
    if cnt[n]: L.append(f"  | {n} => {cnt[n]}")
L.append("  | _ => 0\n")
L.append("""set_option maxRecDepth 100000 in
theorem aEcount_tab : ∀ n ∈ List.range 28, aEcount n = aEcnt n := by decide +kernel

lemma aE_of_tab {n : ℕ} (hn : n < 28) : aE n = (aEcnt n : ℝ) / 2 := by
  unfold aE
  rw [aEcount_tab n (List.mem_range.mpr hn)]
""")
for n in range(1,NMAX+1):
    v=Fr(lattice_aE(n))
    L.append(f"lemma aE_{n} : aE {n} = {v.numerator} := by rw [aE_of_tab (by norm_num)]; norm_num [aEcnt]")
L.append("")
L.append("/-- `c_E(n)/log n` on `[1, 27]` (from the recursion `aE(n) log n = sum_{d|n} c(d) aE(n/d)`). -/\ndef rhoE : ℕ → ℚ")
for n,v in rhoE.items():
    if v: L.append(f"  | {n} => {q(v)}")
L.append("  | _ => 0\n")
L.append("/-- The coefficients `c_E(n)` of `-E'/E` for `n <= 27`. -/\ndef cE (n : ℕ) : ℝ := (rhoE n : ℝ) * Real.log n\n")
for n in range(1,NMAX+1):
    v=rhoE[n]
    L.append(f"lemma rhoE_{n} : rhoE {n} = {q(v)} := rfl")
L.append("")
# log factorization lemmas
comps=[n for n in range(4,NMAX+1) if not sympy.isprime(n)]
for n in comps:
    f=fac(n)
    prod=" * ".join(f"(({p} : ℝ) ^ {e})" for p,e in f.items())
    rhs=" + ".join(f"{e} * Real.log {p}" for p,e in f.items())
    L.append(f"lemma lg_{n} : Real.log ({n} : ℝ) = {rhs} := by")
    L.append(f"  rw [show ({n} : ℝ) = {prod} by norm_num]")
    ps=list(f.items())
    # log of product
    L.append("  repeat rw [Real.log_mul (by positivity) (by positivity)]")
    L.append("  simp only [Real.log_pow]")
    L.append("  push_cast")
    L.append("  ring")
L.append("")
lgnames=", ".join(f"lg_{n}" for n in comps)
aEnames=", ".join(f"aE_{n}" for n in range(1,NMAX+1))
rhoEnames=", ".join(f"rhoE_{n}" for n in range(1,NMAX+1))
def conv_lemma(name, a, cdef, rnames, anames, n):
    ds=divisors(n)
    s=[]
    s.append(f"lemma {name}_{n} : {a} {n} * Real.log ({n} : ℕ) = ∑ d ∈ Nat.divisors {n}, {cdef} d * {a} ({n} / d) := by")
    dset="{"+", ".join(map(str,ds))+"}"
    s.append(f"  rw [show Nat.divisors {n} = {dset} by decide]")
    ins=[]
    for i,d in enumerate(ds[:-1]):
        rest="{"+", ".join(map(str,ds[i+1:]))+"}"
        ins.append(f"Finset.sum_insert (show ({d} : ℕ) ∉ ({rest} : Finset ℕ) by decide)")
    ins.append("Finset.sum_singleton")
    s.append(f"  simp only [{', '.join(ins)}]")
    s.append(f"  norm_num [{cdef}, {rnames}, {anames}]")
    s.append(f"  try simp only [{lgnames}]")
    s.append("  try ring")
    return "\n".join(s)
for n in range(1,NMAX+1):
    L.append(conv_lemma("cE_conv","aE","cE",rhoEnames,aEnames,n))
    L.append("")
L.append("""/-- **The defining identity of `-E'/E`** (`-E' = E (-E'/E)` read coefficientwise), `n <= 27`. -/
theorem cE_conv : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, cE d * aE (n / d) := by
  intro n h1 h2
  interval_cases n""")
for n in range(1,NMAX+1):
    L.append(f"  · exact cE_conv_{n}")
L.append("""
lemma aE_one : aE 1 = 1 := by rw [aE_1]; try norm_num
lemma cE_one : cE 1 = 0 := by simp [cE]

/-- **Uniqueness**: any `w` with the defining identity on `[1, 27]` equals `cE` there. -/
theorem eq_cE_of_conv (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 27 → w n = cE n := by
  have hw1 : w 1 = 0 := by
    have h := hw 1 le_rfl (by norm_num)
    rw [Nat.divisors_one, Finset.sum_singleton, Nat.div_self (by norm_num), aE_one, Nat.cast_one, Real.log_one,
      mul_zero, mul_one] at h
    exact h.symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; rw [hw1, cE_one]
    · have hn0 : n ≠ 0 := by omega
      have e1 := hw n h1 h2
      have e2 := cE_conv n h1 h2
      rw [← Nat.insert_self_properDivisors hn0, Finset.sum_insert Nat.self_notMem_properDivisors] at e1 e2
      rw [Nat.div_self (by omega), aE_one, mul_one] at e1 e2
      have hsum : ∑ d ∈ n.properDivisors, w d * aE (n / d) = ∑ d ∈ n.properDivisors, cE d * aE (n / d) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd' := Nat.mem_properDivisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
        rw [ih d hd'.2 hd1 (by omega)]
      linarith

/-! ## B. zeta_K, K = Q(sqrt -5): chi_-20, its coefficients and its weights -/

/-- The Kronecker symbol `(-20/n)` (the character of `Q(sqrt -5)`): `1` on `{1, 3, 7, 9} mod 20`,
`-1` on `{11, 13, 17, 19} mod 20`, `0` otherwise. -/
def chi20 (n : ℕ) : ℤ :=
  if n % 20 = 1 ∨ n % 20 = 3 ∨ n % 20 = 7 ∨ n % 20 = 9 then 1
  else if n % 20 = 11 ∨ n % 20 = 13 ∨ n % 20 = 17 ∨ n % 20 = 19 then -1 else 0

/-- `chi_-4`. -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-- `chi_5 = (./5)`. -/
def chi5 (n : ℕ) : ℤ := if n % 5 = 1 ∨ n % 5 = 4 then 1 else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0

/-- The coefficients of `zeta_K = zeta * L(chi_-20)`: `aK = 1 * chi_-20` (ideals of norm `n`). -/
def aKint (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi20 d

/-- The coefficients of the genus product `L(chi_-4) L(chi_5)`. -/
def aGint (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi4 d * chi5 (n / d)

/-- `chi_-20 = chi_-4 chi_5` on `[0, 40)` (hence everywhere, both sides having period 20). -/
theorem chi20_eq_mul : ∀ n ∈ List.range 40, chi20 n = chi4 n * chi5 n := by decide

/-- **`E = (zeta_K + L(chi_-4) L(chi_5))/2`** at the level of coefficients, `n <= 27`:
`2 aE(n) = aK(n) + aG(n)` (i.e. the lattice count equals `aK + aG`). -/
theorem aE_eq_half_sum : ∀ n ∈ List.range 28, 1 ≤ n → (aEcount n : ℤ) = aKint n + aGint n := by
  decide +kernel

def aK (n : ℕ) : ℝ := (aKint n : ℝ)

/-- The weights of `-zeta_K'/zeta_K`: `Lambda(n) (1 + chi_-20(n))`, supported on prime powers. -/
def cK (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (1 + (chi20 n : ℝ))
""")
L.append("/-- `c_K(n)/log n` on `[1, 27]`. -/\ndef rhoK : ℕ → ℚ")
for n,v in rhoK.items():
    if v: L.append(f"  | {n} => {q(v)}")
L.append("  | _ => 0\n")
for n in range(1,NMAX+1):
    L.append(f"lemma rhoK_{n} : rhoK {n} = {q(rhoK[n])} := rfl")
aKv={n:aK(n) for n in range(1,NMAX+1)}
L.append("""
lemma aK_of_tab : ∀ n ∈ List.range 28, aKint n = aKtab n := by decide
""".replace("aKtab n","aKtab n"))
# aKtab def must come before; insert
akdef=["/-- `aK` table. -/","def aKtab : ℕ → ℤ"]
for n in range(0,NMAX+1):
    v = aK(n) if n>0 else 0
    if v: akdef.append(f"  | {n} => {v}")
akdef.append("  | _ => 0\n")
L.insert(len(L)-1,"\n".join(akdef))
for n in range(1,NMAX+1):
    L.append(f"lemma aK_{n} : aK {n} = {aKv[n]} := by unfold aK; rw [aK_of_tab {n} (by decide)]; norm_num [aKtab]")
L.append("")
L.append("""/-- `cK n = rhoK n * log n` on `[1, 27]` (from `Lambda(n) = mu_n log n`, Crux3's `lam_tab`). -/
theorem cK_eq : ∀ n : ℕ, n ≤ 27 → cK n = (rhoK n : ℝ) * Real.log n := by
  intro n hn
  unfold cK
  rw [Crux3.lam_tab n (by omega)]
  interval_cases n <;> norm_num [Crux3.tab, chi20, rhoK] <;> ring
""")
rhoKnames=", ".join(f"rhoK_{n}" for n in range(1,NMAX+1))
aKnames=", ".join(f"aK_{n}" for n in range(1,NMAX+1))
L.append("/-- `cK` in `rho log` form (for the per-`n` identities). -/\ndef cK' (n : ℕ) : ℝ := (rhoK n : ℝ) * Real.log n\n")
for n in range(1,NMAX+1):
    L.append(conv_lemma("cK_conv'","aK","cK'",rhoKnames,aKnames,n))
    L.append("")
L.append("""/-- **The defining identity of `-zeta_K'/zeta_K`** with the weights `Lambda(n)(1 + chi_-20(n))`,
`n <= 27`: `aK(n) log n = sum_{d | n} cK(d) aK(n/d)`. -/
theorem cK_conv : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aK n * Real.log n = ∑ d ∈ n.divisors, cK d * aK (n / d) := by
  intro n h1 h2
  have hc : ∀ d ∈ n.divisors, cK d * aK (n / d) = cK' d * aK (n / d) := by
    intro d hd
    have hdn : d ≤ n := Nat.divisor_le hd
    rw [cK_eq d (by omega)]
    rfl
  rw [Finset.sum_congr rfl hc]
  interval_cases n""")
for n in range(1,NMAX+1):
    L.append(f"  · exact cK_conv'_{n}")
L.append("""
/-! ## C. Lemma-O witnesses at `n = 6` -/

/-- `c_E(6) = 2 log 6`: the Epstein counterfeit has a periodic orbit of length `log 6`. -/
theorem cE_six : cE 6 = 2 * Real.log 6 := by norm_num [cE, rhoE]

theorem cE_six_ne_zero : cE 6 ≠ 0 := by
  rw [cE_six]
  have : 0 < Real.log 6 := Real.log_pos (by norm_num)
  positivity

/-- `Lambda(6) = 0` and `c_K(6) = 0`: zeta and zeta_K have no orbit of length `log 6`. -/
theorem vonMangoldt_six : ArithmeticFunction.vonMangoldt 6 = 0 := by
  rw [Crux3.lam_tab 6 (by norm_num)]
  norm_num [Crux3.tab]

theorem cK_six : cK 6 = 0 := by rw [cK, vonMangoldt_six, zero_mul]

/-- For ANY weights with E's defining identity on `[1, 27]`, `w 6 = 2 log 6 != 0 = Lambda(6)`. -/
theorem epstein_orbit_six (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 1 ≤ n → n ≤ 27 → aE n * Real.log n = ∑ d ∈ n.divisors, w d * aE (n / d)) :
    w 6 = 2 * Real.log 6 ∧ w 6 ≠ 0 ∧ ArithmeticFunction.vonMangoldt 6 = 0 := by
  have h := eq_cE_of_conv w hw 6 (by norm_num) (by norm_num)
  refine ⟨by rw [h, cE_six], by rw [h]; exact cE_six_ne_zero, vonMangoldt_six⟩

end CF
""")
open('/Users/peterwmurphy/arda-cf/telperion/examples/rvm_bridge/lean/CF_EData.lean','w').write("\n".join(L))
print("written")
