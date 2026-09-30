from mirror import prime_powers
from math import gcd
pp = {n: (p, e) for (n, p, e) in prime_powers(56)}
def split(n):
    # n = a * b, a = p^k full prime power part of the smallest prime, b > 1 coprime
    m, p = n, None
    for d in range(2, n + 1):
        if m % d == 0:
            p = d
            break
    a = 1
    while m % p == 0:
        m //= p
        a *= p
    return a, m
L = []
L.append('''/-- `Λ n = 0` when `n = a b` with coprime `a, b > 1` (`n` is not a prime power). -/
lemma vonMangoldt_eq_zero_of_coprime' {n : ℕ} (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hab : Nat.Coprime a b) (hn : n = a * b) : ArithmeticFunction.vonMangoldt n = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
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
''')
L.append('/-- `Λ n = mu_n log n` for every `n < 57` (the table\'s `mu`). -/')
L.append('theorem lam_tab : ∀ n < 57, ArithmeticFunction.vonMangoldt n = ((tab n).mu : ℝ) * Real.log n := by')
L.append('  intro n hn')
L.append('  interval_cases n')
for n in range(57):
    if n in pp:
        p, e = pp[n]
        mu = '1' if e == 1 else '1 / %d' % e
        L.append('  · have hm : (tab %d).mu = %s := rfl' % (n, mu))
        L.append('    rw [hm]')
        if e == 1:
            L.append('    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]')
            L.append('    push_cast')
            L.append('    ring')
        else:
            L.append('    rw [show (%d : ℕ) = %d ^ %d by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),' % (n, p, e))
            L.append('      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]')
            L.append('    push_cast')
            L.append('    rw [show (%d : ℝ) = (%d : ℝ) ^ %d by norm_num, Real.log_pow]' % (n, p, e))
            L.append('    push_cast')
            L.append('    ring')
    else:
        L.append('  · have hm : (tab %d).mu = 0 := rfl' % n)
        L.append('    rw [hm]')
        if n in (0, 1):
            L.append('    simp')
        else:
            a, b = split(n)
            assert a > 1 and b > 1 and gcd(a, b) == 1 and a * b == n
            L.append('    rw [vonMangoldt_eq_zero_of_coprime\' %d %d (by norm_num) (by norm_num) (by norm_num) (by norm_num)]' % (a, b))
            L.append('    simp')
open('lean/lam.lean', 'w').write('\n'.join(L) + '\n')
