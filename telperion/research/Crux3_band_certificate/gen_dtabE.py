"""Generate the D checker data of Crux3_BandDH.lean: the sqrt brackets behind the kappa ball, the
prime-log table lpTab, and the per-n table dtabE (log n, 1/sqrt n enclosures, 2pi-reduction multiples).
Single process; exact fractions.  Writes dtabE.lean (pasted into Crux3_BandDH.lean)."""
from fractions import Fraction as Fr
from dmirror import kap_ball, LP, primes, run

def q(x):
    x = Fr(x)
    return '((%d : ℚ) / %d)' % (x.numerator, x.denominator) if x.denominator != 1 else '(%d : ℚ)' % x.numerator

(a5, b5, c, dd), KB = kap_ball()
_, rows = run()
L = []
L.append('/-- `sqrt 5` and `sqrt(10 - 2 sqrt 5)` between rationals (squares checked by the kernel). -/')
L.append('def s5lo : ℚ := %s' % q(a5))
L.append('def s5hi : ℚ := %s' % q(b5))
L.append('def s10lo : ℚ := %s' % q(c))
L.append('def s10hi : ℚ := %s' % q(dd))
L.append('')
L.append('/-- The prime-log table `log p in [lo, hi]`, `p <= 53`. -/')
L.append('def lpTab : ℕ → ℚ × ℚ')
for p in primes:
    lo, hi = LP[p]
    L.append('  | %d => (%s, %s)' % (p, q(lo), q(hi)))
L.append('  | _ => (0, 0)')
L.append('')
L.append('/-- The D table entry of `n` (`log n`, `1/sqrt n`, reduction multiples). -/')
L.append('def dtabE : ℕ → DEntry')
for (n, lo, hi, q0, q1, m1, m2) in rows:
    L.append('  | %d => ⟨%s, %s, %s, %s, %d, %d⟩' % (n, q(lo), q(hi), q(q0), q(q1), m1, m2))
L.append('  | _ => ⟨0, 0, 0, 0, 0, 0⟩')
open('dtabE.lean', 'w').write('\n'.join(L) + '\n')
print('rows', len(rows))
