from fractions import Fraction as Fr
from mirror import run, prime_powers, log_encl
tot, table = run()
pp = {n: (p, e) for (n, p, e) in prime_powers(56)}
def q(x):
    x = Fr(x)
    if x.denominator == 1:
        return '(%d : ℚ)' % x.numerator
    return '((%d : ℚ) / %d)' % (x.numerator, x.denominator)
lines = []
lines.append('/-- The table: entry `n` (`n < 57`). -/')
lines.append('def tab : ℕ → TEntry')
tabd = {t[0]: t for t in table}
for n in range(57):
    if n in tabd:
        (_, p, e, lo, hi, q0, q1, m1, m2) = tabd[n]
        lines.append('  | %d => ⟨%s, %s, %s, %s, %s, %d, %d⟩' % (n, q(Fr(1, e)), q(lo), q(hi), q(q0), q(q1), m1, m2))
lines.append('  | _ => ⟨0, 0, 0, 0, 0, 0, 0⟩')
open('lean/tab.lean', 'w').write('\n'.join(lines) + '\n')
# the log 57 lower bound for 2A < log 57
lo57, hi57 = log_encl(57)
print('lo57 =', lo57, float(lo57))
print(len(table), 'entries')
