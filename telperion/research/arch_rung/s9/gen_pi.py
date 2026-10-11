"""Witness sequences for Mathlib's `pi_lower_bound` / `pi_upper_bound` tactics (ArchS9_Pi.lean).
Directed rounding; every inequality the tactic asks norm_num to check is re-verified here exactly.
Usage: python gen_pi.py DIGITS ITERS  -> prints Lean source.   conjecture1_proved = False."""
import sys
from fractions import Fraction as F
import mpmath as mp
DIG = int(sys.argv[1]); N = int(sys.argv[2]); SIG = DIG + 12
mp.mp.dps = 3 * DIG + 60
q = int(mp.floor(mp.pi * 10 ** DIG))
alo, ahi = F(q, 10 ** DIG), F(q + 1, 10 ** DIG)

def rnd(x, up):
    # x = 2 - u, round u to SIG significant digits; up=True rounds r up (u down)
    u = 2 - x
    e = int(mp.floor(mp.log10(u))) - SIG
    s = mp.mpf(10) ** e
    k = int(mp.floor(u / s)) if up else int(mp.ceil(u / s))
    return 2 - (F(k) * F(10) ** e if e >= 0 else F(k, 10 ** (-e)))

def seq(up):
    rs, prev = [], F(0)
    for i in range(N):
        x = mp.sqrt(2 + mp.mpf(prev.numerator) / prev.denominator)
        r = rnd(x, up)
        # exact check of the step condition: up: r^2 >= 2 + prev ; down: r^2 <= 2 + prev (and r >= 0)
        assert (r * r >= 2 + prev) if up else (r * r <= 2 + prev and r >= 0)
        rs.append(r); prev = r
    return rs

lo = seq(True)
assert lo[-1] <= 2 - (alo / 2 ** (N + 1)) ** 2, "lower: insufficient"
hi = seq(False)
assert F(1, 4 ** N) <= ahi and 2 - ((ahi - F(1, 4 ** N)) / 2 ** (N + 1)) ** 2 <= hi[-1], "upper: insufficient"
fmt = lambda L: ",\n    ".join(f"{r.numerator}/{r.denominator}" for r in L)
print(f"""theorem pi_gt_d{DIG} : ({q} : ℝ) / 10 ^ {DIG} < π := by
  pi_lower_bound [
    {fmt(lo)}]

theorem pi_lt_d{DIG} : π < ({q + 1} : ℝ) / 10 ^ {DIG} := by
  pi_upper_bound [
    {fmt(hi)}]""")
