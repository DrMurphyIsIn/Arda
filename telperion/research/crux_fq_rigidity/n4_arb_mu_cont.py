# N4: Arb (python-flint ball arithmetic) certificate that the tempered real partner of P_cont is negative on [1, 5.8].
# mu_cont(r) = 1/(pi (1/4 + r^2)) + (Re psi(1/4 + i r/2) - log pi)/(2 pi).  Rigorous enclosures, outside the kernel.
from flint import arb, acb, ctx
ctx.prec = 120
pi = arb.pi()
def mu_ball(lo, hi):
    r = arb((arb(lo) + arb(hi))/2, (arb(hi) - arb(lo))/2)   # ball covering [lo, hi]
    z = acb(arb(1)/4, r/2)
    return 1/(pi*(arb(1)/4 + r*r)) + (z.digamma().real - pi.log())/(2*pi)
worst = None; ok = True; bad = []
N = 9600
for k in range(N):
    lo = 1 + 4.8*k/N; hi = 1 + 4.8*(k+1)/N
    m = mu_ball(lo, hi)
    upper = m.mid() + m.rad()
    if not (upper < 0): ok = False; bad.append((lo,hi))
    worst = upper if worst is None or upper > worst else worst
print("certified mu_cont < 0 on [1, 5.8]:", ok, " uncertified cells:", len(bad), (bad[0], bad[-1]) if bad else "", " max upper bound:", worst)
print("point value mu_cont(3) =", mu_ball(3, 3))
