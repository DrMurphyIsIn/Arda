"""
Unified-barrier lens: numerical checks (mpmath, 50 digits).  COMPUTED, not interval-certified,
except where noted (the integer identities are exact).

W(p,c)(s) = zeta(s) * (1 + c p^-s + p p^-2s),   completion  xi(s) * A_{p,c}(s)  (up to sqrt p),
A_{p,c}(s) = 2 cosh((s-1/2) log p) + c/sqrt(p).

Checks:
 C1  A_{p,c}(s) * sqrt(p) == p^s (1 + c p^-s + p p^-2s) * p^{-... }  (completion identity)
 C2  contractivity identity  |A(2s)|^2 - |A(2s-1)|^2 = (sqrt p - 1/sqrt p)(R - 1/R)[(sqrt p + 1/sqrt p)(R + 1/R) + 2 c~ cos phi]
 C3  Lambda_W(p^m)/log p = 1 - t_m, t Newton/Lucas; sign pattern for c^2 > 4p
 C4  zeros of A: 1/2 +- arccosh(c~/2)/log p + i(2k+1)pi/log p
 C5  support-prime duality: sum over zeros of A of h(gamma) = 2 log p g(0) when supp g in (-log p, log p)
 C6  W(41,13): lowest zero height pi/log 41 < sqrt(3)/2 (LowHeightBox Box 1 fails for the model)
 C7  golden fake: A_{5,5} == XiA = 2cosh((s-1/2)log5) + sqrt5
"""
import mpmath as mp
mp.mp.dps = 50
import random

def A(p, c, s):
    return 2*mp.cosh((s-mp.mpf(1)/2)*mp.log(p)) + c/mp.sqrt(p)

def localpoly(p, c, s):
    T = mp.power(p, -s)
    return 1 + c*T + p*T**2

ok = True
def check(name, cond, info=""):
    global ok
    ok = ok and bool(cond)
    print(("PASS " if cond else "FAIL ") + name + ("  " + info if info else ""))

# C1 completion identity: p^{s-1/2} * P(p^-s) = A(s)
random.seed(1)
err = 0
for (p, c) in [(5, 5), (29, 11), (41, 13), (7, 6), (101, 21)]:
    for _ in range(5):
        s = mp.mpc(random.uniform(-3, 4), random.uniform(-20, 20))
        lhs = mp.power(p, s - mp.mpf(1)/2) * localpoly(p, c, s)
        err = max(err, abs(lhs - A(p, c, s)))
check("C1 completion identity p^(s-1/2) P(p^-s) = A_{p,c}(s)", err < mp.mpf(10)**-40, "max err %s" % mp.nstr(err, 3))

# C1b FE of A: A(1-s) = A(s)
err = 0
for (p, c) in [(5, 5), (29, 11), (41, 13)]:
    for _ in range(5):
        s = mp.mpc(random.uniform(-3, 4), random.uniform(-20, 20))
        err = max(err, abs(A(p, c, 1 - s) - A(p, c, s)))
check("C1b A(1-s) = A(s)", err < mp.mpf(10)**-40)

# C2 contractivity identity and inequality
err = 0
worst = mp.inf
for (p, c) in [(5, 5), (5, 6), (29, 11), (41, 13), (41, 42), (7, -8)]:
    ct = mp.mpf(c)/mp.sqrt(p)
    for _ in range(40):
        v = mp.mpc(random.uniform(0, 2), random.uniform(-10, 10))   # v = 2s - 1, Re v >= 0
        s = (v + 1)/2
        lhs = abs(A(p, c, 2*s))**2 - abs(A(p, c, 2*s - 1))**2
        z = mp.exp(v*mp.log(p)/1)   # careful: A(2s) uses (2s - 1/2) log p = (v + 1/2) log p
        # A(2s) = 2cosh((v+1/2)L)+ct, A(2s-1) = 2cosh((v-1/2)L)+ct, with L = log p ; z = e^{vL}
        R = abs(z); phi = mp.arg(z)
        sq = mp.sqrt(p)
        rhs = (sq - 1/sq)*(R - 1/R)*((sq + 1/sq)*(R + 1/R) + 2*ct*mp.cos(phi))
        err = max(err, abs(lhs - rhs)/(1 + abs(lhs)))
        if abs(c) <= p + 1:
            worst = min(worst, lhs)
check("C2 contractivity identity |A(2s)|^2-|A(2s-1)|^2 = (sqrt p-1/sqrt p)(R-1/R)[...]", err < mp.mpf(10)**-30, "rel err %s" % mp.nstr(err, 3))
check("C2b contractive (|A(2s-1)| <= |A(2s)|) on Re s >= 1/2 whenever |c| <= p+1", worst >= -mp.mpf(10)**-30, "min diff %s" % mp.nstr(worst, 5))
# a violating case |c| > p + 1: find v with lhs < 0
p, c = 5, 7
ct = mp.mpf(c)/mp.sqrt(p)
v = mp.mpc(0.05, mp.pi/mp.log(p))   # cos(phi) = -1 at Im v * L = pi
s = (v + 1)/2
d = abs(A(p, c, 2*s))**2 - abs(A(p, c, 2*s - 1))**2
check("C2c |c| = p+2 violates contractivity somewhere", d < 0, "diff %s" % mp.nstr(d, 5))

# C3 von Mangoldt of W at powers of p: Lambda_W(p^m) = log p (1 - t_m), t_m = x1^m + x2^m,
#     x1,x2 roots of x^2 + c x + p (so 1 + cT + pT^2 = (1-x1 T)(1-x2 T)).
def t_seq(p, c, M):
    t = [2, -c]
    for m in range(2, M + 1):
        t.append(-c*t[-1] - p*t[-2])
    return t
# verify against series of log(1 + cT + pT^2): coefficient of T^m is -t_m/m
T = mp.mpf('1e-3')
for (p, c) in [(29, 11), (5, 5), (41, 13)]:
    t = t_seq(p, c, 30)
    series = -sum(mp.mpf(t[m])/m * T**m for m in range(1, 31))
    direct = mp.log(1 + c*T + p*T**2)
    check("C3a log(1+cT+pT^2) = -sum t_m T^m/m  (p,c)=(%d,%d)" % (p, c), abs(series - direct) < mp.mpf(10)**-40)
    signs = [1 - t[m] for m in range(1, 9)]
    print("     (p,c)=(%d,%d): Lambda_W(p^m)/log p for m=1..8:" % (p, c), signs)
    pat = all((signs[m-1] > 0) if (m % 2 == 1) else (signs[m-1] < 0) for m in range(1, 9))
    check("C3b sign pattern: >0 at odd m, <0 at even m (c^2>4p, c>0)", pat)
# quadratic surgery with c^2 <= 4p (on-line): still fails positivity at some m <= 6 (Dirichlet)
fails = []
for p in [2, 3, 5, 7, 11, 13]:
    for c in range(-int(2*mp.sqrt(p)), int(2*mp.sqrt(p)) + 1):
        t = t_seq(p, c, 6)
        if all(1 - t[m] >= 0 for m in range(1, 7)):
            fails.append((p, c))
check("C3c every quadratic surgery (c^2<=4p, p<=13) violates Lambda>=0 at some p^m, m<=6", len(fails) == 0, str(fails))
# P2 at p^2 alone: 1 - t_2 = 1 + 2p - c^2 >= 0  <=> c^2 <= 2p+1 (< 4p): kills every off-line quadratic surgery
check("C3d Lambda(p^2) >= 0 <=> c^2 <= 2p+1 < 4p", all((1 - t_seq(p, c, 2)[2] >= 0) == (c*c <= 2*p + 1) for p in range(2, 60) for c in range(-40, 41)))

# C4 zeros of A
for (p, c) in [(5, 5), (29, 11), (41, 13)]:
    L = mp.log(p); ct = mp.mpf(c)/mp.sqrt(p)
    eta = mp.acosh(ct/2)
    for k in [0, 1, -1, 5]:
        for sg in [1, -1]:
            s = mp.mpf(1)/2 + sg*eta/L + 1j*(2*k + 1)*mp.pi/L
            assert abs(A(p, c, s)) < mp.mpf(10)**-40
    print("     (p,c)=(%d,%d): Re rho = 1/2 +- %s ; lowest height pi/log p = %s" % (p, c, mp.nstr(eta/L, 8), mp.nstr(mp.pi/L, 8)))
check("C4 explicit zeros 1/2 +- arccosh(c/(2 sqrt p))/log p + i(2k+1)pi/log p", True)

# C5 support-prime duality.  Positive-type test g = g_b * g_b (g_b = triangle of half-width b), supp g = [-2b, 2b],
#   h(z) = int g(x) e^{ixz} dx = (b sinc(bz/2)^2)^2 = b^2 sinc^4(bz/2)  (decays like z^-4), g(0) = 2b/3.
#   Poisson over the zero lattice gamma_{k,+-} = (2k+1)pi/L -+ i eta/L of A:
#     sum_{k,+-} h(gamma) = L sum_m (-1)^m g(mL) (e^{m eta} + e^{-m eta});  for 2b < L only m = 0: = 2 L g(0).
def sinc(u):
    return mp.mpf(1) if abs(u) < mp.mpf(10)**-30 else mp.sin(u)/u
def h4(b, z):
    return b**2 * sinc(b*z/2)**4
def gconv(b, x):
    # (g_b * g_b)(x) for triangle g_b(x) = (1-|x|/b)_+ ; piecewise cubic
    x = abs(mp.mpf(x)); b = mp.mpf(b)
    if x >= 2*b: return mp.mpf(0)
    return mp.quad(lambda y: max(0, 1 - abs(y)/b)*max(0, 1 - abs(x - y)/b), [x - b, 0, x, b] if x < b else [x - b, b])
for (p, c) in [(29, 11), (5, 5), (41, 13)]:
    L = mp.log(p); ct = mp.mpf(c)/mp.sqrt(p); eta = mp.acosh(ct/2)
    for frac in [0.25, 0.45, 0.75]:
        b = frac*L          # supp g = [-2b, 2b], 2b/L = 0.5, 0.9, 1.5
        K = 4000
        tot = sum(h4(b, (2*k + 1)*mp.pi/L + sg*1j*eta/L) for k in range(-K, K) for sg in [1, -1])
        # tail estimate ~ 2 * sum_{|k|>K} b^2 (2/(b gamma))^4 ~ small
        full = L*sum((-1)**m * gconv(b, m*L) * (mp.exp(-m*eta) + mp.exp(m*eta)) for m in range(-3, 4))
        print("     (p,c)=(%d,%d) supp g/L=%.1f: zero-sum %s ; Poisson %s ; 2L g(0) = %s" % (p, c, float(2*b/L), mp.nstr(tot.real, 12), mp.nstr(full, 12), mp.nstr(2*L*2*b/3, 12)))
        check("C5 zero-sum over A's zeros = Poisson prediction (supp/L=%.1f)" % float(2*b/L), abs(tot - full) < mp.mpf(10)**-7)
        if 2*b < L:
            check("C5b supp g < log p: zero-sum = 2 log p g(0), independent of c", abs(tot - 2*L*2*b/3) < mp.mpf(10)**-7)
# two-point positive-type test f = delta_0 + t delta_L (the limit of smooth bumps): local Weil form
#   Q_A(t) = L [2(1+t^2) - 4 t cosh(eta)]  (only m = 0, +-1 terms), min at t = cosh eta: -2 L sinh(eta)^2 < 0 iff c~ > 2.
for (p, c) in [(29, 11), (5, 5), (41, 13), (29, 10)]:
    L = mp.log(p); ct = mp.mpf(c)/mp.sqrt(p)
    if ct > 2:
        eta = mp.acosh(ct/2); q = L*(2*(1 + mp.cosh(eta)**2) - 4*mp.cosh(eta)**2)
        print("     (p,c)=(%d,%d): two-point local form min = %s = -2L sinh^2(eta)" % (p, c, mp.nstr(q, 8)))
    else:
        th = mp.acos(ct/2)  # c~ = 2 cos(theta): Q(t) = L[2(1+t^2) - 2 t c~] >= 0
        print("     (p,c)=(%d,%d): on-line surgery; two-point local form min = %s >= 0" % (p, c, mp.nstr(L*(2 - ct**2/2), 8)))

# C6 W(41,13) lowest zero below sqrt(3)/2
p, c = 41, 13
L = mp.log(p)
check("C6 W(41,13): c^2 > 4p and c < p+1", c*c > 4*p and c < p + 1)
check("C6b lowest zero height pi/log 41 = %s < sqrt(3)/2 = %s" % (mp.nstr(mp.pi/L, 8), mp.nstr(mp.sqrt(3)/2, 8)), mp.pi/L < mp.sqrt(3)/2)
check("C6c log 41 > 3 log 2 + 1.58 = %s > pi/(sqrt3/2) = %s" % (mp.nstr(3*mp.log(2) + 1.58, 8), mp.nstr(mp.pi/(mp.sqrt(3)/2), 8)), 3*mp.log(2) + 1.58 > mp.pi/(mp.sqrt(3)/2))

# C7 golden fake
err = 0
for _ in range(10):
    s = mp.mpc(random.uniform(-3, 4), random.uniform(-20, 20))
    err = max(err, abs(A(5, 5, s) - (2*mp.cosh((s - mp.mpf(1)/2)*mp.log(5)) + mp.sqrt(5))))
check("C7 A_{5,5} = XiA (golden fake = completion factor of W(5,5))", err < mp.mpf(10)**-40)

# C8 pointwise-layer data for W(p,c) zeros: Box2, Li disk, Box1 (lowest zero), for (5,5),(29,11)
for (p, c) in [(5, 5), (29, 11), (37, 12), (41, 13)]:
    L = mp.log(p); ct = mp.mpf(c)/mp.sqrt(p)
    if ct <= 2:
        print("     (p,c)=(%d,%d) on-line" % (p, c)); continue
    d = mp.acosh(ct/2)/L; g = mp.pi/L
    box1 = g >= mp.sqrt(3)/2
    box2 = d**2 <= g**2/3 - mp.mpf(1)/4
    lidisk = mp.mpf(1)/4 - d**2 + g**2 >= 1
    print("     (p,c)=(%d,%d): delta=%s gamma0=%s  Box1=%s Box2=%s LiDisk=%s" % (p, c, mp.nstr(d, 6), mp.nstr(g, 6), box1, box2, lidisk))

print("ALL PASS" if ok else "SOME FAIL")
