# N5 (builder): numerical cross-checks of the constants and statements used in the kernel file
# telperion/examples/rvm_bridge/lean/Crux/CruxFQ_rigidity.lean.  COMPUTED (mpmath, not interval).
# Single process, no pools.  conjecture1_proved = False.
#
# (a) the smooth test family psi_d * psi_d of Lemma M: |psihat| <= 1, 1 - psihat(xi) <= 2 pi^2 d^2 xi^2,
#     sup psi_d <= 1/d (bump = 1 on [-d/2, d/2], supported in (-d, d)), k_d(r) = psihat(r/2pi)^2 -> 1.
# (b) the Fejer lower bound fej(x) >= 4 eps^2 / (pi^2 R^2) off the integers (quantitative Theorem A).
# (c) the quantitative Theorem A inequality on a perturbed comb.
# (d) the Lee-Yang example PLY = 1 + z1/2 + z2/2 + z1 z2 on (log 2, log 3): self-inversive factorisation
#     PLY(e^{i t1}, e^{i t2}) = e^{i(t1+t2)/2} (2 cos((t1+t2)/2) + cos((t1-t2)/2)), real zero count.
# (e) the local trichotomy of Bragg sequences s_m = sum over inverse roots^m of a local factor:
#     unimodular roots (Lee-Yang) -> bounded, non-decaying (Bohr mean of |s_m|^2 = sum mult^2);
#     root outside the disc (zeta: 1 - p^{-1/2} z) -> decays like p^{-m/2};
#     root inside the disc (golden fake: z^2 + sqrt5 z + 1) -> grows like phi^m, s_m = (-1)^m (phi^m + phi^-m).
import mpmath as mp
mp.mp.dps = 30
pi = mp.pi

print("(a) smooth test family")
def smooth_step(t):
    # C-infinity transition: 0 for t <= 0, 1 for t >= 1
    if t <= 0: return mp.mpf(0)
    if t >= 1: return mp.mpf(1)
    a = mp.e**(-1/t); b = mp.e**(-1/(1 - t))
    return a/(a + b)
def make_psi(d):
    d = mp.mpf(d)
    f = lambda u: smooth_step((d - abs(u))/(d/2))      # = 1 on |u| <= d/2, = 0 on |u| >= d
    Z = 2*mp.quad(f, [0, d/2, d])
    return (lambda u: f(u)/Z), Z
for d in ['0.5', '0.2', '0.05']:
    psi, Z = make_psi(d); dd = mp.mpf(d)
    sup = psi(0)
    worst_gap = mp.mpf(-10); worst_abs = mp.mpf(0)
    for xi in [mp.mpf(x) for x in ['0.1', '0.5', '1', '3', '10', '40']]:
        ph = 2*mp.quad(lambda u: psi(u)*mp.cos(2*pi*u*xi), [0, dd/2, dd])
        gap = (1 - ph) - 2*pi**2*dd**2*xi**2          # must be <= 0
        worst_gap = max(worst_gap, gap); worst_abs = max(worst_abs, abs(ph))
    k = [mp.nstr((2*mp.quad(lambda u: psi(u)*mp.cos(u*r), [0, dd/2, dd]))**2, 8) for r in [1, 10, 30]]
    print(f"  d={d}: int bump = {mp.nstr(Z,8)} (>= d), sup psi_d = {mp.nstr(sup,8)} <= 1/d = {mp.nstr(1/dd,8)};"
          f" max |psihat| = {mp.nstr(worst_abs,8)}; max[(1-psihat) - 2pi^2 d^2 xi^2] = {mp.nstr(worst_gap,6)};"
          f" k_d(r) at r=1,10,30: {k}")

print("\n(b) Fejer lower bound off the integers")
fej = lambda x: mp.mpf(1) if x == 0 else (mp.sin(pi*x)/(pi*x))**2
for R, eps in [(10, '0.1'), (10, '0.25'), (50, '0.5'), (3, '0.05')]:
    R = mp.mpf(R); eps = mp.mpf(eps); c = 4*eps**2/(pi**2*R**2)
    worst = mp.inf; n = 0
    for k in range(-int(R)*400, int(R)*400 + 1):
        x = mp.mpf(k)/400
        if abs(x) <= R and abs(x - mp.nint(x)) >= eps:
            worst = min(worst, fej(x) - c); n += 1
    print(f"  R={mp.nstr(R,3)} eps={mp.nstr(eps,3)}: min over {n} grid points of fej(x) - 4eps^2/(pi^2R^2) = {mp.nstr(worst,6)}  (>= 0 required)")

print("\n(c) quantitative Theorem A on a perturbed comb nu = delta_0 + sum_{1<=|n|<=N} delta_{n + eta sgn n}")
N = 400
for eta in ['0.01', '0.1', '0.3']:
    eta = mp.mpf(eta)
    atoms = [n + eta*mp.sign(n) for n in range(-N, N + 1) if n != 0]
    defect = mp.fsum(fej(x) for x in atoms)                     # = int fej dnu - int tri dnu (gap holds)
    for R, eps in [(20, eta), (100, eta/2)]:
        R = mp.mpf(R); mass = sum(1 for x in atoms if abs(x) <= R and abs(x - mp.nint(x)) >= eps)
        lhs = 4*eps**2/(pi**2*R**2)*mass
        print(f"  eta={mp.nstr(eta,3)} R={mp.nstr(R,4)} eps={mp.nstr(eps,3)}: (4eps^2/pi^2R^2)*mass = {mp.nstr(lhs,6)} <= defect = {mp.nstr(defect,6)} : {lhs <= defect}")

print("\n(d) the Lee-Yang example PLY on (log 2, log 3)")
l1, l2 = mp.log(2), mp.log(3)
PLY = lambda z1, z2: 1 + z1/2 + z2/2 + z1*z2
f = lambda x: PLY(mp.e**(1j*l1*x), mp.e**(1j*l2*x))
h = lambda x: 2*mp.cos(x*(l1 + l2)/2) + mp.cos(x*(l1 - l2)/2)
err = max(abs(f(x)*mp.e**(-1j*(l1 + l2)*x/2) - h(x)) for x in [mp.mpf(k)/7 for k in range(0, 700)])
xs = [mp.mpf(60)*k/12000 for k in range(12001)]
vals = [h(x) for x in xs]
sc = sum(1 for a, b in zip(vals[:-1], vals[1:]) if a*b < 0)
print(f"  max |PLY(2^ix,3^ix) e^(-ix log6/2) - (2cos(x log6/2) + cos(x log(2/3)/2))| on [0,100] = {mp.nstr(err,5)}")
print(f"  real zeros on [0,60] (sign changes of the real factor) = {sc}; heuristic 2*60/(4pi/log6) = {mp.nstr(2*60/(4*pi/mp.log(6)),6)}")
print(f"  PLY - PLY(.,0)PLY(0,.) at (1,1) = {mp.nstr(PLY(1,1) - PLY(1,0)*PLY(0,1),6)} (= 3/4, the mixed coefficient)")

print("\n(e) local Bragg sequences s_m = sum_roots w^(-m) of rescaled local factors")
def powsums(roots, M):
    return [mp.fsum(w**(-m) for w in roots) for m in range(1, M + 1)]
M = 4000
ly = [mp.e**(0.7j), mp.e**(-0.7j)]
s = powsums(ly, M)
print(f"  Lee-Yang (roots e^(+-0.7i)): Bohr mean of |s_m|^2 over m<={M} = {mp.nstr(mp.fsum(abs(x)**2 for x in s)/M,8)} (sum mult^2 = 2);"
      f" limsup-type max |s_m| over m in [3000,4000] = {mp.nstr(max(abs(x) for x in s[3000:]),8)}")
p = 5
zeta_s = [-(mp.mpf(p)**(-mp.mpf(m)/2)) for m in range(1, 9)]
print(f"  zeta at p={p} (root sqrt(p) outside the disc): s_m = -p^(-m/2): {[mp.nstr(x,5) for x in zeta_s[:6]]} -> 0")
gold = [(-mp.sqrt(5) + 1)/2, (-mp.sqrt(5) - 1)/2]
gs = powsums(gold, 8)
print(f"  golden fake at p=5 (z^2+sqrt5 z+1, one root -1/phi inside the disc): s_m = {[mp.nstr(mp.re(x),6) for x in gs]} (= (-1)^m (phi^m + phi^-m), grows like phi^m)")
print("conjecture1_proved = False")
