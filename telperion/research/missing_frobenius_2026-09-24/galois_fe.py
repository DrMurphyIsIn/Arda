# Galois-coherence test for Davenport-Heilbronn D.
# D_y(s) = 5^{-s} (zeta(s,1/5) + y zeta(s,2/5) - y zeta(s,3/5) - zeta(s,4/5)),  y real.
# Lambda_y(s) = (5/pi)^{(s+1)/2} Gamma((s+1)/2) D_y(s)   (odd character mod 5, conductor 5)
# FE test: is Lambda_y(1-s) = w Lambda_y(s) for w = +1 or -1 ?
import mpmath as mp, sympy as sp
mp.mp.dps = 40
s5 = sp.sqrt(5)
kap = (sp.sqrt(10-2*s5)-2)/(s5-1)
x = sp.symbols('x')
mpk = sp.minimal_polynomial(kap, x)
print("minpoly(kappa) =", mpk)
fac = sp.factor(mpk, extension=sp.sqrt(5))
print("factor over Q(sqrt5):", fac)
roots = sorted([sp.N(r, 30) for r in sp.Poly(mpk, x).nroots(n=30)])
print("conjugates:", roots)
def Lam(y, s):
    s = mp.mpc(s)
    D = mp.power(5, -s)*(mp.zeta(s, mp.mpf(1)/5) + y*mp.zeta(s, mp.mpf(2)/5) - y*mp.zeta(s, mp.mpf(3)/5) - mp.zeta(s, mp.mpf(4)/5))
    return mp.power(mp.mpf(5)/mp.pi, (s+1)/2)*mp.gamma((s+1)/2)*D
pts = [mp.mpc(0.3, 2.0), mp.mpc(0.1, 7.5), mp.mpc(-0.4, 13.0), mp.mpc(0.2, 0)]
names = {}
kv = mp.mpf(str(sp.N(kap, 45)))
for r in roots:
    y = mp.mpf(str(r))
    tag = "kappa" if abs(y-kv) < 1e-20 else ("-1/kappa" if abs(y+1/kv) < 1e-20 else "sigma-conj (root of x^2+(1-sqrt5)x-1)")
    print(f"\ny = {mp.nstr(y,15)}  [{tag}]")
    for s in pts:
        a, b = Lam(y, 1-s), Lam(y, s)
        print("  s=", mp.nstr(s,4), " |L(1-s)-L(s)|/|L(s)|=", mp.nstr(abs(a-b)/abs(b),5), "  |L(1-s)+L(s)|/|L(s)|=", mp.nstr(abs(a+b)/abs(b),5))
# control: the Dirichlet L-function itself (y = i gives L(s,chi) with chi(2)=i):
print("\ncontrol L(s,chi) (y=i): FE maps to L(s,chibar) (y=-i) with root number eps:")
for s in pts[:2]:
    a = Lam(mp.mpc(0,1), 1-s); b = Lam(mp.mpc(0,-1), s)
    print("  ratio Lam_chi(1-s)/Lam_chibar(s) =", mp.nstr(a/b, 15), " |.|=", mp.nstr(abs(a/b),15))
