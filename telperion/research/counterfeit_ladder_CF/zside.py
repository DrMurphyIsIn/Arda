import mpmath as mp, json
from cf_core import *
mp.mp.dps = 30
E = json.load(open('zeros_E_150.json')); K = json.load(open('zeros_ZK_150.json'))
Eon=[mp.mpf(x) for x in E['online']]; Eoff=[(mp.mpf(b),mp.mpf(g)) for b,g in E['offline']]
Kon=[mp.mpf(x) for x in K['zeta']]+[mp.mpf(x) for x in K['L20']]
T=mp.mpf(150)
def zero_side(W, c, on, off):
    F = lambda z: sum(c[i]*W.F(i,z) for i in range(len(c)))
    s_on = sum(2*F(t)**2 for t in on)
    s_off = sum(4*mp.re(F(mp.mpc(g, b-mp.mpf(1)/2))**2) for b,g in off)
    Cc = sum(c[i]*W.ss[i]*W.ks[i] for i in range(len(c)))
    # tail: F^2 ~ 4 C^2 cos^2(tA)/t^4, averaged 2C^2/t^4; density (1/pi) log(sqrt20 t/(2pi)); factor 2 for +-t
    tail = mp.quad(lambda t: 2*2*Cc**2/t**4*(1/mp.pi)*mp.log(mp.sqrt(20)*t/(2*mp.pi)), [T, mp.inf])
    return s_on, s_off, tail
N=80
cE = logderiv_coeffs(lattice_aE, N); cK = cK_list(N)
cases=[]
# (a) x = 28, 9 Dirichlet modes, E's least eigenvector
A = mp.log(28)/2; W = dirichlet_window(A/mp.pi, 9); Ms = matrices(W, cE, cK)
ev, V = mp.eigsy(Ms['QE']/A); i0=min(range(9), key=lambda i: ev[i]); v=[V[r,i0] for r in range(9)]
mx=max(v,key=abs); v=[x/mx for x in v]
cases.append(("x=28 eigvec", W, v, Ms))
# (b) the Lean test
from fractions import Fraction as Fr
cs=[Fr(-33,100),Fr(-1,50),Fr(-37,100),Fr(23,100),Fr(-3,10),Fr(3,25),Fr(-37,100),Fr(1),Fr(-1,4)]
W2 = dirichlet_window(mp.mpf(9)/17, 9); Ms2 = matrices(W2, cE, cK)
cases.append(("Lean test x=e^(18pi/17)", W2, [mp.mpf(x.numerator)/x.denominator for x in cs], Ms2))
for name, W, v, Ms in cases:
    nv = W.A*sum(x*x for x in v)
    aE = quadval(Ms['QE'], v); aK = quadval(Ms['QK'], v)
    on, off, tail = zero_side(W, v, Eon, Eoff)
    onK, _, tailK = zero_side(W, v, Kon, [])
    print(f"== {name}: ||v||^2 = {mp.nstr(nv,12)}")
    print(f"  E : arithmetic {mp.nstr(aE,12)}  zero side {mp.nstr(on+off+tail,12)} (on-line {mp.nstr(on,8)}, off-line quadruples {mp.nstr(off,8)}, tail {mp.nstr(tail,3)})  ratio/||v||^2 {mp.nstr(aE/nv,8)}")
    print(f"  ZK: arithmetic {mp.nstr(aK,12)}  zero side {mp.nstr(onK+tailK,12)} (tail {mp.nstr(tailK,3)})  ratio/||v||^2 {mp.nstr(aK/nv,8)}")
    # per off-line quadruple contribution
    F = lambda z: sum(v[i]*W.F(i,z) for i in range(len(v)))
    print("  first off-line quadruples:", [(mp.nstr(g,8), mp.nstr(4*mp.re(F(mp.mpc(g,b-0.5))**2),6)) for b,g in Eoff[:4]])
