import mpmath as mp
from fractions import Fraction as Fr
from cf_core import *
mp.mp.dps = 50
Q = Fr(9,17); M = 9
ks = [Fr(2*i+1,1)*17/18 for i in range(M)]
ss = [1 if i%2==0 else -1 for i in range(M)]
cs = [Fr(-33,100),Fr(-1,50),Fr(-37,100),Fr(23,100),Fr(-3,10),Fr(3,25),Fr(-37,100),Fr(1),Fr(-1,4)]
rhoE = {4:Fr(1),5:Fr(1),6:Fr(2),9:Fr(3),14:Fr(2),16:Fr(1,2),21:Fr(4),25:Fr(1,2)}
rhoK = {2:Fr(1),3:Fr(2),4:Fr(1,2),5:Fr(1),7:Fr(2),8:Fr(1,3),9:Fr(1),16:Fr(1,4),23:Fr(2),25:Fr(1,2),27:Fr(2,3)}
PI = mp.pi
A = mp.mpf(9)/17*PI
def F(x): return mp.mpf(x.numerator)/x.denominator
def alpha(m):
    s = Fr(0)
    for i in range(M):
        if i!=m: s += cs[i]*ss[i]*ks[i]/(ks[i]**2-ks[m]**2)
    return cs[m]**2/(2*ks[m]) + 2*cs[m]*ss[m]*s
al=[alpha(m) for m in range(M)]
def gstar(y):
    return (2*A-y)/2*sum(F(cs[i])**2*mp.cos(F(ks[i])*y) for i in range(M)) + sum(F(al[m])*mp.sin(F(ks[m])*y) for m in range(M))
# check gstar vs Window G
W = Window(A, [F(k) for k in ks], ss)
y=mp.mpf('1.234')
print("gstar check", gstar(y), sum(F(cs[i])*F(cs[j])*W.G(i,j,y) for i in range(M) for j in range(M)))
PE = sum(2*F(rhoE.get(n,Fr(0)))*mp.log(n)/mp.sqrt(n)*gstar(mp.log(n)) for n in range(1,28))
PK = sum(2*F(rhoK.get(n,Fr(0)))*mp.log(n)/mp.sqrt(n)*gstar(mp.log(n)) for n in range(1,28))
print("PE", PE, "PK", PK)
C2 = sum(c*c for c in cs)
rhoP = sum(cs[i]*2*ks[i]*ss[i]/(ks[i]**2+Fr(1,4)) for i in range(M))
print("C2", C2, float(C2), "rhoP", float(rhoP))
def tau1(b): return 4*b*sum(cs[i]**2/(4*b*b+ks[i]**2) for i in range(M))
def S(b): return sum(cs[i]*ss[i]*ks[i]/(4*b*b+ks[i]**2) for i in range(M))
N=300
t14 = sum(tau1(Fr(j)+Fr(1,4)) for j in range(N+1)); t34 = sum(tau1(Fr(j)+Fr(3,4)) for j in range(N+1))
s14 = sum(S(Fr(j)+Fr(1,4))**2 for j in range(N+1)); s34 = sum(S(Fr(j)+Fr(3,4))**2 for j in range(N+1))
print("tau sums", float(t14), float(t34), "S2 sums", float(s14), float(s34), "S0^2", float(S(Fr(1,4))**2), float(S(Fr(3,4))**2))
H = mp.harmonic(N); gam = mp.euler
L = mp.log(20/PI**2)
R = Fr(33)   # 2 k_max = 2*17*17/18 = 32.1
Kp = Fr(8,3)*sum(abs(cs[i])*ks[i] for i in range(M))
print("Kp", float(Kp), "2kmax", float(2*ks[-1]))
coshA2 = mp.cosh(A/2)
Em1 = mp.e**(-A); Em3 = mp.e**(-3*A)
g0 = A*F(C2)
archUp = 2*coshA2**2*F(rhoP)**2 + L*g0 + (-gam+H+mp.mpf(1)/4/N)*g0 - (A*F(t14)+2*F(s14)+2*Em1*F(S(Fr(1,4)))**2) \
   + (-gam+H+mp.mpf(3)/4/N)*g0 - (A*F(t34)+2*F(s34)+2*Em3*F(S(Fr(3,4)))**2) + (F(R)**2*g0 + F(Kp)**2/F(R))/(4*N*N)
archLo = 2*coshA2**2*F(rhoP)**2 + L*g0 + 2*(-gam+H)*g0 - (A*F(t14)+4*F(s14)) - (A*F(t34)+4*F(s34))
print("QE_up/g0 (true gamma)", (archUp-PE)/g0, "QK_lo/g0", (archLo-PK)/g0)
print("A", A, "g0", g0)
