import mpmath as mp
from fractions import Fraction as Fr
mp.mp.dps = 60
exec(open("gen_cert.py").read())
def fl(x, d):  # floor to d digits
    return Fr(int(mp.floor(x*10**d)), 10**d)
def ce(x, d):
    return Fr(int(mp.ceil(x*10**d)), 10**d)
def qs(x):
    x=Fr(x)
    return f"(({x.numerator} : ℚ) / {x.denominator})" if x.denominator!=1 else f"({x.numerator} : ℚ)"
ent=[]
for n in range(1,28):
    ln = mp.log(n)
    lo = fl(ln,16) - Fr(1,10**16) if n>1 else Fr(0)
    hi = ce(ln,16) + Fr(1,10**16) if n>1 else Fr(0)
    isq = 1/mp.sqrt(n)
    q0 = fl(isq,18) - Fr(1,10**18); q1 = ce(isq,18)+Fr(1,10**18)
    if n==1: q0=Fr(1); q1=Fr(1)
    ms = [int(mp.nint(F(ks[i])*ln/(2*mp.pi))) for i in range(M)]
    ent.append((n,lo,hi,q0,q1,ms))
lines=["def tabM : ℕ → MEntry"]
for (n,lo,hi,q0,q1,ms) in ent:
    lines.append(f"  | {n} => ⟨{qs(lo)}, {qs(hi)}, {qs(q0)}, {qs(q1)}, {ms}⟩")
lines.append("  | _ => ⟨0, 0, 0, 0, []⟩")
open('tab.lean.txt','w').write("\n".join(lines))
print("\n".join(lines[:3]))
print("PE",PE,"PK",PK)
print("PE_lo", fl(PE,9), "PK_hi", ce(PK,9))
print("t14 lo/hi", fl(F(t14),12), ce(F(t14),12), "t34", fl(F(t34),12), ce(F(t34),12))
print("s14 lo/hi", fl(F(s14),12), ce(F(s14),12), "s34", fl(F(s34),12), ce(F(s34),12))
print("H300 lo", fl(mp.harmonic(300),12), "H100 lo", fl(mp.harmonic(100),12), "log101 hi", ce(mp.log(101),15))
print("log20", fl(mp.log(20),15), ce(mp.log(20),15), "log28 lo", fl(mp.log(28),15))
print("rhoP", rhoP, "C2", C2, "Kp", Kp, "S14^2", S(Fr(1,4))**2, "S34^2", S(Fr(3,4))**2)
print("9PHI/34 up", ce(mp.mpf(9)*mp.mpf('3.14159265358979323847')/34,15), "9PLO/34 lo", fl(mp.mpf(9)*mp.mpf('3.14159265358979323846')/34,15))
print("9PHI/17 up", ce(mp.mpf(9)*mp.mpf('3.14159265358979323847')/17,15), "27PHI/17 up", ce(mp.mpf(27)*mp.mpf('3.14159265358979323847')/17,15))
print("exp(A/2)", mp.e**(A/2), "exp(-A/2)", mp.e**(-A/2), "e^-A", mp.e**(-A), "e^-3A", mp.e**(-3*A))
