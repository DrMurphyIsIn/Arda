from fractions import Fraction as Fr
from math import isqrt, gcd
def h_forms(D):  # class number of primitive pos-def forms disc -D (D>0, D=0,3 mod 4), weighted
    cnt=Fr(0)
    for a in range(1,isqrt(D//3)+2):
        for b in range(-a+1,a+1):
            if (b*b+D)%(4*a): continue
            c=(b*b+D)//(4*a)
            if c<a: continue
            if b<0 and a==c: continue
            if gcd(gcd(a,abs(b)),c)!=1: continue
            w=Fr(1,2) if (a==b==c) else (Fr(1,3) if (a==c and b==a) else Fr(1))
            cnt+= Fr(1,3) if (a==b and a==c) else (Fr(1,2) if (b==0 and a==c) else Fr(1))
    return cnt
def H(N):  # Hurwitz class number
    if N==0: return Fr(-1,12)
    if N%4 in (1,2): return Fr(0)
    s=Fr(0); f=1
    while f*f<=N:
        if N%(f*f)==0 and (N//(f*f))%4 in (0,3): s+=h_forms(N//(f*f))
        f+=1
    return s
def sigma(n): return sum(d for d in range(1,n+1) if n%d==0)
def lam(n): return sum(min(d,n//d) for d in range(1,n+1) if n%d==0)
ok=True
for n in range(1,41):
    fix=sum(H(4*n-t*t) for t in range(-isqrt(4*n),isqrt(4*n)+1))
    rhs=2*sigma(n)-lam(n)
    ok &= (fix==rhs)
    if n<=12 or not fix==rhs: print(n,'Gamma_Tn.Delta (CM fixed pts)=',fix,' 2sigma-lambda=',rhs)
print('Hurwitz-Kronecker Lefschetz identity on X(1), n<=40:',ok)
# 11a: eta(z)^2 eta(11z)^2
M=200; c=[0]*(M+1); c[0]=1
for n in range(1,M+1):
    for e,step in ((2,n),(2,11*n)):
        for _ in range(e):
            if step>M: continue
            for i in range(M,step-1,-1): c[i]-=c[i-step]
a=[0]+c[:M]  # a[n]=coef of q^n
import math
print('p  a_p(11a)  2sqrt(p) [Frobenius CS, Eichler-Shimura]  p+1 [char-0 Hecke CS, symmetric bidegree]')
for p in [2,3,5,7,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]:
    print(p,a[p],round(2*math.sqrt(p),2),p+1)
