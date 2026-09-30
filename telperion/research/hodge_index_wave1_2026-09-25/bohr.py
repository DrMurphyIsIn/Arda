# Lee-Yang in Bohr fugacities: sup Re of zeros of E and D in sigma>1
import numpy as np, mpmath as mp
N=10**7
sieve=np.ones(N+1,bool); sieve[:2]=False
for i in range(2,int(N**.5)+1):
    if sieve[i]: sieve[i*i::i]=False
P=np.nonzero(sieve)[0].astype(float)
def S_E(s):  # sum m_p 2 arctan(p^-s) over non-principal primes of Q(sqrt-5)
    pm=P%20
    m=np.where(P==2,1.0,np.where((pm==3)|(pm==7),2.0,0.0))
    return np.sum(m*2*np.arctan(P**(-s)))
def S_D(s):
    pm=P%5; m=np.where((pm==2)|(pm==3),1.0,0.0)
    return np.sum(m*2*np.arctan(P**(-s)))
kap=float((mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1))
tD=np.pi-2*np.arctan(kap)
def solve(S,target,lo=1.0001,hi=3.0):
    for _ in range(60):
        mid=(lo+hi)/2
        if S(mid)>target: lo=mid
        else: hi=mid
    return lo
# tail correction: primes > N contribute ~ sum 2 p^-s density 1/(2 or 4) -> estimate
def tail(s,dens): return dens*2*mp.quad(lambda u: u**(-s)/mp.log(u),[N,mp.inf])
sE=solve(S_E,np.pi); sD=solve(S_D,tD)
print('sigma*_E (primes<1e7) =',sE,' tail at s*:',float(tail(sE,0.5)))  # split nonprincipal density: (2 of 8 classes)*m=2 -> 1/2 weighted
print('sigma*_D (primes<1e7) =',sD,' target',tD,' tail:',float(tail(sD,0.5)))
print('partial sums at s=1.01: E',S_E(1.01),' D',S_D(1.01))
# how many primes needed to exceed pi at sigma=1 + eps
for s in (1.05,1.1,1.2):
    print(s,'S_E',S_E(s),'S_D',S_D(s))
sE2=solve(lambda s: S_E(s)+float(tail(s,0.5)),np.pi); sD2=solve(lambda s: S_D(s)+float(tail(s,0.5)),tD)
print('with tail: sigma*_E =',sE2,' sigma*_D =',sD2)
