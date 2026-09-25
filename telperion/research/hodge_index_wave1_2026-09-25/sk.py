# Independent skeptic reproduction: g_k built by Fourier inversion of |F|^{2k} on the line (not by u-grid convolution)
import numpy as np, mpmath as mp, sys


def psi(z):  # complex digamma via mpmath vectorized is slow; use asymptotic w/ recurrence
    z=np.asarray(z,complex).copy(); acc=np.zeros_like(z)
    for _ in range(10): acc-=1/z; z=z+1
    z2=1/(z*z)
    return acc+np.log(z)-0.5/z-z2*(1/12-z2*(1/120-z2*(1/252-z2/240)))
def coeffs_from_a(a):
    N=len(a)-1; n=np.arange(N+1); c=a*np.log(np.maximum(n,1)); c[0]=0
    for d in range(2,N+1):
        if c[d]!=0: c[2*d::d]-=c[d]*a[2*(1):N//d+1] if False else c[d]*a[np.arange(2*d,N+1,d)//d]
    return c
def a_of(kind,N):
    a=np.zeros(N+1)
    if kind=='zeta': a[1:]=1
    elif kind=='E':  # brute force count of x^2+5y^2=n, (x,y) in Z^2, /2
        X=int(N**.5)+1
        for y in range(-X,X+1):
            r=5*y*y
            if r>N: continue
            xs=np.arange(-X,X+1); v=xs*xs+r; v=v[(v<=N)&(v>0)]
            np.add.at(a,v,0.5)
    elif kind=='ZK':  # zeta_K, K=Q(sqrt-5): a(n)=sum_{d|n} chi_-20(d)
        chi=np.zeros(N+1)
        for d in range(1,N+1):
            chi[d]=float(mp.re(0))
        # kronecker(-20,d)
        import sympy
        for d in range(1,N+1): chi[d]=sympy.jacobi_symbol(-20% (d if d%2 else 1),d) if False else 0
        from sympy.ntheory import legendre_symbol
        for d in range(1,N+1): chi[d]=kron(-20,d)
        for d in range(1,N+1): a[d::d]+=chi[d]
    elif kind=='D':
        k=float((mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)); tab=[0,1,k,-k,-1]
        a=np.array([tab[i%5] for i in range(N+1)],float); a[0]=0
    return a
def kron(D,n):
    import sympy
    return int(sympy.ntheory.residue_ntheory.jacobi_symbol(D% n,n)) if n%2 else _kron2(D,n)
def _kron2(D,n):
    from sympy import factorint
    r=1
    for p,e in factorint(n).items():
        if p==2: v=0 if D%2==0 else (1 if D%8 in (1,7) else -1)
        else:
            from sympy.ntheory import legendre_symbol
            v=0 if D%p==0 else legendre_symbol(D%p,p)
        r*=v**e
    return r
ARCH={'zeta':lambda t:-np.log(np.pi)+psi(.25+.5j*t).real,
      'ZK':lambda t:np.log(20)-2*np.log(2*np.pi)+2*psi(.5+1j*t).real,
      'E':lambda t:np.log(20)-2*np.log(2*np.pi)+2*psi(.5+1j*t).real,
      'D':lambda t:np.log(5/np.pi)+psi(.75+.5j*t).real}
POLE={'zeta':1,'ZK':1,'E':1,'D':0}
class Tst:
    def __init__(s,x,frac,m,g0):
        s.T=.5*np.log(x); s.eps=frac*s.T; s.T0=s.T-s.eps; s.m=m; s.g0=g0; s.x=x
    def F(s,z0):
        z=np.asarray(z0,complex)-.5-1j*s.g0; w=z*s.eps/s.m
        with np.errstate(all='ignore'): b=np.where(np.abs(w)<1e-9,1,np.sinh(w)/np.where(np.abs(w)<1e-9,1,w))**s.m
        return 2*np.cosh(s.T0*z)*b
def arith(kind,te,K,cache={}):
    N=int(te.x**K)+1
    if (kind,N) not in cache: cache[(kind,N)]=coeffs_from_a(a_of(kind,N))
    c=cache[(kind,N)]; ns=np.nonzero(np.abs(c)>1e-14)[0]; ns=ns[ns>=2]
    Nf=1<<21; dt=0.004; t=te.g0+(np.arange(Nf)-Nf//2)*dt
    Ft2=np.abs(te.F(.5+1j*t))**2; A=ARCH[kind](t)
    out=[]
    for k in range(1,K+1):
        gh=Ft2**k
        # g(u)=(1/2pi) sum gh e^{-itu} dt on u-grid
        du=2*np.pi/(Nf*dt); j=np.arange(Nf)-Nf//2; u=j*du
        # e^{-i t u} with t=g0+ l dt: factor e^{-i g0 u} * sum_l gh_l e^{-i l dt u}
        G=np.fft.fftshift(np.fft.fft(np.fft.ifftshift(gh)))*dt/(2*np.pi)*np.exp(-1j*te.g0*u)
        # fft uses e^{-2pi i l j/N} = e^{-i l dt u_j}: correct
        sel=np.abs(u)<k*np.log(te.x)+0.05
        us=u[sel]; Gs=G[sel]
        lg=np.log(ns); gv=np.interp(lg,us,Gs.real)+1j*np.interp(lg,us,Gs.imag)
        prime=np.sum(c[ns]/np.sqrt(ns)*2*gv.real)
        arch=np.sum(gh*A)*dt/(2*np.pi)
        pole=2*(te.F(1.)**k*np.conj(te.F(0.))**k).real*POLE[kind]
        out.append(pole+arch-prime)
    return np.array(out)
def zside(te,zeros,K):
    zeros=np.asarray(zeros,complex); lam=te.F(zeros)*np.conj(te.F(1-np.conj(zeros)))
    return np.array([np.sum(lam**k).real for k in range(1,K+1)]), lam
