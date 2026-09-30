import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
import bcore, numpy as np, mpmath as mp
def kron(D,n):
    # Kronecker symbol (D/n), D fundamental discriminant
    if n==0: return 0
    res=1
    while n%2==0:
        n//=2
        if D%2==0: return 0
        res*= 1 if D%8 in (1,7) else -1
    # Jacobi (D/n) n odd
    a=D%n; j=1; m=n
    while a:
        while a%2==0:
            a//=2
            if m%8 in (3,5): j=-j
        a,m=m,a
        if a%4==3 and m%4==3: j=-j
        a%=m
    return res*j if m==1 else 0
orig_w=bcore.weights_mp; orig_f=bcore.families
def install(D):
    def w(kind,nmax):
        if kind!='DK': return orig_w(kind,nmax)
        lp=bcore.mangoldt(nmax)
        return [mp.log(lp[n])*(1+kron(D,n)) if lp[n] else mp.mpf(0) for n in range(nmax+1)]
    def f(kind):
        if kind!='DK': return orig_f(kind)
        return [(mp.mpf(1)/2,-mp.log(mp.pi)),(mp.mpf(3)/2,mp.log(abs(D)/mp.pi))]
    bcore.weights_mp=w; bcore.families=f
def run(kind,x,N=40,basis='neumann'):
    A=float(mp.log(x))/2
    F=bcore.Form(A,kind)
    kap=bcore.sector_basis(A,N,0,basis)
    M,G,P=bcore.real_sector(F,kap,0,parts=True)
    e,V=bcore.gmin(M,G,vec=True)
    Q0=P['arch']-P['comb']; e0,V0=bcore.gmin(Q0,G,vec=True)
    u=np.linspace(-A,A,4001)
    Phi=np.array([np.cos(k*u) for k in kap])
    fn=V[:,0]@Phi; fn/=fn[np.argmax(abs(fn))]
    sc=int(np.sum(np.sign(fn[1:])!=np.sign(fn[:-1])))
    return e[0],e[1],sc,fn.min(),e0[0],e0[1]
if __name__=='__main__':
    D=int(sys.argv[1]); kind=sys.argv[2]; basis=sys.argv[4] if len(sys.argv)>4 else 'neumann'
    install(D)
    for x in [float(t) for t in sys.argv[3].split(',')]:
        for N in (32,48):
            r=run(kind,x,N,basis)
            print(f"D={D} {kind} x={x} N={N} {basis} lam={r[0]:.3e} lam2={r[1]:.3e} signch={r[2]} minf={r[3]:.3e} Q0eig=({r[4]:.3f},{r[5]:.4f})",flush=True)
