import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
import numpy as np, mpmath as mp, bcore
from bcore import Form, real_sector, sector_basis, gmin
mp.mp.dps=30
k=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def wD(nmax):
    aD=[0]+[ {1:1,2:k,3:-k,4:-1,0:0}[n%5] for n in range(1,nmax+1)]
    c=[mp.mpf(0)]*(nmax+1)
    for n in range(2,nmax+1):
        acc=aD[n]*mp.log(n)
        for d in range(2,n):
            if n%d==0: acc-=c[d]*aD[n//d]
        c[n]=acc
    return c
_w=bcore.weights_mp; _f=bcore.families
bcore.weights_mp=lambda kind,n: wD(n) if kind=='D' else _w(kind,n)
bcore.families=lambda kind: [(mp.mpf(3)/2, mp.log(5/mp.pi))] if kind=='D' else _f(kind)

def analyze(kind,x,N=40,par=0):
    A=float(mp.log(x))/2
    F=Form(A,kind); kap=sector_basis(A,N,par,'neumann')
    M,G,P=real_sector(F,kap,par,parts=True)
    Q0=P['arch']-P['comb']; pole=P['pole']
    if kind=='D': M=Q0.copy()
    e,V=gmin(M,G,vec=True); e0,V0=gmin(Q0,G,vec=True)
    u=np.linspace(-A,A,4001); B=np.array([np.cos(kk*u) if par==0 else np.sin(kk*u) for kk in kap]).T
    def sc(v):
        f=B@v; f=f/np.max(np.abs(f)); s=np.sign(f[np.abs(f)>1e-3]); return int(np.sum(s[1:]!=s[:-1])), float(f.min()), float(f.max())
    v=V[:,0]; v0=V0[:,0]
    res=dict(kind=kind,x=x,par=par,lam=e[0],lam2=e[1],ind_full=int(np.sum(e<0)),
             lam0_Q0=e0[0],ind_Q0=int(np.sum(e0<0)),
             signs_full=sc(v),signs_Q0gs=sc(v0),
             pole_on_fullmin=float(v@pole@v/(v@G@v)), Q0_on_fullmin=float(v@Q0@v/(v@G@v)),
             pole_on_Q0gs=float(v0@pole@v0/(v0@G@v0)))
    # positive cone: symmetrized nonneg bumps
    if par==0:
        nb=24; cent=np.linspace(0,A*0.97,nb); w=A/nb*1.6
        phis=[]
        for cj in cent:
            ph=np.exp(-((u-cj)/w)**2)+np.exp(-((u+cj)/w)**2); phis.append(ph)
        du=u[1]-u[0]
        b=np.array([[np.sum(ph*B[:,m])*du for m in range(N)] for ph in phis])
        a=np.linalg.solve(G,b.T).T  # coeffs
        # projection residual check
        rec=np.max(np.abs(a@B.T-np.array(phis)))
        Mc=a@M@a.T; Gc=a@G@a.T
        L=np.linalg.cholesky((Gc+Gc.T)/2); Li=np.linalg.inv(L)
        best=np.inf; rng=np.random.default_rng(0)
        for t in range(4):
            be=rng.random(nb)+0.1
            for it in range(10):
                al=be*be; nrm=al@Gc@al; q=al@Mc@al/nrm
                g=(2*(Mc@al)-2*q*(Gc@al))/nrm*2*be
                be=be-1e-2*g/ (np.linalg.norm(g)+1e-30)*min(1,np.linalg.norm(g))*np.linalg.norm(be)
            best=min(best,q)
        res['cone_min']=best; res['cone_projerr']=float(rec)
    return res

if __name__=='__main__':
    import json
    runs=[('zeta',x) for x in (2,8,14,20)]+[('ZK',x) for x in (8,16,20,24,28)]+[('E',x) for x in (8,16,19,20.5,22,24,28)]+[('D',x) for x in (8,20,28,35,40)]
    for kind,x in runs:
        for par in (0,1):
            r=analyze(kind,x,N=40,par=par)
            print(json.dumps({kk:(round(v,6) if isinstance(v,float) and abs(v)>1e-4 else v) for kk,v in r.items()}),flush=True)
