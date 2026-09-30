import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
N=40
lp=mangoldt(200)
def setup(x,par):
    A=np.log(x)/2; kap=sector_basis(A,N,par); F=Form(A,'ZK')
    M,G,P=real_sector(F,kap,par,parts=True); base=P['pole']+P['arch']
    ns=[n for n in range(2,F.nmax+1) if lp[n]]; T={}
    for n in ns:
        F.pr=[(n,1.0,float(np.log(n)))]; _,_,Pn=real_sector(F,kap,par,parts=True); T[n]=Pn['comb']
    return base,G,T,ns
def lam_c(base,G,T,c):
    M=base.copy()
    for n,cn in c.items(): M-= cn/np.sqrt(n)*T[n]
    e,V=gmin(M,G,vec=True); return e[0],V[:,0]/np.sqrt(V[:,0]@G@V[:,0])
def box(x,par):
    base,G,T,ns=setup(x,par)
    c={n:(2*np.log(lp[n]) if (chi_m20(n)==1 or n%1==0) else 0) for n in ns}  # start
    c={n:float(weights_mp('ZK',max(ns))[n]) for n in ns}
    best=1e9
    for it in range(30):
        l,v=lam_c(base,G,T,c); best=min(best,l)
        c={n:2*np.log(lp[n])*np.sign(v@T[n]@v) for n in ns}
    return best
def euler(x,par,grid=24):
    base,G,T,ns=setup(x,par)
    ps=sorted(set(lp[n] for n in ns)); th={p:(0.0 if chi_m20(p)==1 else (np.pi/2 if chi_m20(p)==-1 else None)) for p in ps}
    def cvec(th):
        c={}
        for n in ns:
            p=lp[n]; k=round(np.log(n)/np.log(p))
            c[n]= np.log(p)*(1 if th[p] is None else 2*np.cos(k*th[p]))  # ramified: single unit root 1 (chi=0) ; keep as zeta_K
        return c
    l0=lam_c(base,G,T,cvec(th))[0]; best=l0
    for sweep in range(3):
        for p in ps:
            if th[p] is None: continue
            vals=[]
            for t in np.linspace(0,np.pi,grid+1):
                th2=dict(th); th2[p]=t; vals.append((lam_c(base,G,T,cvec(th2))[0],t))
            best,th[p]=min(vals)
    return l0,best,th
if __name__=="__main__":
 for x in [float(a) for a in sys.argv[1:]]:
     b=[box(x,p) for p in (0,1)]
     eu=[euler(x,p) for p in (0,1)]
     print(f'x={x}: box worst even {b[0]:+.3e} odd {b[1]:+.3e} | euler-shaped: ZK {eu[0][0]:+.3e}/{eu[1][0]:+.3e} adversarial {eu[0][1]:+.3e}/{eu[1][1]:+.3e}',flush=True)
     print('   adversarial angles even:',{p:round(t,3) for p,t in eu[0][2].items() if t is not None})
 