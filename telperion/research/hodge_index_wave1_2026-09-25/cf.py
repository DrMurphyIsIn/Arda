import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
N=40
wZ=[float(v) for v in weights_mp('ZK',60)]; wE=[float(v) for v in weights_mp('E',60)]
def lam(x,par,w):
    A=np.log(x)/2; F=Form(A,'E')
    F.pr=[(n,w[n]/np.sqrt(n),float(np.log(n))) for n in range(2,F.nmax+1) if w[n]!=0]
    M,G=real_sector(F,sector_basis(A,N,par),par); return gmin(M,G)[0]
def thresh(w,par,lo=12,hi=40):
    xs=np.arange(lo,hi+0.01,1.0); prev=None
    for x in xs:
        if lam(x,par,w)<0:
            a,b=x-1,x
            for _ in range(10):
                m=(a+b)/2
                if lam(m,par,w)<0: b=m
                else: a=m
            return round((a+b)/2,3)
    return '>%d'%hi
cases={'E':{},'E, c(14)=0':{14:0},'E, c(6)=0':{6:0},'E, c(9)->ZK':{9:wZ[9]},'E, c(21)=0':{21:0},
 'E, composites (6,14,21)=0':{6:0,14:0,21:0},'E + ZK at 2,3,7 (add split-prime atoms)':{2:wZ[2],3:wZ[3],7:wZ[7]}}
for lab,mod in cases.items():
    w=list(wE)
    for n,v in mod.items(): w[n]=v
    print(lab,' even',thresh(w,0),' odd',thresh(w,1),flush=True)
