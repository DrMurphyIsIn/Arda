import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
N=48
def lam(kind,x,par):
    A=np.log(x)/2; F=Form(A,kind); M,G=real_sector(F,sector_basis(A,N,par),par); return gmin(M,G)[0]
h=0.02
for kind,n in [('ZK',9),('E',9),('E',14),('ZK',16),('E',16),('E',21),('ZK',23),('ZK',25),('E',25)]:
    out=[]
    for par in (0,1):
        a,b,c,d=[lam(kind,n+t,par) for t in (-2*h,-h+1e-9,h,2*h)]
        sl=(b-a)/h; sr=(d-c)/h
        out.append(f'par{par}: slopeL={sl:+.4e} slopeR={sr:+.4e} jump={sr-sl:+.3e}')
    print(kind,n,' | '.join(out),flush=True)
print('E odd fine:')
for x in np.arange(20.9,22.01,0.1): print(round(x,2), '%.4e'%lam('E',x,1),flush=True)
