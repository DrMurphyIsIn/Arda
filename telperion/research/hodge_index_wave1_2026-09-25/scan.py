import sys,time,pickle; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
N=int(sys.argv[1]); xs=np.round(np.arange(8,26.01,0.1),3)
res={}
for kind in ('ZK','E'):
  for x in xs:
    A=np.log(x)/2; F=Form(A,kind); r=[]
    for par in (0,1):
        M,G=real_sector(F,sector_basis(A,N,par),par); r.append(gmin(M,G)[:2])
    res[(kind,x)]=r
pickle.dump(res,open(f'scan_N{N}.pkl','wb'))
for x in xs:
    print(x, ' '.join('%s e0=%.3e o0=%.3e'%(k,res[(k,x)][0][0],res[(k,x)][1][0]) for k in ('ZK','E')))
