import sys,time; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
for N in (16,24,32):
  for kind in ('ZK','E'):
    t=time.time(); A=np.log(20.5)/2; F=Form(A,kind)
    out=[]
    for par in (0,1):
        M,G=real_sector(F,sector_basis(A,N,par),par); out.append(gmin(M,G)[0])
    print(N,kind,out,time.time()-t)
