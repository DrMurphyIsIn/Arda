import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
wZ=weights_mp('ZK',40); wE=weights_mp('E',40)
for n in range(2,41):
    if wZ[n]!=0 or wE[n]!=0: print(n, float(wZ[n]), float(wE[n]), float(wE[n]-wZ[n]), 'chi',chi_m20(n))
