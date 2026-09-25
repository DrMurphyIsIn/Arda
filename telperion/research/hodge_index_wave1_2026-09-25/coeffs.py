import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
import mpmath as mp
from bcore import weights_mp
mp.mp.dps=30
N=200
cE=weights_mp('E',N)
neg=[(n,float(cE[n])) for n in range(2,N+1) if cE[n]< -1e-20]
print('E: first negative c_E(n):',neg[:8])
k=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
aD=[0]+[ {1:1,2:k,3:-k,4:-1,0:0}[n%5] for n in range(1,N+1)]
c=[mp.mpf(0)]*(N+1)
for n in range(2,N+1):
    acc=aD[n]*mp.log(n)
    for d in range(2,n):
        if n%d==0: acc-=c[d]*aD[n//d]
    c[n]=acc
print('kappa',k)
print('D: c_D(n) n<=40:',[(n,round(float(c[n]),4)) for n in range(2,41) if abs(c[n])>1e-20])
print('D first negative:',[n for n in range(2,60) if c[n]<-1e-20][:10])
