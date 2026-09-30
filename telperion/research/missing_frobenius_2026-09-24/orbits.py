# "Orbit amplitudes" c(n) of -F'/F = sum c(n) n^-s  (trace-formula periodic-orbit side, orbit length log n)
# zeta: c = Lambda (prime powers only, 0<=c<=log n). D: computed by Dirichlet inversion c*a = a.log
import math
N=400
k=(math.sqrt(10-2*math.sqrt(5))-2)/(math.sqrt(5)-1)
aD=lambda n: [0,1,k,-k,-1][n%5]
aL=lambda n: [0,1,-1,-1,1][n%5]
def logderiv(a):
    c=[0.0]*(N+1)
    for n in range(2,N+1):
        s=a(n)*math.log(n)
        for d in range(1,n):
            if n%d==0 and d>1: pass
        # a(n)log n = sum_{d|n} c(d) a(n/d), a(1)=1
        s=a(n)*math.log(n)-sum(c[d]*a(n//d) for d in range(2,n) if n%d==0)
        c[n]=s
    return c
def ispp(n):
    for p in range(2,n+1):
        if n%p==0:
            while n%p==0: n//=p
            return n==1
cD=logderiv(aD); cL=logderiv(aL)
print('kappa',k)
print('max |c_L5| on non-prime-powers:', max(abs(cL[n]) for n in range(2,N+1) if not ispp(n)))
bad=[(n,round(cD[n],4)) for n in range(2,40) if not ispp(n)]
print('D amplitudes at non-prime-powers n<40:',bad)
# growth test: max |c_D(n)|/log n in dyadic blocks
b=2
while b<N:
    blk=range(b,min(2*b,N+1)); print('block',b, 'max|cD|/log n =', round(max(abs(cD[n])/math.log(n) for n in blk),3), ' max|cL5|/log n =', round(max(abs(cL[n])/math.log(n) for n in blk),3))
    b*=2
