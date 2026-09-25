# independent: E coefficients by brute-force lattice count, then -E'/E via Dirichlet-series log
import math
N=130
r=[0]*(N+1)
for x in range(-12,13):
  for y in range(-6,7):
    q=x*x+5*y*y
    if 0<q<=N: r[q]+=1
a=[0]+[r[n]/2 for n in range(1,N+1)]
assert a[1]==1
# log E = sum b(n) n^-s ; n b(n) log... use c(n) = coefficient of -E'/E: E' -> -a(n)log n
c=[0.0]*(N+1)
for n in range(2,N+1):
  s=a[n]*math.log(n)
  for d in range(2,n):
    if n%d==0: s-=c[d]*a[n//d]
  c[n]=s
neg=[(n,round(c[n],3)) for n in range(2,N+1) if c[n]<-1e-9]
print("E negatives:",neg[:6])
print("E nonzero c(n), n<36:",[(n,round(c[n],3)) for n in range(2,36) if abs(c[n])>1e-9])
