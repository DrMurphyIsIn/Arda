# -D'/D = sum a(n) n^{-s}; recursion d(n) log n = sum_{m|n} a(m) d(n/m), d(1)=1.
# Compare Lefschetz mass growth with zeta (Lambda(n) <= log n) and L(chi).
import numpy as np, math
N = 200000
kap = 0.28407904384041229603
dv = np.array([ {1:1.0,2:kap,3:-kap,4:-1.0,0:0.0}[n%5] for n in range(N+1)]); dv[0]=0
a = np.zeros(N+1)
acc = np.zeros(N+1)   # acc[n] = sum_{m|n, m<n} a(m) d(n/m)
for m in range(1, N+1):
    if m > 1:
        a[m] = dv[m]*math.log(m) - acc[m]
    am = a[m]
    if am != 0.0 and 2*m <= N:
        idx = np.arange(2*m, N+1, m)
        acc[idx] += am*dv[idx//m]
r = np.abs(a[2:])/np.log(np.arange(2, N+1))
lo = 2
while lo < N:
    hi = min(2*lo, N)
    seg = r[lo-2:hi-2]
    i = int(np.argmax(seg))+lo
    print(f"[{lo:6d},{hi:6d}) max |a(n)|/log n = {seg.max():10.4f} at n={i}")
    lo = hi
for s in [1.05, 1.1, 1.2, 1.5]:
    ns = np.arange(2, N+1)
    print("sigma", s, " partial sum |a(n)| n^-s up to N:", float(np.sum(np.abs(a[2:])*ns**(-s))), " vs zeta analog sum log n n^-s over prime powers ~ finite")
