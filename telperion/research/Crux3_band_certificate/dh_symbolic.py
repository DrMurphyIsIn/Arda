"""Symbolic Dirichlet coefficients of -D'/D: c(n) = a(n) log n - sum_{d|n, 1<d<n} c(d) a(n/d),
a(n) = 1, k, -k, -1, 0 for n = 1,2,3,4,0 mod 5.  Represent c(n) as {prime p: poly in k (dict deg->Fraction)}."""
from fractions import Fraction as Fr
import sympy as sp
k = sp.Symbol('k')
L = {p: sp.Symbol('L%d' % p) for p in sp.primerange(2, 60)}
def a(n):
    return {1: 1, 2: k, 3: -k, 4: -1, 0: 0}[n % 5]
def logsym(n):
    return sum(e * L[p] for p, e in sp.factorint(n).items())
c = {1: 0}
for n in range(2, 57):
    val = a(n) * logsym(n) - sum(c[d] * a(n // d) for d in sp.divisors(n) if 1 < d < n)
    c[n] = sp.expand(val)
maxdeg = 0
for n in range(2, 57):
    poly = sp.Poly(c[n], k, *L.values())
    d = sp.degree(c[n], k) if c[n] != 0 else 0
    maxdeg = max(maxdeg, d)
print('max k-degree', maxdeg)
for n in (2, 4, 6, 12, 24, 32, 36, 48):
    print(n, c[n])
import mpmath as mpm
kv = (mpm.sqrt(10 - 2 * mpm.sqrt(5)) - 2) / (mpm.sqrt(5) - 1)
from weilmodes import lambda_dh
import mpmath as mp
lam = lambda_dh(56)
err = 0
for n in range(2, 57):
    v = c[n].subs(k, sp.Float(str(kv), 30)).subs({L[p]: sp.Float(str(mp.log(p)), 30) for p in L})
    err = max(err, abs(float(v) - float(lam[n])))
print('max |symbolic - numeric| =', err)
import json
out = {}
for n in range(2, 57):
    terms = {}
    for p in L:
        coeff = sp.expand(c[n]).coeff(L[p])
        if coeff != 0:
            pk = sp.Poly(coeff, k)
            terms[p] = {int(m[0]): str(Fr(int(sp.fraction(cf)[0]), int(sp.fraction(cf)[1]))) for m, cf in zip(pk.monoms(), pk.coeffs())}
    out[n] = terms
json.dump(out, open('dh_coeffs.json', 'w'), indent=0)
print('nonzero n:', [n for n in out if out[n]])
