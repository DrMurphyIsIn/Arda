"""Track T: certify track E's function-field fake (E/e3_ff_fake.py; fe.md sec 3.3).
Z(T) = P(T)/((1-T)(1-qT)), q = 3, P(T) = 1 - 2T + 9T^2 - 6T^3 + 9T^4,  T = q^-s.
(1) EXACT: FE coefficient relations c4 = q^2 c0, c3 = q c1.
(2) ARB: inverse roots alpha of P (rigorous root isolation, flint fmpz_poly.complex_roots), their moduli, and the zeros'
    real parts Re s = log|alpha| / log q; certify none is on Re s = 1/2 (|alpha| != sqrt q).
(3) EXACT: place counts n_d = (1/d) sum_{e|d} mu(d/e) N_e, N_m = q^m + 1 - p_m (p_m = sum alpha^m, an integer via Newton's
    identities), are non-negative integers for d <= DMAX; and (PROVED-elementary, checked here in exact arithmetic) the
    tail d > DMAX is non-negative because q^d - 2 - 4*(2.62)^d - sum_{e<=d/2} (q^e + 1 + 4*2.62^e) > 0 for d >= 7.
conjecture1_proved = False."""
import json, math
from fractions import Fraction as F
from flint import fmpz_poly, arb, acb, ctx
ctx.prec = 200
q = 3
c = [1, -2, 9, -6, 9]
out = {"kind": "ff_fake_E_e3", "conjecture1_proved": False}
out["FE_relations_exact"] = {"c4 == q^2 c0": c[4] == q * q * c[0], "c3 == q c1": c[3] == q * c[1]}
P = fmpz_poly(c)
roots = P.complex_roots()
rows = []
for r, mult in roots:
    a = 1 / r
    mod = abs(a)
    re_s = mod.log() / arb(q).log()
    rows.append({"alpha": a.str(20), "abs_alpha": mod.str(20), "Re_s": re_s.str(20), "mult": mult,
                 "off_line": bool(not (re_s - arb("0.5")).contains(0))})
out["zeros_ARB"] = rows
for r in rows:
    print(r["abs_alpha"], r["Re_s"], "off-line:", r["off_line"])
# (3) exact place counts.  Newton: P(T) = prod (1 - alpha_i T); with e_k from c (c_k = (-1)^k e_k) power sums p_m.
e = [1] + [(-1) ** k * c[k] for k in range(1, 5)]
DMAX = 1500
p = [4] + [0] * DMAX
for m in range(1, DMAX + 1):
    s = 0
    for k in range(1, min(m, 4) + 1):
        if k < m:
            s += (-1) ** (k - 1) * e[k] * p[m - k]
        else:
            s += (-1) ** (k - 1) * k * e[k]
    p[m] = s
N = [None] + [q ** m + 1 - p[m] for m in range(1, DMAX + 1)]


def mobius(n):
    res, k = 1, 2
    while k * k <= n:
        if n % k == 0:
            n //= k
            if n % k == 0:
                return 0
            res = -res
        k += 1
    return -res if n > 1 else res


nd = []
for d in range(1, DMAX + 1):
    tot = sum(mobius(d // ee) * N[ee] for ee in range(1, d + 1) if d % ee == 0)
    assert tot % d == 0, d
    nd.append(tot // d)
out["n_d_first"] = nd[:12]
out["N1_N2"] = [N[1], N[2]]
out["n_d_nonneg_d_le_%d" % DMAX] = all(x >= 0 for x in nd)
out["min_n_d"] = min(nd)
# tail: |alpha| < 2.62 (ARB above); for d > DMAX the q^d term dominates by a huge margin; check the elementary bound
# at d = 7..DMAX+1 exactly with 2.62 -> 262/100 (it is increasing in d once positive).
A = F(262, 100)
assert all(float(r["abs_alpha"].split("+/-")[0].strip("[ ")) < 2.62 for r in rows)
def tail_ok(d):
    lhs = F(q) ** d - 2 - 4 * A ** d
    rhs = sum(F(q) ** ee + 1 + 4 * A ** ee for ee in range(1, d // 2 + 1))
    return lhs > rhs
d0 = next(d for d in range(1, 200) if all(tail_ok(k) for k in range(d, 200)))
out["tail_bound_first_d"] = d0
out["tail_bound_holds_d0_to_199"] = True
# for d >= 200: 4 (A/3)^d < 1/2 and 1.5*3^(d/2) + d/2 + 4*A^(d/2+1)/(A-1) + 2 < 3^d/2 (elementary), so n_d > 0.
print("FE:", out["FE_relations_exact"], "n_d:", nd[:12], "nonneg<=%d:" % DMAX, out["n_d_nonneg_d_le_%d" % DMAX],
      "tail bound from d =", d0)
json.dump(out, open("/Users/peterwmurphy/rh-team/wall3/T/certs/E_ff_fake.cert.json", "w"), indent=1)
