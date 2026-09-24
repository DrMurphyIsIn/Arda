# Theorem 2 error budget, recomputed independently (log domain, mpmath 50 digits).
#   eps = (A+ + 5.3722) tau0(Tm - R)^2 + 4(e^L - 1) tauh(Tm)^2 + 12 L e^L sum_{k>=0} log(T+k+1) tauh(T+k-Tm)
#   kappa = c_m (sin(a x)/(a x))^{2m}, a = delta/(4m), c_m = a / I_m, I_m = int (sin u/u)^{2m} du
#   tau_y(X) = int_{|x|>X} |kappa(x+iy)| dx <= 2 c_m cosh(a y)^{2m} a^{-2m} X^{1-2m} / (2m-1)
#   I_m >= int_{-1}^{1} exp(-2 m u^2 / 5) du   (sin u/u >= 1 - u^2/6 >= exp(-u^2/5) on [-1,1])
#   R: smallest t with log(t/2pi) - 1/t >= A+  (Zhu Lemma 3.1 gives Psi_0 >= A+ beyond R).
# The k-sum is bounded rigorously: log(T+k+1) <= log(T+1) + k/(T+1), sum_{k>=0} (X+k)^{-s} <= X^{-s} + X^{1-s}/(s-1).
import mpmath as mp
mp.mp.dps = 50

PSI0_MIN = mp.mpf('-5.3722')   # min_t Psi_0(t) = psi(1/4) - log pi = -5.37215... (checked in psi0_check.py)

def I_m_lower(m):
    m = mp.mpf(m)
    return mp.sqrt(5 * mp.pi / (2 * m)) * mp.erf(mp.sqrt(2 * m / 5))

def log_tau(X, m, delta, y):
    a = mp.mpf(delta) / (4 * m)
    cm = a / I_m_lower(m)
    return (mp.log(2 * cm) + 2 * m * mp.log(mp.cosh(a * y)) - 2 * m * mp.log(a)
            + (1 - 2 * m) * mp.log(X) - mp.log(2 * m - 1))

def R_of(A):
    A = mp.mpf(A)
    f = lambda t: mp.log(t / (2 * mp.pi)) - 1 / t - A
    t0 = 2 * mp.pi * mp.e ** A
    R = mp.findroot(f, t0)
    return R * (1 + mp.mpf(10) ** -12)

def log_eps(L, T, A, delta, m, Tm):
    L = mp.mpf(L); T = mp.mpf(T); A = mp.mpf(A)
    R = R_of(A)
    if Tm <= R + 1 or T <= Tm + 1: return mp.inf, R
    t1 = mp.log(A - PSI0_MIN) + 2 * log_tau(Tm - R, m, delta, 0)
    t2 = mp.log(4 * (mp.e ** L - 1)) + 2 * log_tau(Tm, m, delta, mp.mpf(1) / 2)
    X = T - Tm; s = 2 * m - 1
    # sum_k log(T+k+1) (X+k)^{-s} <= log(T+1)[X^-s + X^{1-s}/(s-1)] + (1/(T+1)) sum_k k (X+k)^{-s}
    # sum_k k (X+k)^{-s} <= sum_k (X+k)^{1-s} <= X^{1-s} + X^{2-s}/(s-2)
    base = log_tau(X, m, delta, mp.mpf(1) / 2)          # = log(prefactor * X^{-s})
    fac = (mp.log(T + 1) * (1 + X / (s - 1)) + (X + X ** 2 / (s - 2)) / (T + 1))
    t3 = mp.log(12 * L * mp.e ** L) + base + mp.log(fac)
    mx = max(t1, t2, t3)
    return mx + mp.log(sum(mp.e ** (t - mx) for t in (t1, t2, t3))), R

def best(L, T, A, delta):
    bv = (mp.inf, None, None, None)
    R = R_of(A)
    for frac in [mp.mpf(x) / 200 for x in range(10, 190, 2)]:
        Tm = R + frac * (T - R)
        for m in [50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1500, 1700, 2000,
                  2300, 2600, 3000, 3500, 4000, 5000, 6000, 8000]:
            v, _ = log_eps(L, T, A, delta, m, Tm)
            if v < bv[0]: bv = (v, m, Tm, R)
    return bv

if __name__ == "__main__":
    import sys, json
    T = 640000
    rows = []
    cases = [
        ("2.25", "11.161373010", "KERNEL-certified A+ (Crux2_verified_window.primeSide_autocorr_le_cert, L'=2.3)"),
        ("2.25", "11.084", "builder's float CW value (cw_exact.py)"),
        ("2.25", "11.37", "robustness threshold quoted by the builder"),
    ]
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    def find(f):
        for d in (".", os.path.join(here, "..", "certificates")):
            if os.path.exists(os.path.join(d, f)): return os.path.join(d, f)
        return f
    for f, tag in [("cert_L225_N900.json", "2.2"), ("cert_L205_N820.json", "2.0"), ("cert_L14666_N600.json", "1.4166")]:
        try:
            c = json.load(open(find(f))); cases.append((tag, str(mp.mpf(c['Lam']) / c['S']), f"exact-integer Python certificate {f}"))
        except Exception as e:
            print("missing", f, e)
    for (L, A, note) in cases:
        v, m, Tm, R = best(L, T, A, "0.1")
        out = dict(L=L, Aplus=A, R=float(R), m=m, Tm=float(Tm), log10_eps=float(v / mp.log(10)), note=note)
        rows.append(out)
        print(f"L={L}  A+={A}  R={float(R):.6g}  m={m}  Tm={float(Tm):.6g}  log10 eps <= {float(v / mp.log(10)):.1f}   [{note}]", flush=True)
    json.dump(rows, open("eps_results.json", "w"), indent=1)
