"""Lane B core (float64 + mpmath digamma): window Weil form on [-A,A] (x = e^{2A}) for
   kind in {'zeta','ZK','E'}:
     zeta : Gamma_R(s), no conductor, pole, w = Lambda
     ZK   : zeta_K, K=Q(sqrt-5): Gamma_R(s)Gamma_R(s+1), conductor 20, pole, w = Lambda (1+chi_-20)
     E    : (1/2) sum' (x^2+5y^2)^{-s}, a(1)=1: same gamma/conductor/pole, w = c_E (-E'/E coefficients)
   Q(f) = Pole + Arch - Comb, complex-exponential closed forms of Crux3 FWindow (general kappa),
   re-implemented vectorized.  Real parity sectors built from +-kappa exponentials."""
import numpy as np, mpmath as mp
mp.mp.dps = 30

def chi_m4(n):
    r = n % 4
    return 0 if r % 2 == 0 else (1 if r == 1 else -1)
def leg5(n):
    return {0: 0, 1: 1, 4: 1, 2: -1, 3: -1}[n % 5]
def chi_m20(n):
    return chi_m4(n) * leg5(n)

def mangoldt(nmax):
    lam = [0.0] * (nmax + 1)
    for n in range(2, nmax + 1):
        m = n; p = next(q for q in range(2, n + 1) if m % q == 0)
        while m % p == 0: m //= p
        if m == 1: lam[n] = p
    return lam  # returns the prime p (0 if not prime power)

def weights_mp(kind, nmax):
    """w(n) as mpmath numbers, n = 0..nmax."""
    lp = mangoldt(nmax)
    if kind == 'zeta':
        return [mp.log(lp[n]) if lp[n] else mp.mpf(0) for n in range(nmax + 1)]
    if kind == 'ZK':
        return [mp.log(lp[n]) * (1 + chi_m20(n)) if lp[n] else mp.mpf(0) for n in range(nmax + 1)]
    if kind == 'E':
        # a(n) of (1/2) sum' Q^{-s}: (aK + aG)/2, aK = sum_{d|n} chi_-20(d), aG = sum_{d|n} chi_-4(d) chi_5(n/d)
        a = [mp.mpf(0)] * (nmax + 1)
        for n in range(1, nmax + 1):
            s = 0
            for d in range(1, n + 1):
                if n % d == 0:
                    s += chi_m20(d) + chi_m4(d) * leg5(n // d)
            a[n] = mp.mpf(s) / 2
        assert a[1] == 1
        c = [mp.mpf(0)] * (nmax + 1)
        for n in range(2, nmax + 1):
            acc = a[n] * mp.log(n)
            for d in range(2, n):
                if n % d == 0:
                    acc -= c[d] * a[n // d]
            c[n] = acc
        return c
    raise ValueError(kind)

def families(kind):
    if kind == 'zeta':
        return [(mp.mpf(1) / 2, -mp.log(mp.pi))]
    return [(mp.mpf(1) / 2, -mp.log(mp.pi)), (mp.mpf(3) / 2, mp.log(20 / mp.pi))]

class Form:
    def __init__(self, A, kind):
        self.A = mp.mpf(A); self.a = 2 * self.A; self.kind = kind
        x = mp.exp(self.a)
        nmax = int(mp.floor(x))
        if nmax == x: nmax -= 1
        self.nmax = nmax
        w = weights_mp(kind, nmax)
        self.pr = [(n, float(w[n] / mp.sqrt(n)), float(mp.log(n))) for n in range(2, nmax + 1) if w[n] != 0]
        self.fams = []
        for b0, c0 in families(kind):
            J = int(mp.ceil(80 / self.a)) + 4
            betas = [b0 + 2 * j for j in range(J)]
            CL = c0 + mp.digamma(b0 / 2) + sum(2 * mp.exp(-b * self.a) / b for b in betas)
            self.fams.append((b0, betas, CL))
        self.Af = float(self.A)

    def Ivals(self, lam):  # I(lam) summed over families, lam: array
        out = np.zeros(len(lam), complex)
        for b0, betas, CL in self.fams:
            ph = mp.digamma(b0 / 2)
            for i, l in enumerate(lam):
                l = mp.mpf(l)
                v = mp.digamma(mp.mpc(b0 / 2, -l / 2)) - ph
                for b in betas:
                    z = mp.mpc(b, -l)
                    v -= 2 * (mp.exp(-b * self.a) / b - mp.exp(-z * self.a) / z)
                out[i] += complex(v)
        return out

    def Cuvals(self, k):
        out = np.zeros(len(k))
        for b0, betas, CL in self.fams:
            for i, kk in enumerate(k):
                kk = mp.mpf(kk)
                v = mp.re(mp.polygamma(1, mp.mpc(b0 / 2, kk / 2))) / 2
                for b in betas:
                    z = mp.mpc(b, -kk)
                    v -= 2 * mp.re(mp.exp(-z * self.a) * (self.a / z + 1 / (z * z)))
                out[i] += float(v)
        return out

    def complex_mats(self, ks, parts=False):
        """M (Hermitian, Q = sum c_m conj c_n M[m,n]) and Gram, on e^{i k u} 1_[-A,A]."""
        A = self.Af; ks = np.asarray(ks, float); n = len(ks)
        CLs = sum(float(CL) for _, _, CL in self.fams)
        D = ks[:, None] - ks[None, :]
        z = np.abs(D) < 1e-14
        Ds = np.where(z, 1.0, D)
        gram = np.where(z, 2 * A, 2 * np.sin(Ds * A) / Ds)
        Ip = self.Ivals(ks); Im = self.Ivals(-ks)
        Cu = self.Cuvals(ks)
        e1 = np.exp(1j * Ds * A) / (2j * Ds); e2 = -np.exp(-1j * Ds * A) / (2j * Ds)
        arch = gram * CLs + e1 * (Ip[None, :] + Im[:, None]) + e2 * (Ip[:, None] + Im[None, :])
        diag = 2 * A * CLs + 2 * A * Ip.real + Cu
        arch = np.where(z, diag[:, None] * np.ones((1, n)), arch)
        comb = np.zeros((n, n), complex)
        for (_, c, y) in self.pr:
            E1 = np.exp(1j * Ds * A); E2 = np.exp(-1j * Ds * A)
            gp = (E1 * (np.exp(1j * ks[None, :] * y) + np.exp(-1j * ks[:, None] * y))
                  - E2 * (np.exp(1j * ks[:, None] * y) + np.exp(-1j * ks[None, :] * y))) / (1j * Ds)
            gp0 = 2 * (2 * A - y) * np.cos(ks[:, None] * y) * np.ones((1, n))
            comb += c * np.where(z, gp0, gp)
        h = 0.5j
        F = lambda k, zz: 2 * np.sin((k + zz) * A) / (k + zz)
        Fp = F(ks, h); Fm = F(ks, -h)
        pole = Fp[:, None] * np.conj(Fm)[None, :] + Fm[:, None] * np.conj(Fp)[None, :]
        M = pole + arch - comb
        if parts:
            return M, gram, dict(pole=pole, arch=arch, comb=comb)
        return M, gram

def sector_basis(A, N, par, kind='neumann'):
    """frequencies of the real sector basis. par 0 even (cos), 1 odd (sin).
       neumann: cos(m pi u/A) m=0..N-1 ; sin((m+1/2) pi u/A)
       dirichlet: cos((m+1/2) pi u/A) ; sin(m pi u /A) m>=1   (vanish at the edges)"""
    A = float(A)
    if kind == 'neumann':
        return [np.pi * m / A for m in range(N)] if par == 0 else [np.pi * (m + 0.5) / A for m in range(N)]
    return [np.pi * (m + 0.5) / A for m in range(N)] if par == 0 else [np.pi * (m + 1) / A for m in range(N)]

def real_sector(form, kap, par, parts=False):
    """real symmetric sector matrix for phi_m = cos(kap_m u) (par 0) or sin(kap_m u) (par 1)."""
    ks = []; idx = []
    for k in kap:
        if k == 0:
            idx.append([(len(ks), 1.0)]); ks.append(0.0)
        else:
            if par == 0:
                idx.append([(len(ks), 0.5), (len(ks) + 1, 0.5)])
            else:
                idx.append([(len(ks), 0.5 / 1j), (len(ks) + 1, -0.5 / 1j)])
            ks += [k, -k]
    T = np.zeros((len(ks), len(kap)), complex)
    for i, lst in enumerate(idx):
        for a, v in lst: T[a, i] = v
    res = form.complex_mats(ks, parts)
    M, G = res[0], res[1]
    Mr = T.T @ M @ np.conj(T); Gr = T.T @ G @ np.conj(T)
    assert np.max(np.abs(Mr.imag)) < 1e-8 * max(1, np.max(np.abs(Mr))), np.max(np.abs(Mr.imag))
    if parts:
        P = {k: (T.T @ v @ np.conj(T)).real for k, v in res[2].items()}
        return Mr.real, Gr.real, P
    return Mr.real, Gr.real

def gmin(M, G, vec=False):
    M = (M + M.T) / 2; G = (G + G.T) / 2
    L = np.linalg.cholesky(G); Li = np.linalg.inv(L)
    e, W = np.linalg.eigh(Li @ M @ Li.T)
    if vec:
        return e, Li.T @ W
    return e
