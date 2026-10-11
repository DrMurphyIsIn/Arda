"""De Bruijn-Newman heat flow of the zeros of H_t, truncated system + mean-field tail.

This is part of a bounded numerical SEARCH for an arithmetic Lyapunov functional along the
heat flow (see HEAT_FLOW_DIFFRACTION_2026-10-11.md).  It is not a proof of anything and it
is NOT an estimate of the de Bruijn-Newman constant.  conjecture1_proved = False.

Conventions
-----------
  Phi(u)  = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
  H_t(z)  = int_0^inf e^{t u^2} Phi(u) cos(z u) du,      H_0(z) = xi(1/2 + i z/2) / 8.
  d_t H_t = int u^2 e^{t u^2} Phi cos(zu) du = - d_z^2 H_t     (BACKWARD heat equation).

Zero dynamics.  If z_k(t) is a simple zero, H(z_k(t), t) = 0 gives
  dz_k/dt = - (d_t H)/(d_z H) = H''(z_k)/H'(z_k) = 2 sum_{j != k} 1/(z_k - z_j),
the sum running over ALL zeros (both signs, H_t is even), summed symmetrically.  This is the
Csordas-Smith-Varga / Rodgers-Tao normalisation (repulsion for t increasing).  In terms of the
positive zeros only:
  dz_k/dt = 1/z_k + 4 z_k sum_{j != k, j >= 1} 1/(z_k^2 - z_j^2).
In zeta ordinates gamma = z/2:  dgamma_k/dt = (1/2) sum_{j != k (signed)} 1/(gamma_k - gamma_j).

Gradient structure.  With E(z) = - sum_{j<k} log|z_j^2 - z_k^2| - (1/2) sum_k log(2 z_k)
(the log-gas energy of the symmetric configuration, reduced to positive zeros),
dz_k/dt = -2 dE/dz_k, so dE/dt = -(1/2) sum_k (dz_k/dt)^2 <= 0.

Tail (mean field).  The zeros beyond z_N are replaced by a continuum of density
  rho(w) = (1/4 pi) log(w / 4 pi)        (z-coordinates; = d/dZ of (Z/4pi) log(Z/4pi e))
on w >= Z_c = (z_N + z_{N+1})/2, together with its mirror image on w <= -Z_c.  Its force on a
discrete zero z < Z_c is
  f_tail(z) = 2 int_{Z_c}^inf rho(w) [1/(z - w') + 1/(z + w')] dw
            = -4 z int_{Z_c}^inf rho(w) / (w'^2 - z^2) dw,           w' = w - s(t).
The continuum itself is not static: the mean-field velocity of a density rho on all of R is
2 PV int rho(w)/(z-w) dw, and the Hilbert transform of log|w| is -(pi/2) sgn, so a log density
drifts RIGIDLY with velocity 2 (1/4pi)(-pi^2/2) = -pi/4 (z-units; -pi/8 in gamma).  Hence the
tail is translated, s(t) = pi t / 4.  (Consistency check: this is exactly the shift
N_t(Z) = N_0(Z) + (t/16) log(Z/4pi) of the zero-counting function under the flow, since
(pi/4) rho(Z) = (1/16) log(Z/4pi).)  The tail contributes the external potential
  V(z,t) = - int_{Z_c}^inf rho(w) log(1 - z^2/w'^2) dw,   f_tail = -2 dV/dz.
Its fluctuations (the arithmetic structure of the zeros beyond N) are NOT modelled; that is why
diffraction is measured only on the first N' < N zeros.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from numba import njit
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
SCRATCH = Path(os.environ.get(
    "HEATFLOW_SCRATCH",
    "/private/tmp/claude-0/-Users-peterwmurphy/d468a49a-41a3-402a-a634-199ecc771fa2/scratchpad/heatflow"))
FOURPI = 4.0 * math.pi


# ----------------------------------------------------------------------------- zeros
def load_zeta_zeros(n: int) -> np.ndarray:
    """First n zeta ordinates gamma_k (float64).  Source: research/zeros2000.json (cached
    island list) + zeros5001.txt in this directory (mpmath.zetazero, computed 2026-10-11)."""
    f5 = HERE / "zeros5001.txt"
    if f5.exists():
        g = np.loadtxt(f5)
        if len(g) >= n:
            return g[:n].copy()
    g = np.array([float(x) for x in json.loads((HERE.parent / "zeros2000.json").read_text())])
    if len(g) < n:
        raise ValueError(f"only {len(g)} cached zeros; need {n}")
    return g[:n]


def nbar_gamma(g, t=0.0):
    """Smooth zero count (gamma units) at time t: N_0 + (t/16) log(gamma/2pi)."""
    g = np.asarray(g, dtype=float)
    return g / (2 * np.pi) * np.log(g / (2 * np.pi * np.e)) + 7.0 / 8.0 + t / 16.0 * np.log(g / (2 * np.pi))


def nbar_inverse(x):
    x = np.atleast_1d(np.asarray(x, dtype=float))
    out = np.empty_like(x)
    for i, xi in enumerate(x):
        out[i] = brentq(lambda g: nbar_gamma(g) - xi, 7.0, 1e7, xtol=1e-13)
    return out


# ----------------------------------------------------------------------------- controls
def gue_unfolded(m_keep: int, seed: int) -> np.ndarray:
    """m_keep consecutive unfolded GUE eigenvalues (mean spacing 1), from the bulk of a
    Dumitriu-Edelman beta=2 tridiagonal matrix of size 2*m_keep."""
    from scipy.linalg import eigvalsh_tridiagonal
    rng = np.random.default_rng(seed)
    M = 2 * m_keep
    beta = 2
    d = rng.normal(0.0, math.sqrt(2.0), M) / math.sqrt(2.0)
    e = np.sqrt(rng.chisquare(beta * np.arange(M - 1, 0, -1))) / math.sqrt(2.0)
    lam = eigvalsh_tridiagonal(d, e)
    R = math.sqrt(2.0 * beta * M)  # semicircle radius: E tr H^2 = M + beta M(M-1)/2 ~ M R^2/4
    x = np.clip(lam / R, -1.0, 1.0)
    F = M * (0.5 + (x * np.sqrt(1 - x * x) + np.arcsin(x)) / np.pi)
    lo = (M - m_keep) // 2
    xs = F[lo:lo + m_keep]
    return xs - xs[0] + 0.5


def control_gammas(kind: str, n: int, seed: int) -> np.ndarray:
    """n points with the zeta zero density: x_k (mean spacing 1, starting near 1/2) mapped by
    N-bar^{-1}.  kind in {'gue','poisson'}."""
    if kind == "gue":
        xs = gue_unfolded(n, seed)
    elif kind == "poisson":
        rng = np.random.default_rng(seed)
        xs = np.sort(rng.uniform(0.0, n, n))
        xs = xs - xs[0] + 0.5
    else:
        raise ValueError(kind)
    return nbar_inverse(xs)


# ----------------------------------------------------------------------------- direct H_t
def H_direct(t, z, dps=32):
    import mpmath as mp
    mp.mp.dps = dps
    t = mp.mpf(t)
    z = mp.mpf(z)

    def phi(u):
        s = mp.mpf(0)
        for n in range(1, 9):
            s += (2 * mp.pi ** 2 * n ** 4 * mp.e ** (9 * u) - 3 * mp.pi * n ** 2 * mp.e ** (5 * u)) * \
                mp.e ** (-mp.pi * n ** 2 * mp.e ** (4 * u))
        return s

    pts = mp.linspace(0, mp.mpf("1.3"), 27)
    return mp.quad(lambda u: mp.e ** (t * u * u) * phi(u) * mp.cos(z * u), pts)


def xi_over_8(z, dps=32):
    import mpmath as mp
    mp.mp.dps = dps
    s = mp.mpf(1) / 2 + 1j * mp.mpf(z) / 2
    return (s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)) / 8


def direct_zero(t, z0, dps=32):
    import mpmath as mp
    mp.mp.dps = dps
    f = lambda z: H_direct(t, z, dps)
    # bracket then Illinois/anderson
    a, b = mp.mpf(z0) - mp.mpf("0.05"), mp.mpf(z0) + mp.mpf("0.05")
    fa, fb = f(a), f(b)
    k = 0
    while fa * fb > 0 and k < 6:
        a -= mp.mpf("0.1"); b += mp.mpf("0.1"); fa, fb = f(a), f(b); k += 1
    r = mp.findroot(f, (a, b), solver="anderson", tol=mp.mpf(10) ** (-24))
    return float(r)


# ----------------------------------------------------------------------------- ODE
@njit(cache=True)
def pair_velocity(z):
    """1/z_k + 4 z_k sum_{j != k} 1/(z_k^2 - z_j^2)   (discrete part of dz_k/dt)."""
    n = z.shape[0]
    acc = np.zeros(n)
    z2 = z * z
    for k in range(n):
        for j in range(k + 1, n):
            inv = 1.0 / (z2[k] - z2[j])
            acc[k] += inv
            acc[j] -= inv
    out = np.empty(n)
    for k in range(n):
        out[k] = 1.0 / z[k] + 4.0 * z[k] * acc[k]
    return out


@njit(cache=True)
def pair_velocity_complex(z):
    """Same, for complex z (used only for the post-collision illustration)."""
    n = z.shape[0]
    acc = np.zeros(n, dtype=np.complex128)
    z2 = z * z
    for k in range(n):
        for j in range(k + 1, n):
            inv = 1.0 / (z2[k] - z2[j])
            acc[k] += inv
            acc[j] -= inv
    out = np.empty(n, dtype=np.complex128)
    for k in range(n):
        out[k] = 1.0 / z[k] + 4.0 * z[k] * acc[k]
    return out


@njit(cache=True)
def log_gas_energy(z):
    n = z.shape[0]
    e = 0.0
    z2 = z * z
    for k in range(n):
        e -= 0.5 * math.log(2.0 * z[k])
        for j in range(k + 1, n):
            e -= math.log(abs(z2[k] - z2[j]))
    return e


class Tail:
    """Mean-field continuum beyond Z_c, rigidly translated by s(t) = pi t / 4."""

    def __init__(self, Zc: float, drift: bool = True, enabled: bool = True):
        self.Zc = Zc
        self.drift = drift
        self.enabled = enabled
        # panels on y = w - Zc: [0,0.5],[0.5,1],[1,2],... doubling up to W - Zc
        self.W = 400.0 * Zc
        edges = [0.0, 0.5]
        while edges[-1] < self.W - Zc:
            edges.append(min(edges[-1] * 2, self.W - Zc))
        xg, wg = np.polynomial.legendre.leggauss(20)
        ws, wts = [], []
        for a, b in zip(edges[:-1], edges[1:]):
            ws.append(Zc + a + (b - a) * (xg + 1) / 2)
            wts.append(wg * (b - a) / 2)
        self.w = np.concatenate(ws)
        self.wt = np.concatenate(wts) * np.log(self.w / FOURPI) / FOURPI  # rho(w) * weight

    def shift(self, t):
        return math.pi * t / 4.0 if self.drift else 0.0

    def _far(self, p):
        W, a = self.W, FOURPI
        # int_W^inf log(w/a)/(4pi) w^{-p} dw
        return W ** (1 - p) * (math.log(W / a) / (p - 1) + 1.0 / (p - 1) ** 2) / FOURPI

    def force(self, z, t):
        if not self.enabled:
            return np.zeros_like(z)
        wp = self.w - self.shift(t)
        near = -4.0 * z * ((self.wt[None, :] / (wp[None, :] ** 2 - z[:, None] ** 2)).sum(axis=1))
        far = -4.0 * z * (self._far(2) + z ** 2 * self._far(4) + z ** 4 * self._far(6))
        return near + far

    def potential(self, z, t):
        if not self.enabled:
            return np.zeros_like(z)
        wp = self.w - self.shift(t)
        near = -(self.wt[None, :] * np.log1p(-(z[:, None] / wp[None, :]) ** 2)).sum(axis=1)
        far = z ** 2 * self._far(2) + 0.5 * z ** 4 * self._far(4)
        return near + far


def velocity(z, t, tail: Tail):
    """dz_k/dt = 1/z_k + 4 z_k sum_{j!=k} 1/(z_k^2-z_j^2) + f_tail(z_k)."""
    v = pair_velocity(z)
    if tail.enabled:
        v = v + tail.force(z, t)
    return v


def total_energy(z, t, tail: Tail):
    return log_gas_energy(z) + (tail.potential(z, t).sum() if tail.enabled else 0.0)


def integrate(z0, t_eval, tail: Tail, rtol=1e-9, atol=1e-9, method="RK45", events=None):
    fun = lambda t, z: velocity(z, t, tail)
    t_span = (float(t_eval[0]), float(t_eval[-1]))
    t0 = time.time()
    sol = solve_ivp(fun, t_span, z0, method=method, t_eval=t_eval, rtol=rtol, atol=atol,
                    events=events)
    sol.wall = time.time() - t0
    return sol


def setup_system(gammas_np1: np.ndarray, tail_on=True, drift=True):
    """gammas_np1: N+1 ordinates; the first N are evolved, the (N+1)-st only fixes Z_c."""
    z = 2.0 * gammas_np1
    Zc = 0.5 * (z[-2] + z[-1])
    return z[:-1].copy(), Tail(Zc, drift=drift, enabled=tail_on)


T_GRID = np.unique(np.concatenate([np.linspace(0.0, 1.0, 41), [0.005, 0.01, 0.0125]]))


def spacing_stats(z, t, lo, hi):
    """Unfolded nearest-neighbour spacing statistics of zeros lo..hi-1 (0-based)."""
    g = z[lo:hi] / 2.0
    x = nbar_gamma(g, t)
    s = np.diff(x)
    return dict(mean=float(s.mean()), var=float(s.var()), min=float(s.min()),
                p_small=float((s < 0.25).mean()))


# ----------------------------------------------------------------------------- validation
def _dz_job(a):
    return direct_zero(a[0], a[1])


def validate(N=5000, out=None):
    lines = []
    P = lambda *a: (print(*a), lines.append(" ".join(str(x) for x in a)))
    import mpmath as mp
    P("== check H_0(z) = xi(1/2+iz/2)/8 ==")
    for zz in (0.0, 10.0, 28.0):
        h = H_direct(0, zz)
        x = xi_over_8(zz)
        P(f"z={zz:5.1f}  H_0={mp.nstr(h, 18)}  xi/8={mp.nstr(mp.re(x), 18)}  rel.diff={mp.nstr(abs(h - mp.re(x)) / abs(h), 3)}")
    g = load_zeta_zeros(N + 1)
    z0, tail = setup_system(g)
    P(f"N={N}, Z_c={tail.Zc:.4f}, tail drift s(t)=pi t/4")
    # gradient check of the energy, coordinate-local (the global sum is ~1e8: FD cancels)
    v = velocity(z0, 0.0, tail)

    def e_local(zz, k):
        others = np.delete(z0, k)
        return (-np.log(np.abs(zz ** 2 - others ** 2)).sum() - 0.5 * math.log(2 * zz)
                + tail.potential(np.array([zz]), 0.0)[0])

    for k in (0, 5, N // 2, N - 1):
        h = 1e-5
        dE = (e_local(z0[k] + h, k) - e_local(z0[k] - h, k)) / (2 * h)
        P(f"gradient check k={k}: v_k={v[k]:.10f}  -2 dE/dz_k={-2 * dE:.10f}")
    # ODE vs direct
    tv = [0.0, 0.01, 0.05, 0.2, 1.0]
    sol = integrate(z0, np.array(tv), tail, rtol=1e-11, atol=1e-11)
    P(f"ODE integration ({sol.nfev} rhs evals, {sol.wall:.1f}s)")
    sol_nt = integrate(z0, np.array(tv), Tail(tail.Zc, enabled=False), rtol=1e-11, atol=1e-11)
    sol_nd = integrate(z0, np.array(tv), Tail(tail.Zc, drift=False), rtol=1e-11, atol=1e-11)
    P("k  t      z_direct           z_ODE(tail+drift)  err        err(no tail)  err(static tail)  dz/dt(0)")
    rows = []
    from concurrent.futures import ProcessPoolExecutor
    jobs = [(t, float(sol.y[k, i])) for k in range(8) for i, t in enumerate(tv)]
    with ProcessPoolExecutor(8) as ex:
        dz = list(ex.map(_dz_job, jobs))
    dz = {(k, i): dz[k * len(tv) + i] for k in range(8) for i in range(len(tv))}
    for k in range(8):
        for i, t in enumerate(tv):
            zd = dz[(k, i)]
            e1 = sol.y[k, i] - zd
            e2 = sol_nt.y[k, i] - zd
            e3 = sol_nd.y[k, i] - zd
            P(f"{k + 1}  {t:<5}  {zd:.12f}  {sol.y[k, i]:.12f}  {e1:+.2e}  {e2:+.2e}     {e3:+.2e}        {v[k]:+.6f}")
            rows.append((k + 1, t, zd, sol.y[k, i], e1, e2, e3))
    np.savetxt(HERE / "validation_ode_vs_direct.csv", np.array(rows), delimiter=",",
               header="k,t,z_direct,z_ode_tail_drift,err_tail_drift,err_no_tail,err_static_tail",
               fmt="%.14g", comments="")
    if out:
        Path(out).write_text("\n".join(lines) + "\n")
    return rows


# ----------------------------------------------------------------------------- runs
def run_forward(label, gammas_np1, t_grid=T_GRID, rtol=1e-11, atol=1e-11, drift=True):
    z0, tail = setup_system(gammas_np1, drift=drift)
    sol = integrate(z0, t_grid, tail, rtol=rtol, atol=atol)
    if not sol.success:
        raise RuntimeError(sol.message)
    Z = sol.y.T  # (nt, N)
    E = np.array([total_energy(Z[i], t, tail) for i, t in enumerate(t_grid)])
    D = np.array([float((velocity(Z[i], t, tail) ** 2).sum()) for i, t in enumerate(t_grid)])
    np.savez(SCRATCH / f"traj_{label}.npz", t=t_grid, Z=Z, E=E, D=D, Zc=tail.Zc)
    print(f"[{label}] N={len(z0)} nfev={sol.nfev} wall={sol.wall:.1f}s")
    return t_grid, Z, E, D


def main():
    SCRATCH.mkdir(parents=True, exist_ok=True)
    N = int(os.environ.get("HF_N", "5000"))
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("validate", "all"):
        validate(N, out=HERE / "validation_ode_vs_direct.txt")
    if what in ("zeta", "all"):
        g = load_zeta_zeros(N + 1)
        t, Z, E, D = run_forward("zeta", g)
        rows = []
        for i, tt in enumerate(t):
            st = spacing_stats(Z[i], tt, 100, 3000)
            rows.append((tt, st["mean"], st["var"], st["min"], st["p_small"], E[i], D[i]))
        np.savetxt(HERE / "spacing_stats_zeta.csv", np.array(rows), delimiter=",", fmt="%.10g",
                   header="t,mean_unfolded_spacing,var_unfolded_spacing,min_spacing,frac_spacing_lt_0.25,energy_total,dissipation_sum_v2",
                   comments="")
    if what in ("zeta_static", "all"):
        # autonomous variant (tail frozen, no drift): an exact gradient flow, so E must decrease;
        # used only for the energy sanity check (a).  Accuracy vs direct H_t: see validation.
        g = load_zeta_zeros(N + 1)
        t, Z, E, D = run_forward("zeta_static", g, drift=False)
        d = np.diff(E)
        print(f"[zeta_static] energy increments: max {d.max():.4g} (must be < 0), violations {(d > 0).sum()}")
    if what in ("controls", "all"):
        for kind in ("gue", "poisson"):
            for seed in (1, 2, 3):
                g = control_gammas(kind, N + 1, seed)
                t, Z, E, D = run_forward(f"{kind}{seed}", g)
                rows = []
                for i, tt in enumerate(t):
                    st = spacing_stats(Z[i], tt, 100, 3000)
                    rows.append((tt, st["mean"], st["var"], st["min"], st["p_small"], E[i], D[i]))
                np.savetxt(HERE / f"spacing_stats_{kind}{seed}.csv", np.array(rows), delimiter=",",
                           fmt="%.10g",
                           header="t,mean_unfolded_spacing,var_unfolded_spacing,min_spacing,frac_spacing_lt_0.25,energy_total,dissipation_sum_v2",
                           comments="")


if __name__ == "__main__":
    main()
