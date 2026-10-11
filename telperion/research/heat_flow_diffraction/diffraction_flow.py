"""Diffraction of the zero comb along the de Bruijn-Newman heat flow (Dyson's quasicrystal view).

A bounded numerical SEARCH for an arithmetic Lyapunov functional.  Nothing here is progress on
RH and nothing here estimates the de Bruijn-Newman constant.  conjecture1_proved = False.

Objects (gamma = z/2 ordinates of the evolved zeros, weights attached to particles):
  A_t(u)  = sum_k w_k exp(i gamma_k(t) u)          (complex finite-height Bragg amplitude)
  F_t(u)  = Re A_t(u) = sum_k w_k cos(gamma_k(t) u) (the island's F(u), dh_diffraction.py)
  sharp:  w_k = 1 for k <= N'                      smooth: w_k = cos^2(pi gamma_k(0) / 2T)
  T = (gamma_{N'} + gamma_{N'+1})/2.

Explicit formula (Landau):  sum_{0<gamma<=T} w(gamma/T) x^{i gamma}
     ~ -(1/2pi) int_0^T w(gamma/T) dgamma * Lambda(x)/sqrt(x) + smooth,
so the effective von Mangoldt weight read off the diffraction is
  LamHat_t(n) := -2 pi sqrt(n) (A_t(log n) - bg(log n)) / (T <w>),   <w> = int_0^1 w.
At t = 0, LamHat(p^m) ~ log p and LamHat(n) ~ 0 otherwise.

Exact identity (task 4; S(u) = sum over the SIGNED configuration {+-gamma_k} of cos(gamma u)):
  d/dt S_t(u) = (u^2/4) S_t(u) - (u/4) int_0^u S_t(v) S_t(u-v) dv,
valid for any finite symmetric configuration moving by dgamma_k/dt = (1/2) sum_{j!=k} 1/(gamma_k-gamma_j).
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import math
import sys
from pathlib import Path

import numpy as np
from numba import njit
from scipy.special import psi as digamma

sys.path.insert(0, str(Path(__file__).resolve().parent))
import heat_flow_ode as hf  # noqa: E402

HERE = hf.HERE
SCRATCH = hf.SCRATCH
U_MAX = 5.0
DU = 2e-4
U_GRID = np.arange(0.0, U_MAX + DU / 2, DU)
NS = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
NPRIME_MAIN = 3000
NPRIME_LIST = [500, 1000, 2000, 3000]
CONTROLS = ["gue1", "gue2", "gue3", "poisson1", "poisson2", "poisson3"]
OUT_LINES: list[str] = []


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT_LINES.append(s)


# ----------------------------------------------------------------------------- arithmetic
def mangoldt(n):
    if n < 2:
        return 0.0
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0


def lambda_D(a):
    """Lambda_D(n), n=0..len(a)-1, for D = sum a_n n^{-s} (a_1 = 1): -D'/D = sum Lambda_D n^{-s}."""
    nmax = len(a) - 1
    L = np.zeros(nmax + 1, dtype=complex)
    for n in range(2, nmax + 1):
        s = a[n] * math.log(n)
        d = 2
        while d * d <= n:
            if n % d == 0:
                s -= a[d] * L[n // d]
                if d != n // d:
                    s -= a[n // d] * L[d]
            d += 1
        L[n] = s
    return L


def lambda_b(t, nmax=200):
    """Lambda for b_n = exp((t/4) log^2 n) (the heat-flow Dirichlet multiplier)."""
    a = np.array([0.0] + [math.exp(t / 4 * math.log(n) ** 2) for n in range(1, nmax + 1)], dtype=complex)
    return lambda_D(a)


def lam_conv(nmax=200):
    L = np.array([mangoldt(n) for n in range(nmax + 1)])
    C = np.zeros(nmax + 1)
    for m in range(2, nmax + 1):
        for k in range(2, nmax // m + 1):
            C[m * k] += L[m] * L[k]
    return L, C


# ----------------------------------------------------------------------------- kernels
@njit(cache=True)
def amp_at(gam, w, us):
    out = np.zeros(us.shape[0], dtype=np.complex128)
    for i in range(us.shape[0]):
        u = us[i]
        s = 0j
        for k in range(gam.shape[0]):
            s += w[k] * complex(math.cos(gam[k] * u), math.sin(gam[k] * u))
        out[i] = s
    return out


@njit(cache=True)
def f_grid(gam, w, du, m):
    """F(u_j) = sum_k w_k cos(gam_k u_j), u_j = j du, j < m, via rotation recurrence
    (re-synchronised every 512 steps)."""
    out = np.zeros(m)
    for k in range(gam.shape[0]):
        rot = complex(math.cos(gam[k] * du), math.sin(gam[k] * du))
        for j0 in range(0, m, 512):
            c = complex(math.cos(gam[k] * du * j0), math.sin(gam[k] * du * j0))
            for j in range(j0, min(j0 + 512, m)):
                out[j] += w[k] * c.real
                c *= rot
    return out


@njit(cache=True)
def pair_sin_sum(g, u):
    """sum over the signed set {+-g_k}: sum_{a != b} sin(x_a u)/(x_a - x_b)."""
    n = g.shape[0]
    x = np.empty(2 * n)
    x[:n] = g
    x[n:] = -g
    tot = 0.0
    for a in range(2 * n):
        sa = math.sin(x[a] * u)
        acc = 0.0
        for b in range(2 * n):
            if b != a:
                acc += 1.0 / (x[a] - x[b])
        tot += sa * acc
    return tot


# ----------------------------------------------------------------------------- setup
def load(label):
    d = np.load(SCRATCH / f"traj_{label}.npz")
    return d["t"], d["Z"] / 2.0, d["E"], d["D"], float(d["Zc"])


def weights(g0, nprime, kind):
    T = 0.5 * (g0[nprime - 1] + g0[nprime])
    w = np.zeros(len(g0))
    if kind == "sharp":
        w[:nprime] = 1.0
        wbar = 1.0
    else:
        x = g0[:nprime] / T
        w[:nprime] = np.cos(np.pi * x / 2) ** 2
        wbar = 0.5
    return w, T, wbar


def wfun(x, kind):
    x = np.asarray(x)
    if kind == "sharp":
        return (x <= 1).astype(float)
    return np.where(x <= 1, np.cos(np.pi * x / 2) ** 2, 0.0)


def smooth_background(us, T, kind, dr=0.02):
    """F_sm(u) = int_0^inf w(r/T) cos(ru) theta'(r)/pi dr + cosh(u/2) (pole term, local approx)."""
    r = np.arange(0.0, T * 1.0 + dr / 2, dr)
    th = 0.5 * np.real(digamma(0.25 + 0.5j * r)) - 0.5 * math.log(math.pi)
    g = wfun(r / T, kind) * th / math.pi * dr
    g[0] *= 0.5
    out = np.empty(len(us))
    for i0 in range(0, len(us), 64):
        uu = us[i0:i0 + 64]
        out[i0:i0 + 64] = np.cos(np.outer(uu, r)) @ g
    return out + np.cosh(np.asarray(us) / 2)


def K_T(y, T, kind, dr=0.02):
    r = np.arange(0.0, T + dr / 2, dr)
    g = wfun(r / T, kind) * dr / math.pi
    g[0] *= 0.5
    return np.cos(np.outer(np.atleast_1d(y), r)) @ g


_FFT_M = 2 ** 21
_FFT_DR = 2 * math.pi / (DU * _FFT_M)


def _cos_transform_grid(g):
    """sum_j g_j cos(r_j u_m) on u_m = m DU (m < len(U_GRID)), r_j = j _FFT_DR."""
    buf = np.zeros(_FFT_M)
    buf[:len(g)] = g
    return np.real(np.fft.fft(buf))[:len(U_GRID)]


def smooth_background_grid(T, kind):
    r = np.arange(0.0, T * 1.0 + _FFT_DR / 2, _FFT_DR)
    th = 0.5 * np.real(digamma(0.25 + 0.5j * r)) - 0.5 * math.log(math.pi)
    g = wfun(r / T, kind) * th / math.pi * _FFT_DR
    g[0] *= 0.5
    return _cos_transform_grid(g) + np.cosh(U_GRID / 2)


def K_T_grid(T, kind):
    r = np.arange(0.0, T + _FFT_DR / 2, _FFT_DR)
    g = wfun(r / T, kind) * _FFT_DR / math.pi
    g[0] *= 0.5
    buf = np.zeros(_FFT_M)
    buf[:len(g)] = g
    K = np.real(np.fft.fft(buf))
    y = np.arange(_FFT_M) * DU
    return y[:_FFT_M // 2], K[:_FFT_M // 2]


def ef_peak_curve_grid(T, kind, nmax=400):
    """-(1/2) sum_{n<=nmax} Lambda(n)/sqrt(n) [K_T(u - log n) + K_T(u + log n)] on U_GRID."""
    y, K = K_T_grid(T, kind)
    tot = np.zeros(len(U_GRID))
    for n in range(2, nmax + 1):
        L = mangoldt(n)
        if L == 0:
            continue
        ln = math.log(n)
        tot += -0.5 * L / math.sqrt(n) * (np.interp(np.abs(U_GRID - ln), y, K) + np.interp(U_GRID + ln, y, K))
    return tot


def ef_peak_at(us, T, kind, nmax=400):
    y, K = K_T_grid(T, kind)
    tot = np.zeros(len(us))
    for n in range(2, nmax + 1):
        L = mangoldt(n)
        if L == 0:
            continue
        ln = math.log(n)
        tot += -0.5 * L / math.sqrt(n) * (np.interp(np.abs(us - ln), y, K) + np.interp(us + ln, y, K))
    return tot


# ----------------------------------------------------------------------------- task 2/3
def window_integral(T, kind, f, g1=14.134725141734693):
    """int_0^T w(gamma/T) f(gamma) dgamma; on [0, g1] w = 1 to O((g1/T)^2) and f is integrated by
    adaptive quadrature (it may have an integrable singularity at 0); numeric trapezoid beyond."""
    from scipy.integrate import quad
    head = quad(f, 0.0, g1, limit=200)[0]
    gg = np.linspace(g1, T, 40001)
    return head + np.trapz(wfun(gg / T, kind) * f(gg), gg)


def phonon_rate(u, gamma):
    """Linear relaxation rate of a density mode exp(i gamma u) in the log-gas crystal of local
    density rho = (1/2pi) log(gamma/2pi):  r = (u/4) (2 pi rho - u) = (u/4)(log(gamma/2pi) - u)."""
    return 0.25 * u * (np.log(gamma / (2 * np.pi)) - u)


def lamhat(A, n, T, wbar, bg):
    return -2 * math.pi * math.sqrt(n) * (A - bg) / (T * wbar)


def pred_lamhat(t, n, T, kind, g_lo=None):
    """Heuristic (Polymath15-type effective Dirichlet series) prediction for LamHat_t(n):
    Lambda_b(n;t) n^{-i pi t/8} <(gamma/2pi)^{-(t/4) log n}>_w, window average over heights
    gamma in [0, T] (Landau's formula integrates heights from 0)."""
    Lb = lambda_b(t, max(n, 2))[n]
    a = (t / 4) * math.log(n)
    fac = window_integral(T, kind, lambda g: (np.asarray(g) / (2 * np.pi)) ** (-a)) / \
        (T * (0.5 if kind != "sharp" else 1.0))
    return Lb * n ** (-1j * math.pi * t / 8) * fac


def lattice_amp(gam_t, w, t):
    x = hf.nbar_gamma(gam_t, t)
    return abs(np.sum(w * np.exp(2j * np.pi * x))) / w.sum()


def prime_powers(umax):
    return [n for n in range(2, int(math.exp(umax)) + 1) if mangoldt(n) > 0]


def analyse(label, nprime=NPRIME_MAIN, kind="smooth", full=True, tsel=None):
    t, G, E, D, Zc = load(label)
    if tsel is not None:
        t, G, E, D = t[tsel], G[tsel], E[tsel], D[tsel]
    g0 = G[0]
    w, T, wbar = weights(g0, nprime, kind)
    sel = w > 0
    us_n = np.log(np.array(NS, dtype=float))
    bg_n = smooth_background(us_n, T, kind)
    res = dict(t=t, T=T, wbar=wbar, E=E, D=D)
    res["A"] = np.array([amp_at(G[i][sel], w[sel], us_n) for i in range(len(t))])
    res["LamHat"] = np.array([[lamhat(res["A"][i, j], n, T, wbar, bg_n[j]) for j, n in enumerate(NS)]
                              for i in range(len(t))])
    res["latt"] = np.array([lattice_amp(G[i][sel], w[sel], t[i]) for i in range(len(t))])
    pp = prime_powers(U_MAX)
    App = np.array([amp_at(G[i][sel], w[sel], np.log(np.array(pp, float))) for i in range(len(t))])
    res["B"] = (np.abs(App.real) ** 2).sum(axis=1) / nprime ** 2      # (b) with F = Re A
    res["Bc"] = (np.abs(App) ** 2).sum(axis=1) / nprime ** 2          # (b') complex modulus
    if full:
        m = len(U_GRID)
        i0 = int(round(0.3 / DU))
        Fg = np.array([f_grid(G[i][sel], w[sel], DU, m) for i in range(len(t))])
        res["Fgrid"] = Fg
        # (c) distances
        uu = U_GRID[i0:]
        F_ef = (smooth_background_grid(T, kind) + ef_peak_curve_grid(T, kind))[i0:]
        res["F_ef"] = F_ef
        nrm = lambda a: math.sqrt(np.trapz(a * a, uu))
        res["d_ef"] = np.array([nrm(Fg[i, i0:] - F_ef) for i in range(len(t))]) / nrm(F_ef)
        d_l = []
        gl0 = hf.nbar_inverse(np.arange(1, nprime + 1) - 0.5)
        for i, tt in enumerate(t):
            # lattice at time t: Nbar_t^{-1}(k - 1/2) = Nbar_0^{-1}(k - 1/2) - pi t / 8 (uniform drift)
            Fl = f_grid(gl0 - np.pi * tt / 8, w[:nprime], DU, m)[i0:]
            d_l.append(nrm(Fg[i, i0:] - Fl) / nrm(Fl))
        res["d_latt"] = np.array(d_l)
        # (d) pure-point fraction: energy in the top-K windows of width 8 pi / T, K = #prime powers
        wlen = max(4, int(round(8 * math.pi / T / DU)))
        K = len(pp)
        ppf = []
        for i in range(len(t)):
            e = Fg[i, i0:] ** 2
            nw = len(e) // wlen
            we = e[:nw * wlen].reshape(nw, wlen).sum(axis=1)
            ppf.append(np.sort(we)[-K:].sum() / we.sum())
        res["ppf"] = np.array(ppf)
    return res


def monotone_report(name, y, t):
    d = np.diff(y)
    s = np.sign(d)
    nz = s[s != 0]
    dom = 1 if (nz > 0).sum() > (nz < 0).sum() else -1
    viol = int((nz == -dom).sum())
    return f"{name:28s} {('increasing' if dom > 0 else 'decreasing'):10s} violations {viol:2d}/{len(d)}  " \
           f"y(0)={y[0]:.6g} y(1)={y[-1]:.6g}"


# ----------------------------------------------------------------------------- task 4
def identity_check(nfin=1000, us=(0.4, 0.693147, 1.0986, 1.6094, 2.0, 2.3979)):
    """Exact identity on the finite symmetric configuration of the first nfin zeta zeros (no tail):
    LHS: sum_{a!=b} sin(x_a u)/(x_a-x_b)  (pair sum)
    RHS: (1/2)[ int_0^u S(v) S(u-v) dv - u S(u) ],   S(v) = sum_a cos(x_a v) = 2 sum_k cos(g_k v)."""
    g = hf.load_zeta_zeros(nfin)
    say(f"\n== Task 4: exact pair-sum / autoconvolution identity, finite configuration N={nfin} (signed 2N points) ==")
    xg, wg = np.polynomial.legendre.leggauss(40)
    rows = []
    for u in us:
        lhs = pair_sin_sum(g, u)
        npan = int(u * g[-1] / 2) + 50
        edges = np.linspace(0, u, npan + 1)
        v = ((edges[:-1, None] + edges[1:, None]) / 2 + (edges[1:, None] - edges[:-1, None]) / 2 * xg[None, :]).ravel()
        wv = ((edges[1:, None] - edges[:-1, None]) / 2 * wg[None, :]).ravel()
        Sv = np.zeros(len(v)); Suv = np.zeros(len(v))
        for c0 in range(0, len(v), 20000):
            Sv[c0:c0 + 20000] = 2 * np.cos(np.outer(v[c0:c0 + 20000], g)).sum(axis=1)
            Suv[c0:c0 + 20000] = 2 * np.cos(np.outer(u - v[c0:c0 + 20000], g)).sum(axis=1)
        conv = float((wv * Sv * Suv).sum())
        Su = 2 * np.cos(u * g).sum()
        rhs = 0.5 * (conv - u * Su)
        say(f"u={u:.6f}  pair-sum LHS={lhs:+.10e}  convolution RHS={rhs:+.10e}  rel.diff={abs(lhs - rhs) / max(abs(lhs), 1e-300):.2e}")
        rows.append((u, lhs, rhs))
    np.savetxt(HERE / "task4_identity_check.csv", np.array(rows), delimiter=",", fmt="%.14g",
               header="u,pair_sum_lhs,autoconvolution_rhs", comments="")


def derivative_at_zero(label, nprime, kind, gpre=None):
    """Measured d/dt LamHat_t(n) at t=0 from the exact ODE velocities (with tail) vs the
    arithmetic prediction  (1/4)[log^2 n Lambda(n) + log n (Lambda*Lambda)(n)]
                          - (1/4) log n Lambda(n) [<log(gamma/2pi)>_w + i pi/2]."""
    t, G, E, D, Zc = load(label)
    g0 = G[0]
    vz = hf.velocity(2 * g0, 0.0, hf.Tail(Zc))
    gd = vz / 2.0
    w, T, wbar = weights(g0, nprime, kind)
    sel = w > 0
    out = []
    L, C = lam_conv(200)
    mlog = window_integral(T, kind, lambda g: np.log(np.asarray(g) / (2 * np.pi))) / (T * wbar)
    norm_int = 1.0
    for n in NS:
        u = math.log(n)
        dA = 1j * u * np.sum(w[sel] * np.exp(1j * g0[sel] * u) * gd[sel])
        meas = -2 * math.pi * math.sqrt(n) * dA / (T * wbar)
        pred = norm_int * (0.25 * (u * u * L[n] + u * C[n]) - 0.25 * u * L[n] * (mlog + 1j * math.pi / 2))
        out.append((n, meas, pred))
    return out, mlog


# ----------------------------------------------------------------------------- task 6
def backward_and_offline():
    say("\n== Task 6: backward flow (qualitative; truncated system; NOT a bound on anything) ==")
    g = hf.load_zeta_zeros(5001)
    z0, tail = hf.setup_system(g)
    gaps = np.diff(z0)
    k = int(np.argmin(gaps))
    say(f"closest pair among the first 5000 (z-units): k={k + 1},{k + 2}  gamma={z0[k] / 2:.6f},{z0[k + 1] / 2:.6f}  gap_gamma={gaps[k] / 2:.6f}")
    thr = 1e-3

    def ev(t, z):
        return np.min(np.diff(z)) - thr
    ev.terminal = True
    t_eval = -np.linspace(0, 0.05, 2001)
    sol = hf.integrate(z0, t_eval, tail, rtol=1e-12, atol=1e-13, events=ev)
    tc = sol.t_events[0][0] if len(sol.t_events[0]) else None
    zz = sol.y_events[0][0] if tc is not None else sol.y[:, -1]
    kk = int(np.argmin(np.diff(zz)))
    say(f"first near-collision (z-gap < {thr}) of the TRUNCATED system: pair k={kk + 1},{kk + 2} at gamma~{zz[kk] / 2:.4f};"
        f" |t| at the event = {abs(tc) if tc is not None else float('nan'):.3e}  [artifact of the truncated model; not reported as, and is not, a bound on Lambda]")
    w, T, wbar = weights(g[:-1], NPRIME_MAIN, "smooth")
    sel = w > 0
    us = np.log(np.array([2, 3, 5, 7, 11], float))
    A0 = amp_at(z0[sel] / 2, w[sel], us)
    Ac = amp_at(zz[sel] / 2, w[sel], us)
    rows = []
    for j, p in enumerate([2, 3, 5, 7, 11]):
        say(f"  F(log {p:2d}): t=0 {A0[j].real:+.4f}   just before the event {Ac[j].real:+.4f}   rel.change {abs(Ac[j].real - A0[j].real) / abs(A0[j].real):.2e}")
        rows.append((p, A0[j].real, Ac[j].real))
    say("  colliding pair's own contribution 2cos(gamma u)cos(...)-type term is O(1) out of F ~ O(T): invisible at log p.")
    # complex continuation: near a collision the pair separation obeys d(Delta^2)/dt ~ 8 (z-units),
    # so past the collision Delta = i sqrt(8 |t - t_c|): an off-line pair gamma0 +- i delta, delta = sqrt(2|t-t_c|)/2.
    say("\n== Off-line signature (hand-constructed complex pair; illustration of what RH-failure looks like in F) ==")
    say("A pair of H-zeros z = x +- i y corresponds to zeta zeros 1/2 +- y/2 + i x/2, i.e. gamma = x/2, delta = y/2;")
    say("its contribution to F is cos((x+iy)u/2) + cos((x-iy)u/2) = 2 cosh(delta u) cos(gamma u)  (island convention).")
    g0 = z0[kk] / 4 + z0[kk + 1] / 4
    off_rows = []
    for delta in (0.01, 0.05, 0.2, 0.5):
        for u in (math.log(2), math.log(11), 5.0, 10.0, 20.0):
            on = 2 * math.cos(g0 * u)
            off = 2 * math.cosh(delta * u) * math.cos(g0 * u)
            off_rows.append((delta, u, on, off, off - on, math.cosh(delta * u) - 1))
    for delta in (0.01, 0.05, 0.2, 0.5):
        say(f"  delta={delta:<5} excess envelope 2(cosh(delta u)-1): u=log2 {2 * (math.cosh(delta * math.log(2)) - 1):.2e}  "
            f"u=5 {2 * (math.cosh(delta * 5) - 1):.2e}  u=20 {2 * (math.cosh(delta * 20) - 1):.2e}")
    np.savetxt(HERE / "task6_offline_signature.csv", np.array(off_rows), delimiter=",", fmt="%.10g",
               header="delta,u,on_line_pair_2cos,off_line_pair_2cosh_cos,difference,cosh_minus_1", comments="")
    # follow the complex pair a little along the complex ODE to show delta grows like sqrt
    zc = zz.astype(complex)
    mid = 0.5 * (zc[kk] + zc[kk + 1])
    tau = 1e-4
    zc[kk] = mid - 1j * math.sqrt(8 * tau) / 2
    zc[kk + 1] = mid + 1j * math.sqrt(8 * tau) / 2
    say(f"  complex continuation (z-units): seeded pair at {mid.real / 2:.5f} +- i {math.sqrt(8 * tau) / 4:.5f} (gamma units)")
    dt = -2e-6
    tt = 0.0
    trail = []
    for step in range(500):
        v = hf.pair_velocity_complex(zc)
        zc = zc + dt * v
        tt += dt
        if step % 100 == 99:
            trail.append((tt, abs(zc[kk].imag) / 2))
    for a, b in trail:
        say(f"    further backward time {abs(a):.1e}: delta = {b:.5f}")
    return rows


# ----------------------------------------------------------------------------- main
def main():
    say("heat-flow diffraction experiment, 2026-10-11.  SEARCH, not proof.  conjecture1_proved = False")
    L, C = lam_conv(200)
    # ---- t = 0 explicit-formula check
    say("\n== t=0: explicit-formula (Landau) check of the Bragg amplitudes, zeta, N'=3000 ==")
    for kind in ("smooth", "sharp"):
        t, G, *_ = load("zeta")
        w, T, wbar = weights(G[0], NPRIME_MAIN, kind)
        us = np.log(np.array(NS, float))
        A = amp_at(G[0][w > 0], w[w > 0], us)
        bg = smooth_background(us, T, kind)
        pk = ef_peak_at(us, T, kind)
        say(f"[{kind}] T={T:.3f} <w>={wbar}  peak scale T<w>/2pi={T * wbar / 2 / math.pi:.3f}")
        say("   n   F_0(log n)      EF prediction   (bg+peaks)   LamHat_0(n)   Lambda(n)")
        for j, n in enumerate(NS):
            say(f"  {n:2d}  {A[j].real:+12.4f}  {bg[j] + pk[j]:+12.4f}            {lamhat(A[j], n, T, wbar, bg[j]).real:+.4f}      {L[n]:.4f}")
    # ---- main analysis
    R = {}
    for kind in ("smooth", "sharp"):
        R[("zeta", kind)] = analyse("zeta", NPRIME_MAIN, kind, full=True)
    for c in CONTROLS:
        R[(c, "smooth")] = analyse(c, NPRIME_MAIN, "smooth", full=True)
    t = R[("zeta", "smooth")]["t"]
    # ---- H1/H2 tables
    for kind in ("smooth", "sharp"):
        r = R[("zeta", kind)]
        hdr = "t," + ",".join(f"ReLamHat_{n},ImLamHat_{n}" for n in NS)
        arr = np.column_stack([t] + [np.column_stack([r["LamHat"][:, j].real, r["LamHat"][:, j].imag]) for j in range(len(NS))])
        np.savetxt(HERE / f"lamhat_zeta_{kind}.csv", arr, delimiter=",", fmt="%.8g", header=hdr, comments="")
        # normalised F_t(log n) / F_EF-peak(t=0)
        say(f"\n== H1/H2 [{kind}]: Re LamHat_t(n)/Lambda(n) (= F_t(log n) normalised by the t=0 explicit-formula peak), zeta N'=3000 ==")
        sel_t = [0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0]
        say("   t    " + "  ".join(f"n={n:<5d}" for n in [2, 3, 4, 5, 7, 8, 9, 11]))
        for tt in sel_t:
            i = int(np.argmin(np.abs(t - tt)))
            row = []
            for n in [2, 3, 4, 5, 7, 8, 9, 11]:
                j = NS.index(n)
                row.append(r["LamHat"][i, j].real / L[n])
            say(f"  {t[i]:.3f} " + "  ".join(f"{x:+.4f} " for x in row))
    # prediction comparison (smooth)
    r = R[("zeta", "smooth")]
    T = r["T"]
    g0 = load("zeta")[1][0]
    say("\n== H2: measured LamHat_t(n) vs heuristic prediction Lambda_b(n;t) n^{-i pi t/8} <(gamma/2pi)^{-(t/4)log n}>_w  [smooth, N'=3000] ==")
    rows = []
    for tt in [0.0, 0.1, 0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        for n in NS:
            j = NS.index(n)
            pr = pred_lamhat(t[i], n, T, "smooth", g0[0])
            me = r["LamHat"][i, j]
            rows.append((t[i], n, me.real, me.imag, pr.real, pr.imag))
    np.savetxt(HERE / "h2_measured_vs_predicted.csv", np.array(rows), delimiter=",", fmt="%.8g",
               header="t,n,Re_measured,Im_measured,Re_predicted,Im_predicted", comments="")
    say("   t     n   measured (Re, Im)        predicted (Re, Im)       control-noise sd (GUE, Poisson; Re)")
    for tt in [0.0, 0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        for n in [2, 3, 4, 5, 6, 7, 10, 11, 12]:
            j = NS.index(n)
            me = r["LamHat"][i, j]
            pr = pred_lamhat(t[i], n, T, "smooth", g0[0])
            sg = np.std([R[(c, "smooth")]["LamHat"][i, j].real for c in CONTROLS[:3]])
            sp = np.std([R[(c, "smooth")]["LamHat"][i, j].real for c in CONTROLS[3:]])
            say(f"  {t[i]:.2f}  {n:2d}  ({me.real:+.4f}, {me.imag:+.4f})   ({pr.real:+.4f}, {pr.imag:+.4f})   ({sg:.4f}, {sp:.4f})")
    # ---- H3 lattice
    say("\n== H3: lattice peak |sum_k w_k exp(2 pi i Nbar_t(gamma_k(t)))| / sum w_k  (unfolded frequency 2 pi) ==")
    say("   t     zeta     gue1     gue2     gue3     poi1     poi2     poi3")
    for tt in [0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        say(f"  {t[i]:.3f}  " + "  ".join(f"{R[(lab, 'smooth')]['latt'][i]:.4f}" for lab in ["zeta"] + CONTROLS))
    # ---- functionals
    say("\n== Task 3: candidate functionals along t (smooth window, N'=3000): monotonicity on the 44-point t grid ==")
    for lab in ["zeta"] + CONTROLS:
        rr = R[(lab, "smooth")]
        say(f"[{lab}]")
        say("  " + monotone_report("(a) log-gas energy E", rr["E"], t))
        say("  " + monotone_report("(b) Bragg weight B (Re)", rr["B"], t))
        say("  " + monotone_report("(b') Bragg weight |A|^2", rr["Bc"], t))
        say("  " + monotone_report("(c1) l2 dist to EF(t=0)", rr["d_ef"], t))
        say("  " + monotone_report("(c2) l2 dist to lattice(t)", rr["d_latt"], t))
        say("  " + monotone_report("(d) pure-point fraction", rr["ppf"], t))
        say("  " + monotone_report("(H3) lattice peak", rr["latt"], t))
    func_rows = []
    for lab in ["zeta"] + CONTROLS:
        rr = R[(lab, "smooth")]
        for i in range(len(t)):
            func_rows.append([t[i], (["zeta"] + CONTROLS).index(lab), rr["E"][i], rr["D"][i],
                              rr["B"][i], rr["Bc"][i], rr["d_ef"][i], rr["d_latt"][i], rr["ppf"][i], rr["latt"][i]])
    np.savetxt(HERE / "functionals.csv", np.array(func_rows, float), delimiter=",", fmt="%.10g",
               header="t,ensemble(0=zeta,1-3=gue1-3,4-6=poisson1-3),energy,dissipation,B_re,B_abs,dist_EF,dist_lattice,pure_point_fraction,lattice_peak",
               comments="")
    # ---- controls ratio for B
    say("\n== Controls: Bragg weight B(t) zeta / mean(control) ==")
    for tt in [0.0, 0.1, 0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        bz = R[("zeta", "smooth")]["Bc"][i]
        bg_ = np.mean([R[(c, "smooth")]["Bc"][i] for c in CONTROLS[:3]])
        bp_ = np.mean([R[(c, "smooth")]["Bc"][i] for c in CONTROLS[3:]])
        say(f"  t={t[i]:.2f}  B_zeta={bz:.5f}  B_GUE={bg_:.5f}  B_Poisson={bp_:.5f}  ratio zeta/GUE={bz / bg_:.2f}  zeta/Poisson={bz / bp_:.2f}")
    # ---- N' dependence of derivative at 0+
    say("\n== Task 3: derivative at t=0+ vs N' (smooth window); first grid step [0, 0.005] ==")
    for nprime in NPRIME_LIST:
        rr = analyse("zeta", nprime, "smooth", full=False)
        rg = analyse("gue1", nprime, "smooth", full=False)
        dB = (rr["Bc"][1] - rr["Bc"][0]) / (rr["t"][1] - rr["t"][0])
        dE = (rr["E"][1] - rr["E"][0]) / (rr["t"][1] - rr["t"][0])
        dL2 = (rr["LamHat"][1, 0].real - rr["LamHat"][0, 0].real) / (rr["t"][1] - rr["t"][0])
        dBg = (rg["Bc"][1] - rg["Bc"][0]) / (rg["t"][1] - rg["t"][0])
        say(f"  N'={nprime:5d} T={rr['T']:8.2f}  B(0)={rr['Bc'][0]:.5f}  dB/dt={dB:+.5f}  (dB/dt)/B={dB / rr['Bc'][0]:+.4f}"
            f"  d ReLamHat(2)/dt={dL2:+.4f}  [GUE1: B(0)={rg['Bc'][0]:.5f} dB/dt={dBg:+.5f}]")
    # amplitude scaling with T at fixed t (heuristic: |A_t(log p)| ~ T^{1-(t/4)log p})
    say("\n== Height scaling: log|A_t(log 2)| vs log T across N' in {500,1000,2000,3000} (heuristic slope 1-(t/4)log 2) ==")
    for tt in [0.0, 0.5, 1.0]:
        xs, ys = [], []
        for nprime in NPRIME_LIST:
            rr = analyse("zeta", nprime, "smooth", full=False)
            i = int(np.argmin(np.abs(rr["t"] - tt)))
            xs.append(math.log(rr["T"])); ys.append(math.log(abs(rr["A"][i, 0])))
        sl = np.polyfit(xs, ys, 1)[0]
        say(f"  t={tt:.1f}: fitted slope {sl:.3f}   heuristic (large-T) {1 - tt / 4 * math.log(2):.3f}")
    # ---- universality of the decay law (controls): power in u-bands vs phonon prediction
    say("\n== Universality: GUE power <|A_t(u)|^2>_band / <|A_0(u)|^2>_band vs linear phonon prediction "
        "sum_k w_k^2 exp(-2 r(u,gamma_k) t) / sum_k w_k^2,  r = (u/4)(log(gamma/2pi) - u)  [3 GUE samples pooled] ==")
    bands = [(0.4, 0.6), (0.9, 1.1), (1.9, 2.1), (2.9, 3.1)]
    for tt in [0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        line = f"  t={t[i]:.2f}"
        for (a, b) in bands:
            j0, j1 = int(a / DU), int(b / DU)
            num = den = 0.0
            pr = []
            for c in CONTROLS[:3]:
                Fg = R[(c, "smooth")]["Fgrid"]
                num += np.mean(Fg[i, j0:j1] ** 2); den += np.mean(Fg[0, j0:j1] ** 2)
                g0c = load(c)[1][0]
                wc, Tc, _ = weights(g0c, NPRIME_MAIN, "smooth")
                uu = 0.5 * (a + b)
                pr.append(np.sum(wc ** 2 * np.exp(-2 * phonon_rate(uu, g0c) * t[i])) / np.sum(wc ** 2))
            line += f"   u~{0.5 * (a + b):.1f}: meas {num / den:.3f} pred {np.mean(pr):.3f}"
        say(line)
    say("\n== Predicted (dB'/dt)/B' at t=0 from the phonon rates: -2 sum_n |A_0(log n)|^2 <r(log n, gamma)>_w / sum_n |A_0(log n)|^2 ==")
    pp = prime_powers(U_MAX)
    for nprime in NPRIME_LIST:
        rr = analyse("zeta", nprime, "smooth", full=False)
        g0z = load("zeta")[1][0]
        wz, Tz, wbz = weights(g0z, nprime, "smooth")
        num = den = 0.0
        for n in pp:
            amp2 = (L[n] / math.sqrt(n)) ** 2
            rbar = window_integral(Tz, "smooth", lambda g: phonon_rate(math.log(n), np.asarray(g))) / (Tz * wbz)
            num += amp2 * rbar; den += amp2
        dB = (rr["Bc"][1] - rr["Bc"][0]) / (rr["t"][1] - rr["t"][0])
        say(f"  N'={nprime:5d}  measured (dB'/dt)/B' over [0,0.005] = {dB / rr['Bc'][0]:+.4f}   phonon prediction {-2 * num / den:+.4f}")
    # ---- task 4
    identity_check()
    say("\n== Task 4b: d/dt LamHat_t(n) at t=0 from exact ODE velocities (with tail) vs arithmetic prediction ==")
    say("prediction = (1/4)[log^2 n Lambda(n) + log n (Lambda*Lambda)(n)] - (1/4) log n Lambda(n) [<log(gamma/2pi)>_w + i pi/2]")
    der_rows = []
    for lab in ["zeta", "gue1", "poisson1"]:
        out, mlog = derivative_at_zero(lab, NPRIME_MAIN, "smooth")
        say(f"[{lab}] <log(gamma/2pi)>_w = {mlog:.4f}")
        for n, meas, pred in out:
            say(f"   n={n:2d}  measured ({meas.real:+.4f}, {meas.imag:+.4f})   arithmetic prediction ({pred.real:+.4f}, {pred.imag:+.4f})   (Lambda*Lambda)(n)={C[n]:.4f}")
            der_rows.append((["zeta", "gue1", "poisson1"].index(lab), n, meas.real, meas.imag, pred.real, pred.imag))
    np.savetxt(HERE / "task4_derivative_at_zero.csv", np.array(der_rows), delimiter=",", fmt="%.8g",
               header="ensemble(0=zeta,1=gue1,2=poisson1),n,Re_measured,Im_measured,Re_pred,Im_pred", comments="")
    # ---- task 6
    backward_and_offline()
    (HERE / "results_summary.txt").write_text("\n".join(OUT_LINES) + "\n")
    # compact F grid snapshots for the record (zeta smooth, a few t)
    r = R[("zeta", "smooth")]
    idx = [int(np.argmin(np.abs(t - tt))) for tt in (0.0, 0.2, 0.5, 1.0)]
    sub = slice(0, len(U_GRID), 5)
    np.savetxt(HERE / "F_grid_zeta_smooth.csv",
               np.column_stack([U_GRID[sub]] + [r["Fgrid"][i][sub] for i in idx]), delimiter=",", fmt="%.6g",
               header="u,F_t0,F_t0.2,F_t0.5,F_t1.0", comments="")


def nprime_derivatives():
    """Finite-difference derivative at t=0+ (first grid step [0, 0.005]) of every functional, vs N'."""
    lines = ["functional derivative at t=0+ over [0, 0.005] vs N' (smooth window)",
             "label   N'     T        dE/dt          dB/dt        dB'/dt       d(dist_EF)/dt  d(dist_latt)/dt  d(ppf)/dt   d(latt)/dt"]
    rows = []
    for lab in ["zeta", "gue1", "poisson1"]:
        for nprime in NPRIME_LIST:
            r = analyse(lab, nprime, "smooth", full=True, tsel=[0, 1])
            dt = r["t"][1] - r["t"][0]
            d = {k: (r[k][1] - r[k][0]) / dt for k in ("E", "B", "Bc", "d_ef", "d_latt", "ppf", "latt")}
            lines.append(f"{lab:8s}{nprime:5d}  {r['T']:8.1f}  {d['E']:+.5e}  {d['B']:+.5f}  {d['Bc']:+.5f}  "
                         f"{d['d_ef']:+.5f}       {d['d_latt']:+.5f}         {d['ppf']:+.5f}    {d['latt']:+.5f}")
            rows.append([["zeta", "gue1", "poisson1"].index(lab), nprime, r["T"], d["E"], d["B"], d["Bc"],
                         d["d_ef"], d["d_latt"], d["ppf"], d["latt"]])
            print(lines[-1])
    np.savetxt(HERE / "nprime_derivatives.csv", np.array(rows), delimiter=",", fmt="%.8g",
               header="ensemble(0=zeta,1=gue1,2=poisson1),Nprime,T,dE,dB_re,dB_abs,d_dist_EF,d_dist_latt,d_ppf,d_latt",
               comments="")
    (HERE / "nprime_derivatives.txt").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "nprime":
        nprime_derivatives()
    else:
        main()
