"""Anchors requested by the island owner (2026-10-11 follow-up to the heat-flow diffraction search).

A. Reproduce the certified BraggH100 value F_100(u2), u2 = 693147/10^6, island convention
   F_T(u) = sum_{0<gamma<=T} cos(gamma u) (one-sided, unweighted).
B. Landau / Gonek normalisation  F_T(log n) ~ -(T/2pi) Lambda(n)/sqrt(n) + O(log T):
   residual vs T (t = 0) and vs t (along the heat flow).
C. Davenport-Heilbronn on-line comb as a fourth control: refine the certified on-line boxes of
   examples/quasicrystal/zoo_data/dh_zeros.json (read-only) to ordinates, check the certified ZooDH
   values, evolve the on-line comb by the same ODE, and compare its Bragg weights with the -D'/D
   coefficients of D (not prime-supported).

SEARCH, not proof.  Not an estimate of the de Bruijn-Newman constant.  conjecture1_proved = False.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import heat_flow_ode as hf  # noqa: E402
import diffraction_flow as df  # noqa: E402

HERE = hf.HERE
ISLAND = HERE.parent.parent
OUT: list[str] = []
NS = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def landau(T, n):
    return -(T / (2 * math.pi)) * df.mangoldt(n) / math.sqrt(n)


# ----------------------------------------------------------------------------- A
def part_a():
    say("== A. certified anchor: BraggH100 (29 zeros, T = 100) ==")
    mp.mp.dps = 30
    g = [mp.mpf(x) for x in (HERE / "zeros5001.txt").read_text().split()[:30]]
    assert g[28] < 100 < g[29]
    u2 = mp.mpf(693147) / 10 ** 6
    F = mp.fsum(mp.cos(x * u2) for x in g[:29])
    lo, hi = mp.mpf("-7.0780948677"), mp.mpf("-7.0780546651")
    say(f"F_100(u2) = {mp.nstr(F, 15)}   certified [{lo}, {hi}]   inside: {lo <= F <= hi}")
    say(f"Landau peak at u = log 2: -(100/2pi) log2/sqrt2 = {landau(100, 2):.4f}; "
        f"F_100(log 2) = {mp.nstr(mp.fsum(mp.cos(x * mp.log(2)) for x in g[:29]), 10)}")


# ----------------------------------------------------------------------------- B
def part_b():
    say("\n== B. Landau normalisation, unweighted one-sided F_T (island convention) ==")
    t, G, *_ = df.load("zeta")
    g0 = G[0]
    Ts = [100, 200, 500, 1000, 2000, 3500]
    nlist = [2, 3, 4, 5, 7, 8, 9, 11]
    rows = []
    say("t = 0:  residual R = F_T(log n) - Landau;  R_sm = R - (smooth gamma-factor term + Gibbs, from the explicit formula)")
    say("     T    log T   " + "  ".join(f"n={n}: ratio   R      R_sm " for n in nlist[:4]))
    for T in Ts:
        k = int(np.searchsorted(g0, T))
        us = np.log(np.array(nlist, float))
        F = df.amp_at(g0[:k], np.ones(k), us).real
        bg = df.smooth_background(us, T, "sharp")
        line = f"  {T:5d}  {math.log(T):5.2f}  "
        for j, n in enumerate(nlist):
            L = landau(T, n)
            rows.append((0.0, T, n, F[j], L, F[j] / L, F[j] - L, F[j] - L - bg[j]))
            if j < 4:
                line += f"   {F[j] / L:6.3f} {F[j] - L:+7.2f} {F[j] - L - bg[j]:+6.2f}"
        say(line)
    say("(full table incl. n = 7, 8, 9, 11 in anchors_landau_residual.csv)")
    say("\nAlong the flow, T = 3500 (particles with gamma_k(0) <= T): F_t(log n) / Landau(T, n)  and residual R / log T")
    k = int(np.searchsorted(g0, 3500))
    say("   t     " + "  ".join(f"n={n:<2d} ratio  R/logT" for n in nlist[:5]))
    for tt in [0.0, 0.1, 0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        us = np.log(np.array(nlist, float))
        F = df.amp_at(G[i][:k], np.ones(k), us).real
        line = f"  {t[i]:.2f} "
        for j, n in enumerate(nlist):
            L = landau(3500, n)
            rows.append((t[i], 3500, n, F[j], L, F[j] / L, F[j] - L, float("nan")))
            if j < 5:
                line += f"   {F[j] / L:6.3f} {(F[j] - L) / math.log(3500):+7.2f}"
        say(line)
    np.savetxt(HERE / "anchors_landau_residual.csv", np.array(rows), delimiter=",", fmt="%.10g",
               header="t,T,n,F_T,landau_peak,ratio,residual,residual_minus_smooth_term", comments="")


# ----------------------------------------------------------------------------- C
KAPPA = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)


def dh_D(s):
    return mp.power(5, -s) * (mp.zeta(s, mp.mpf(1) / 5) + KAPPA * mp.zeta(s, mp.mpf(2) / 5)
                              - KAPPA * mp.zeta(s, mp.mpf(3) / 5) - mp.zeta(s, mp.mpf(4) / 5))


def dh_Z(t):
    """Real on the critical line: exp(i arg g) D(1/2+it), g = (pi/5)^{-(1+s)/2} Gamma((1+s)/2)."""
    s = mp.mpf(1) / 2 + 1j * mp.mpf(t)
    ph = mp.im(-(1 + s) / 2 * mp.log(mp.pi / 5) + mp.loggamma((1 + s) / 2))
    return mp.re(mp.exp(1j * ph) * dh_D(s))


def dh_ordinates():
    cache = HERE / "dh_online_ordinates.txt"
    if cache.exists():
        return np.loadtxt(cache)
    mp.mp.dps = 25
    d = json.loads((ISLAND / "examples/quasicrystal/zoo_data/dh_zeros.json").read_text())
    on = sorted([z for z in d["zeros"] if z["on_line"]], key=lambda z: z["gamma_approx"])
    out = []
    for z in on:
        a, b = (mp.mpf(Fraction(x).numerator) / Fraction(x).denominator for x in z["im"])
        fa, fb = dh_Z(a), dh_Z(b)
        if fa * fb > 0:
            raise RuntimeError(f"no sign change of Z_D on certified box {z['im']}")
        r = mp.findroot(dh_Z, (a, b), solver="anderson", tol=mp.mpf(10) ** -18)
        assert a <= r <= b
        out.append(float(r))
    np.savetxt(cache, np.array(out), fmt="%.15f",
               header="Davenport-Heilbronn on-line ordinates (refined from certified boxes of dh_zeros.json; mpmath, float precision)")
    return np.array(out)


def dh_lambda(nmax=200):
    c = [None, 1.0, float(KAPPA), -float(KAPPA), -1.0, 0.0]
    a = np.array([0.0] + [c[((n - 1) % 5) + 1] for n in range(1, nmax + 1)], dtype=complex)
    return a, df.lambda_D(a)


def part_c():
    say("\n== C. Davenport-Heilbronn on-line comb (fourth control) ==")
    gd = dh_ordinates()
    say(f"{len(gd)} on-line ordinates refined inside their certified boxes (gamma_1 = {gd[0]:.10f}, gamma_max = {gd[-1]:.6f})")
    d = json.loads((ISLAND / "examples/quasicrystal/zoo_data/dh_zeros.json").read_text())
    offl = [z for z in d["zeros"] if not z["on_line"]]
    for u, name, (lo, hi) in ((693147e-6, "u2", (-0.170181, -0.152173)), (1609437e-6, "u5", (-2.254028, -2.031779))):
        F = float(np.sum(np.cos(gd[gd <= 100] * u)))
        say(f"F_on,100({name}) = {F:+.6f}   certified ZooDH box [{lo}, {hi}]   inside: {lo <= F <= hi}")
    for z in offl:
        dl = z["beta_approx"] - 0.5
        flag = "  (UNVERIFIED: suspiciously round entry)" if abs(z["gamma_approx"] - 166.5) < 1e-9 else ""
        say(f"  off-line gamma~{z['gamma_approx']}, delta~{dl:.3f}: term 2cosh(delta u)cos(gamma u) at log 2 = "
            f"{2 * math.cosh(dl * math.log(2)) * math.cos(z['gamma_approx'] * math.log(2)):+.4f}{flag}")
    a, LD = dh_lambda()
    # evolve the on-line comb (N = 204) with a conductor-5 mean-field tail; off-line zeros are NOT included
    z0 = 2 * gd
    spacing = 2 * math.pi / math.log(5 * gd[-1] / (2 * math.pi))
    Zc = 2 * (gd[-1] + 0.5 * spacing)
    tail = hf.Tail(Zc, conductor=5.0)
    sol = hf.integrate(z0, hf.T_GRID, tail, rtol=1e-11, atol=1e-11)
    t = sol.t
    G = sol.y.T / 2
    np.savez(hf.SCRATCH / "traj_dh.npz", t=t, Z=sol.y.T, Zc=Zc)
    Tw = 250.0
    k_dh = int(np.searchsorted(gd, Tw))
    tz, Gz, *_ = df.load("zeta")
    k_z = int(np.searchsorted(Gz[0], Tw))
    us = np.log(np.array(NS, float))
    say(f"\nT = {Tw} (sharp, one-sided): DH uses {k_dh} on-line zeros, zeta {k_z} zeros.")
    say("t = 0 effective weights LamHat(n) = -2 pi sqrt(n) F(log n) / T (no background subtraction; T is small, so O(log T)/T ~ 0.1 errors)")
    Fdh = df.amp_at(G[0][:k_dh], np.ones(k_dh), us)
    Fz = df.amp_at(Gz[0][:k_z], np.ones(k_z), us)
    ctrl = {}
    for c in ["gue1", "gue2", "gue3", "poisson1", "poisson2", "poisson3"]:
        tc, Gc, *_ = df.load(c)
        kc = int(np.searchsorted(Gc[0], Tw))
        ctrl[c] = (tc, Gc, kc)
    say("   n   Lambda(n)  zeta LamHat   Lambda_D(n)  DH LamHat(on-line)  DH LamHat(+4 off-line pairs)   GUE sd   Poisson sd")
    off = [(z["gamma_approx"], z["beta_approx"] - 0.5) for z in offl if z["gamma_approx"] <= Tw]
    rows = []
    for j, n in enumerate(NS):
        lz = -2 * math.pi * math.sqrt(n) * Fz[j].real / Tw
        ld = -2 * math.pi * math.sqrt(n) * Fdh[j].real / Tw
        cg = [-2 * math.pi * math.sqrt(n) * df.amp_at(ctrl[c][1][0][:ctrl[c][2]], np.ones(ctrl[c][2]), us[j:j + 1])[0].real / Tw
              for c in ["gue1", "gue2", "gue3"]]
        cp = [-2 * math.pi * math.sqrt(n) * df.amp_at(ctrl[c][1][0][:ctrl[c][2]], np.ones(ctrl[c][2]), us[j:j + 1])[0].real / Tw
              for c in ["poisson1", "poisson2", "poisson3"]]
        u = math.log(n)
        foff = sum(2 * math.cosh(dl * u) * math.cos(gm * u) for gm, dl in off)
        ldo = -2 * math.pi * math.sqrt(n) * (Fdh[j].real + foff) / Tw
        say(f"  {n:2d}   {df.mangoldt(n):.4f}     {lz:+.4f}      {LD[n].real:+.4f}      {ld:+.4f}             {ldo:+.4f}                     {np.std(cg):.3f}    {np.std(cp):.3f}")
        rows.append((0.0, n, df.mangoldt(n), lz, LD[n].real, ld))
    # along the flow: DH heuristic prediction uses coefficients c(n) exp((t/4) log^2 n), height factor (5 gamma/2pi)
    say("\nAlong the flow (T = 250): Re LamHat_t(n), measured vs heuristic prediction "
        "Lambda_{c b}(n) n^{-i pi t/8} <(q gamma/2pi)^{-(t/4) log n}>  (q = 1 zeta, q = 5 DH)")
    say("   t     n   zeta meas  zeta pred   DH meas   DH pred")
    for tt in [0.2, 0.5, 1.0]:
        i = int(np.argmin(np.abs(t - tt)))
        aD = a.copy()
        aZ = np.array([0.0] + [1.0] * (len(a) - 1), dtype=complex)
        for n in range(1, len(a)):
            mult = math.exp(t[i] / 4 * math.log(n) ** 2)
            aD[n] *= mult
            aZ[n] *= mult
        LDt, LZt = df.lambda_D(aD), df.lambda_D(aZ)
        Fdh = df.amp_at(G[i][:k_dh], np.ones(k_dh), us)
        Fz = df.amp_at(Gz[i][:k_z], np.ones(k_z), us)
        for j, n in enumerate(NS):
            def hfac(q):
                f = lambda g: (q * np.asarray(g) / (2 * np.pi)) ** (-(t[i] / 4) * math.log(n))
                return df.window_integral(Tw, "sharp", f) / Tw
            pz = (LZt[n] * n ** (-1j * math.pi * t[i] / 8) * hfac(1.0)).real
            pd = (LDt[n] * n ** (-1j * math.pi * t[i] / 8) * hfac(5.0)).real
            mz = -2 * math.pi * math.sqrt(n) * Fz[j].real / Tw
            md = -2 * math.pi * math.sqrt(n) * Fdh[j].real / Tw
            if n in (2, 3, 5, 6, 7, 10, 11):
                say(f"  {t[i]:.2f}  {n:2d}   {mz:+.4f}   {pz:+.4f}    {md:+.4f}   {pd:+.4f}")
            rows.append((t[i], n, pz, mz, pd, md))
    np.savetxt(HERE / "anchors_dh_control.csv", np.array(rows), delimiter=",", fmt="%.8g",
               header="t,n,col3,col4,col5,col6  (t=0 rows: Lambda,zeta_LamHat,Lambda_D,DH_LamHat; t>0 rows: zeta_pred,zeta_meas,DH_pred,DH_meas)",
               comments="")
    say("\nNote: the DH on-line comb misses the 4 off-line zeros (complex in z) and is evolved as a real comb only.")


if __name__ == "__main__":
    say("anchors + DH control, 2026-10-11.  SEARCH, not proof.  conjecture1_proved = False")
    part_a()
    part_b()
    part_c()
    (HERE / "anchors_results.txt").write_text("\n".join(OUT) + "\n")
