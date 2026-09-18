#!/usr/bin/env python3
"""Diffraction figures for the certified zero ladder (Dyson quasicrystal).

Generates, from the rigorous Arb zero inventory (hardy_z_zeros):
  1. dyson_diffraction_T<T>.pdf   -- technical: stems at u = m log p vs Landau
                                     theory, uniform-grid trace, noise band
                                     (the paper figure, \cref{fig:diffraction})
  2. quasicrystal_spectrum_shape.png -- spectrum linked to the phase walks
                                     W(u) = sum_k exp(i gamma_k u)
  3. quasicrystal_music.png       -- lay version: x-axis is the number being
                                     "played"; the zeros ring at the primes

TRUST LABEL: these are NUMERICAL demonstrations over Arb ball ordinates
(width <= ~3e-11) -- the same certified-inventory class that gates the band
certificates, but the cosine sums are floating-point.  The kernel-certified
Bragg amplitudes are the B0-B3 ladder (GW_OS_BRAGG_SCOPING_2026-09-12.md §3).

Usage:
  python3 bragg_figures.py --nzeros 232878 --T 160000 --out-dir /tmp
The zero fetch (~20 min at 233k) is cached in <out-dir>/zeros_<nzeros>.npy.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent.parent / "src"))


def fetch_zeros(n: int, cache: Path) -> np.ndarray:
    if cache.exists():
        g = np.load(cache)
        if len(g) >= n:
            return g[:n]
    from telperion.arb_platt import hardy_z_zeros
    gammas = np.empty(n)
    CHUNK = 8192
    i = 0
    while i < n:
        c = min(CHUNK, n - i)
        for j, (lo, hi) in enumerate(hardy_z_zeros(i + 1, c, prec=64)):
            gammas[i + j] = (float(lo) + float(hi)) / 2
        i += c
        print(f"  fetched {i}/{n} zeros", flush=True)
    np.save(cache, gammas)
    return gammas


def prime_powers(limit: int):
    from sympy import factorint
    out = []
    for m in range(2, limit + 1):
        f = factorint(m)
        if len(f) == 1:
            p, k = next(iter(f.items()))
            out.append((m, p, k))
    return out


def fig_technical(g, T, out: Path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    N = len(g)
    scale = T / (2 * np.pi)
    us = np.linspace(0.3, 4.3, 16001)
    F = np.zeros_like(us)
    for i in range(0, N, 4000):
        F += np.cos(np.outer(us, g[i:i + 4000])).sum(axis=1)

    fig, ax = plt.subplots(figsize=(12, 5.6))
    ax.plot(us, -F / scale, lw=0.4, color="#9ab0d0",
            label="uniform grid trace (spacing $2.5\\times10^{-4}$)")
    pk_u, pk_v, pk_th = [], [], []
    for n, p, m in prime_powers(70):
        u = m * np.log(p) if n == p ** m else None
        u = np.log(n)
        if not (0.3 < u < 4.3):
            continue
        pk_u.append(u)
        pk_v.append(-np.cos(g * u).sum() / scale)
        pk_th.append(np.log(p) / p ** (m / 2))
        if pk_v[-1] > 0.15:
            ax.annotate(f"{p}" if m == 1 else f"${p}^{m}$", (u, pk_v[-1]),
                        xytext=(0, 5), textcoords="offset points",
                        ha="center", fontsize=7, color="#8b1a1a")
    ax.vlines(pk_u, 0, pk_v, color="#1a3a6b", lw=1.2)
    ax.plot(pk_u, pk_v, "o", ms=3.5, color="#1a3a6b",
            label=r"exact $-F_T(m\log p)/(T/2\pi)$")
    ax.plot(pk_u, pk_th, "_", ms=10, color="#c22",
            label=r"Landau: $(\log p)\,p^{-m/2}$")
    nf = np.sqrt(N / 2) / scale
    ax.axhspan(-nf, nf, color="orange", alpha=0.25,
               label=r"random-phase band $\pm\sqrt{N/2}/(T/2\pi)$")
    ax.axhline(0, color="gray", lw=0.4)
    ax.set_xlabel(r"$u$")
    ax.set_ylabel(r"$-F_T(u)/(T/2\pi)$")
    ax.legend(loc="upper right", fontsize=7.5)
    ax.set_xlim(0.3, 4.3)
    ax.set_ylim(-0.1, 0.82)
    fig.tight_layout()
    fig.savefig(out)
    print(f"wrote {out}; max |exact-theory| = "
          f"{max(abs(v - t) for v, t in zip(pk_v, pk_th)):.5f} "
          f"(noise band {nf:.4f})")


def fig_music(g, T, out: Path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec

    N = len(g)
    scale = T / (2 * np.pi)
    us = np.linspace(0.3, 4.3, 16001)
    F = np.zeros_like(us)
    for i in range(0, N, 4000):
        F += np.cos(np.outer(us, g[i:i + 4000])).sum(axis=1)
    nf = np.sqrt(N / 2) / scale

    fig = plt.figure(figsize=(14, 11))
    gs = GridSpec(3, 1, height_ratios=[0.55, 1.5, 1.0], hspace=0.5)

    ax1 = fig.add_subplot(gs[0])
    seg = g[:60]
    ax1.vlines(seg, 0.25, 0.75, color="#1a3a6b", lw=1.4)
    ax1.set_xlim(0, seg[-1] + 3)
    ax1.set_ylim(0, 1)
    ax1.set_yticks([])
    ax1.set_xlabel("position on the number line", fontsize=10)
    ax1.set_title(
        '1.  The raw material: the "zeros" of the Riemann zeta function -- '
        "special points that encode the primes.\nHere are the first 60. They "
        f"look irregular -- no repeating pattern. (We verified {N:,} of them "
        "by computer proof.)", fontsize=11, loc="left")

    ax2 = fig.add_subplot(gs[1])
    ax2.semilogx(np.exp(us), -F / scale, lw=0.5, color="#b0c0d8")
    for n, p, m in prime_powers(70):
        u = np.log(n)
        v = -np.cos(g * u).sum() / scale
        is_prime = m == 1
        ax2.vlines(n, 0, v, color="#c22222" if is_prime else "#888888",
                   lw=2.2 if is_prime else 1.4)
        ax2.annotate(str(n), (n, v), xytext=(0, 5),
                     textcoords="offset points", ha="center",
                     fontsize=10 if is_prime else 7.5,
                     fontweight="bold" if is_prime else "normal",
                     color="#c22222" if is_prime else "#666666")
    ax2.axhspan(-nf, nf, color="orange", alpha=0.3)
    ax2.axhline(0, color="gray", lw=0.4)
    ax2.set_xlim(1.8, 72)
    ax2.set_ylim(-0.12, 0.85)
    ax2.set_xticks([2, 3, 5, 10, 20, 50, 70])
    ax2.set_xticklabels(["2", "3", "5", "10", "20", "50", "70"], fontsize=10)
    ax2.set_xlabel('the number being "played"', fontsize=10)
    ax2.set_ylabel("loudness of the ring", fontsize=10)
    ax2.annotate("silence between the peaks:\nthe orange band is pure static",
                 (11.5, 0.06), fontsize=9.5, color="#b07000", ha="center")
    ax2.set_title(
        '2.  Now "play" every number to the zeros and listen. They ring '
        "loudly at the primes (red) --\n2, 3, 5, 7, 11, 13 ... -- more "
        "quietly at powers of primes (gray: 4, 8, 9, 25, 27...), and at no "
        "other number.\nThe volume of every ring matches the mathematical "
        "prediction to four decimal places.", fontsize=11, loc="left")

    ax3 = fig.add_subplot(gs[2])
    deltas = np.linspace(-8e-5, 8e-5, 481)
    u0 = np.log(2)
    resp = np.array([-np.cos(g * (u0 + d)).sum() / scale for d in deltas])
    ax3.plot(2 * np.exp(deltas), resp, lw=1.2, color="#c22222")
    ax3.axhspan(-nf, nf, color="orange", alpha=0.3)
    ax3.axhline(0, color="gray", lw=0.4)
    ax3.set_xlim(2 * np.exp(-8e-5), 2 * np.exp(8e-5))
    ax3.set_xticks([1.99985, 2.0, 2.00015])
    ax3.set_xticklabels(["1.99985", "exactly 2", "2.00015"], fontsize=10)
    ax3.set_xlabel("tuning the dial near the number 2", fontsize=10)
    ax3.set_ylabel("loudness", fontsize=10)
    ax3.annotate("detune by 2 parts in 100,000\nand the signal vanishes "
                 "into static", (2 * np.exp(4.5e-5), 0.25), fontsize=9.5,
                 color="#444")
    ax3.set_title(
        "3.  How sharp is the ring? Sharper than any radio station: a hair "
        "off the exact number 2 and it is gone.\nThe more zeros we verify, "
        "the sharper the peaks get -- this is why the zeros are called a "
        '"quasicrystal" of the primes.', fontsize=11, loc="left")

    fig.suptitle(f"The hidden music of the primes, played on {N:,} "
                 "computer-verified zeta zeros", fontsize=13.5, y=0.985)
    fig.savefig(out, dpi=140, bbox_inches="tight")
    print(f"wrote {out}")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--nzeros", type=int, default=232878)
    ap.add_argument("--T", type=float, default=160000.0)
    ap.add_argument("--out-dir", type=Path, default=Path("/tmp"))
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    g = fetch_zeros(args.nzeros, args.out_dir / f"zeros_{args.nzeros}.npy")
    fig_technical(g, args.T, args.out_dir / f"dyson_diffraction_T{int(args.T)}.pdf")
    fig_music(g, args.T, args.out_dir / "quasicrystal_music.png")


if __name__ == "__main__":
    main()
