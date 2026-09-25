"""Arb4_emit_seg.py -- lane Arb4: emit the COMPACT hypothesis-free certificates of one ladder segment.

usage: Arb4_emit_seg.py --seg H [--outdir DIR] [--json FILE] [--zeros FILE] [--replan]
                        [--edges-per-file 5] [--slabs-per-file 10] [--bands-per-file 5]
       H = 1000, 2000, or any multiple of 1000 >= 3000 (after Arb4_prepare_seg.py H)

For the segment [H - 1000 (or 1), H] of the zeta_zero_localization ladder (25 Turing bands, band table
from the BandGlue emitter: `BandGlue_h1000.lean`, or `Arb4_BandGlue_h<H>.lean` for H >= 2000) this
plans every kernel certificate with the planners of lanes h1000-integrate / h1000-prep, UNCHANGED:

  * the horizontal argument change at every band edge (octant pieces, endpoint boxes):
    `emit_h1000_offline.plan_edge` + `edge_enclosure`;
  * the zero-free edge-clearance slabs (cells): `emit_h1000_offline.plan_slab` (H <= 2000); for
    H >= 3000 the same cells and budget planned in ROWS (plan_slab_rows below: x-only cells per row,
    rows stacked by `Arb4.slabClear_join`), since an edge next to a zero needs cells short in y too;
  * the on-line sign points of every band: `emit_h1000_line.make_point` / `pt_check`;

and writes them in the COMPACT form of lane Arb4:

  Arb4_H<H>Edges_<k>.lean  -- `EdgeD` data + ONE `decide +kernel` of `edgeOK` per edge;
  Arb4_H<H>Slabs_<k>.lean  -- `SlabD` data + ONE `decide +kernel` of `slabOK` per slab (per row);
  Arb4_H<H>Lines_<k>.lean  -- band grid points `PtD`, ONE `decide +kernel` of `ptCheckC` per chunk of
                              7 points and ONE of `H1000Line.bandOk` per band (`bandC_sound`);
  Arb4_h<H>.lean           -- per band: enclosures `EnclQ`, K6b certificates `GamD`, ONE
                              `decide +kernel` of `validB && k6sideB`, the box certificate
                              (`Arb4.boxCert_of_parts`); the capstone
                              `all_nontrivial_zeros_up_to_height_<H>` (no hypotheses);
  Arb4_AxiomGuard_h<H>.lean -- `#print axioms` of every theorem + statement-shape checks.

Every check is mirrored exactly in Python before emission (the script REFUSES to emit a failing
certificate).  Numerics single-process.  conjecture1_proved = False.
"""
import argparse
import json
import math
import os
import re
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "arbecon"))
import emit_h1000_offline as OFF  # noqa: E402
import emit_h1000_line as LIN  # noqa: E402
import Arb4_emit as A  # noqa: E402
import offline_model as O  # noqa: E402

# Octant-piece evaluator fuel: `Arb4.PieceD.oc` uses Newton fuel 256 (`rootLoop` stops at convergence,
# so every run that converges within 64 steps is unchanged; at m = 2 a center with denominator q needs
# about 1.06 q steps: 72 at q = 64, 273 at q = 256).  The planner must mirror it.  A piece center with
# q = 256 (radius 1/256) therefore falls back: this stops [8000, 9000] at T = 8036.
PIECE_FUEL = 256
_make_ocfg = O.make_ocfg


def _make_ocfg_piece(c, a, b, q, nfuel=PIECE_FUEL):
    return _make_ocfg(c, a, b, q, nfuel)


OFF.O.make_ocfg = _make_ocfg_piece

# ------------------------------------------------------------------ edge-clearance slabs in ROWS
#
# `Arb4.SlabD` covers `[1/2, 1] x [lo, hi]` by FULL-HEIGHT x-columns.  Up to height 2000 the planner
# `emit_h1000_offline.plan_slab` never split a slab in y.  From about 2500 on an edge can sit a few
# hundredths from a zero on the line (2479.977 under T = 2480), the cells touching it must be short
# too, and plan_slab splits in y.  For segments H >= 3000 the slab is planned in ROWS instead: each
# row `[y_i, y_(i+1)]` is planned with x-ONLY splits (the same budget, cells and exact check as
# plan_slab), a row that does not certify is halved in y, and the rows are stacked in Lean by
# `Arb4.slabClear_join` (Arb4_SlabRows.lean).  Column depth is capped at SLAB_XDEPTH x-splits (centers
# `1/2 + j/(12 * 2^k)`, q <= 384).  The Newton root at m = 2 needs about 1.06 q steps, so a center with
# q > ~240 exceeds the fuel 256 of `Arb4.CellD.oc`: its evaluator run falls back, which the exact
# mirror `run_center` reports and the planner treats as a failed cell (never emitted).

SLAB_XDEPTH = 5


def plan_slab_x(tag, a, b, J0=3, tq=14, max_depth=SLAB_XDEPTH):
    """emit_h1000_offline.plan_slab with x-ONLY splits; None if a column does not certify within
    max_depth x-splits (or its evaluator run falls back)."""
    a, b = Fr(a), Fr(b)
    N = OFF.slab_N(b)
    KEM = OFF.KEM
    U = Fr(OFF.ceil_sqrt_int(Fr(2 * KEM) ** 2 + b * b))
    Qr = OFF.round_up_sig(OFF.ceil_sqrt_int(OFF.poch_norm_sq(Fr(1), b, 2 * KEM + 1)))
    r0 = math.isqrt(N)
    E = OFF.CK6 * Qr / (Fr(N) ** (2 * KEM) * r0) / (2 * KEM + Fr(1, 2))

    def cell_geom(xl, xr):
        sig = (xl + xr) / 2
        tc = Fr(round((a + b) / 2 * 2 ** tq), 2 ** tq)
        w = (xr - xl) / 2
        hh = max(tc - a, b - tc)
        rd = 10000
        rn = math.isqrt(int((w * w + hh * hh) * rd * rd)) + 1
        while Fr(rn, rd) ** 2 < w * w + hh * hh:
            rn += 1
        return sig, tc, w, hh, rn, rd

    root = [(Fr(1, 2) + Fr(j, 2 * J0), Fr(1, 2) + Fr(j + 1, 2 * J0)) for j in range(J0)]
    R = max(Fr(cell_geom(*cl)[4], cell_geom(*cl)[5]) for cl in root)
    _, _, _, sN0 = OFF.run_center(round(a * 2 ** tq), tq, Fr(3, 4), N, OFF.PT)
    L = OFF.ceil_to(Fr(sN0.lhi, OFF.TWO64), 1000)
    assert R * L <= 1
    B = (OFF.CP5 * (R * L) ** (OFF.PT + 1) * ((N - 1) + OFF.emcB(N, a, U)) + 3 * OFF.corrVar(N, R, a, U) + E)
    F = OFF.nice_up(B, Fr(1, 100))

    def solve(xl, xr, depth):
        sig, tc, w, hh, rn, rd = cell_geom(xl, xr)
        tn = int(tc * 2 ** tq)
        assert Fr(tn, 2 ** tq) == tc and a <= tc
        try:
            c, o, s1, sN = OFF.run_center(tn, tq, sig, N, OFF.PT)
        except AssertionError:
            return None
        ok, margin = OFF.check_cell_exact(c, o, N, s1.acc, sN.acc, rn, rd, F)
        if ok:
            return dict(leaf=True, xl=xl, xr=xr, yl=a, yh=b, sig=sig, tc=tc, tn=tn, w=w, hh=hh, rn=rn, rd=rd,
                        o=o, s1=s1, sN=sN, margin=margin)
        if depth >= max_depth:
            return None
        xm = (xl + xr) / 2
        lo = solve(xl, xm, depth + 1)
        hi = solve(xm, xr, depth + 1) if lo is not None else None
        if hi is None:
            return None
        return dict(leaf=False, axis="x", m=xm, lo=lo, hi=hi)

    trees = [solve(xl, xr, 0) for xl, xr in root]
    if any(t is None for t in trees):
        return None
    return dict(tag=tag, a=a, b=b, N=N, U=U, Qr=Qr, r0=r0, E=E, R=R, L=L, F=F,
                root=[(xl, xr, a, b) for xl, xr in root], trees=trees, tq=tq)


def plan_slab_rows(tag, a, b, depth=0, max_rows_depth=6):
    """the rows `[a, b]` = row_0 + row_1 + ... (each planned by plan_slab_x; a failing row is halved).

    A row is tried with J0 = 3, 6, 12 root columns: the slab budget F grows like (R L)^6 in the ROOT
    radius R >= 1/(4 J0), so a slab whose corner is a few hundredths from a zero (|zeta| ~ 0.02 there)
    needs narrower root columns, not only smaller leaves (L3560 of [3000, 4000]: J0 = 3 gives F = 0.097
    and never certifies, J0 = 6 gives F = 0.0049 and 8 cells).  Leaves stay >= 1/192 wide (q <= 384)."""
    for J0, md in ((3, SLAB_XDEPTH), (6, SLAB_XDEPTH - 1), (12, SLAB_XDEPTH - 2)):
        sd = plan_slab_x(tag, a, b, J0=J0, max_depth=md)
        if sd is not None:
            return [sd]
    assert depth < max_rows_depth, "slab %s: the rows do not certify" % tag
    m = (Fr(a) + Fr(b)) / 2
    return plan_slab_rows(tag, a, m, depth + 1) + plan_slab_rows(tag, m, b, depth + 1)


def plan_slab_rowed(tag, a, b):
    """a slab as one dict: a single row is the row itself (as plan_slab); several rows are
    `dict(tag, a, b, rows=[...])`."""
    rows = plan_slab_rows(tag, a, b)
    if len(rows) == 1:
        return rows[0]
    return dict(tag=tag, a=Fr(a), b=Fr(b), rows=rows, N=max(r["N"] for r in rows),
                F=max(Fr(r["F"]) for r in rows))


def slab_rows(sd):
    return sd["rows"] if "rows" in sd else [sd]


def slab_ncells(sd):
    return sum(len(A.slab_cells(r)) for r in slab_rows(sd))


SCR = "/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad"


# ------------------------------------------------------------------ the band table (BandGlue module)

def parse_bandglue(path):
    src = open(path).read()
    seg = src[src.index("noncomputable def seg"):src.index("noncomputable def capLo")]
    rows = re.findall(r"\| (\d+) => ⟨(.*?),\n\s*(\S+)\.cPB, \S+\.RPB, \S+\.hs1PB⟩", seg)
    bands = []
    for i, body, mod in rows:
        parts = [p.strip() for p in OFF.split_top(body)]
        T0, T1, n = OFF.parse_num(parts[0]), OFF.parse_num(parts[1]), int(parts[2])
        bands.append(dict(i=int(i), T0=T0, T1=T1, n=n, mod=mod))

    def table(name):
        blk = src[src.index("noncomputable def %s" % name):]
        blk = blk[:blk.index("| _ =>")]
        return {int(i): OFF.parse_num(v) for i, v in re.findall(r"\| (\d+) => (\(.*?\))\n", blk)}

    capLo, capHi = table("capLo"), table("capHi")
    geo = re.findall(r"CapGeom\.of_sqrt \(δ0 := [^)]*\)\) \(δ1 := [^)]*\)\) (\(.*?\)) (\(.*?\)) "
                     r"(\(.*?\)) (\(.*?\))\n", src)
    assert len(geo) == len(bands), (len(geo), len(bands))
    for b, g in zip(bands, geo):
        t0, t1, cim, q = (OFF.parse_num(x) for x in g)
        assert t0 == b["T0"] and t1 == b["T1"]
        b.update(cim=cim, q=q, capLo=capLo[b["i"]], capHi=capHi[b["i"]])
    return bands


# ------------------------------------------------------------------ exact mirror of Arb4_Gamma

L2LO, L2HI = Fr(3465735902799708427977, 5000000000000000000000), Fr(6931471805599487910229, 10 ** 22)
LPLO, LPHI = Fr(11447298858493313056567, 10 ** 22), Fr(5723649429247365361409, 5 * 10 ** 21)
PILO, PIHI = Fr(314159265358979323846, 10 ** 20), Fr(314159265358979323847, 10 ** 20)


def lx(v, k):
    return 1 - v / Fr(2) ** k


def log_ok(v, k):
    x = lx(v, k)
    return v > 0 and 0 <= x < 1


def lser(x, n):
    return sum(x ** (i + 1) / (i + 1) for i in range(n))


def log_lo(v, k, n):
    x = lx(v, k)
    kl = k * L2LO if k >= 0 else k * L2HI
    return kl - lser(x, n) - x ** (n + 1) / (1 - x)


def log_hi(v, k, n):
    x = lx(v, k)
    kh = k * L2HI if k >= 0 else k * L2LO
    return kh - lser(x, n) + x ** (n + 1) / (1 - x)


def atan_ps(u, N):
    return sum((-1) ** j * u ** (2 * j + 1) / (2 * j + 1) for j in range(N))


def atan_err(u, N):
    return u ** (2 * N + 1) / (2 * N + 1)


def atan_ok(y, mode):
    if mode == 0:
        return 0 <= y <= 1
    if mode == 1:
        return y > 0
    return y == 1


def arctan_lo(y, N, mode):
    if mode == 0:
        return atan_ps(y, N) - atan_err(y, N)
    if mode == 1:
        u = 1 / y
        return PILO / 2 - (atan_ps(u, N) + atan_err(u, N))
    return PILO / 4


def arctan_hi(y, N, mode):
    if mode == 0:
        return atan_ps(y, N) + atan_err(y, N)
    if mode == 1:
        u = 1 / y
        return PIHI / 2 - (atan_ps(u, N) - atan_err(u, N))
    return PIHI / 4


def log_cert(v, tol=Fr(1, 10 ** 13)):
    k = 0
    while Fr(2) ** k < v:
        k += 1
    while k > -60 and Fr(2) ** (k - 1) >= v:
        k -= 1
    assert log_ok(v, k)
    x = lx(v, k)
    n = 1
    while x ** (n + 1) / (1 - x) > tol:
        n += 1
    return k, n


def atan_cert(y, tol=Fr(1, 10 ** 13)):
    if y == 1:
        return 2, 0
    if y < 1:
        mode, u = 0, y
    else:
        mode, u = 1, 1 / y
    N = 1
    while atan_err(u, N) > tol:
        N += 1
    return mode, N


def gam_cert(T):
    T = Fr(T)
    v2 = 1 + T * T / 4
    vm = Fr(1, 4) + T * T / 4
    k2, n2 = log_cert(v2)
    km, nm = log_cert(vm)
    md2, N2 = atan_cert(T / 2)
    mdm, Nm = atan_cert(T)
    return dict(T=T, k2=k2, n2=n2, km=km, nm=nm, md2=md2, N2=N2, mdm=mdm, Nm=Nm)


def s2_bounds(G):
    T = G["T"]
    lo = (Fr(1, 2) * arctan_lo(T / 2, G["N2"], G["md2"]) + T / 4 * log_lo(1 + T * T / 4, G["k2"], G["n2"])
          - T / 2 - T / 2 * LPHI)
    hi = (Fr(1, 2) * arctan_hi(T / 2, G["N2"], G["md2"]) + T / 4 * log_hi(1 + T * T / 4, G["k2"], G["n2"])
          - T / 2 - T / 2 * LPLO)
    return lo, hi


def sm1_bounds(G):
    T = G["T"]
    vm = Fr(1, 4) + T * T / 4
    lo = T / 4 * log_lo(vm, G["km"], G["nm"]) + arctan_lo(T, G["Nm"], G["mdm"]) - T / 2 - T / 2 * LPHI
    hi = T / 4 * log_hi(vm, G["km"], G["nm"]) + arctan_hi(T, G["Nm"], G["mdm"]) - T / 2 - T / 2 * LPLO
    return lo, hi


def em1(T):
    return T / (2 * (1 + T * T))


def e2(T):
    return T / (2 * (4 + T * T))


def k6_encl(G0, G1, den=10 ** 9):
    """(L4, H4, L5, H5) passing `Arb4.k6B` exactly (rounded outward to 1/den)."""
    m0, m1 = sm1_bounds(G0), sm1_bounds(G1)
    s0, s1 = s2_bounds(G0), s2_bounds(G1)
    L4 = OFF.floor_to(m1[0] - m0[1] - em1(G1["T"]), den)
    H4 = OFF.ceil_to(m1[1] - m0[0] + em1(G0["T"]), den)
    L5 = OFF.floor_to(s1[0] - s0[1] - e2(G1["T"]), den)
    H5 = OFF.ceil_to(s1[1] - s0[0] + e2(G0["T"]), den)
    return L4, H4, L5, H5


def pin_ok(n, E):
    L1, H1, L2, H2, L3, H3, L4, H4, L5, H5 = E
    pl = 2 * L1 + L2 - H3 + L4 + L5
    ph = 2 * H1 + H2 - L3 + H4 + H5
    lo = 2 * Fr(31416, 10000) * (n - 1)
    hi = 2 * Fr(314, 100) * (n + 1)
    return lo < pl and ph < hi, float(pl - lo), float(hi - ph)


def valid_ok(b):
    t0, t1, cim, q = b["T0"], b["T1"], b["cim"], b["q"]
    return (0 < t0 <= t1 and q > 0 and t0 <= cim <= t1 and Fr(9, 4) + (cim - t0) ** 2 < q
            and Fr(9, 4) + (t1 - cim) ** 2 < q and b["n"] >= 1)


# ------------------------------------------------------------------ on-line points (emit_h1000_line)

def band_points(band, zs, tq, nl):
    """emit_h1000_line.band_points for an explicit band (T0, T1, n) (the h1000 script reads its own
    fixed table)."""
    import mpmath
    mpmath.mp.dps = 25
    T0, T1, n = band["T0"], band["T1"], band["n"]
    T0f, T1f = float(T0), float(T1)
    inb = [z for z in zs if T0f <= z <= T1f]
    assert len(inb) == n, (band["i"], len(inb), n)
    edges = [T0f] + inb + [T1f]
    lo_tn = -(-(T0.numerator * 2 ** tq) // T0.denominator)
    hi_tn = (T1.numerator * 2 ** tq) // T1.denominator
    pts, info = [], []
    for i in range(n + 1):
        a, b = edges[i], edges[i + 1]
        cands = [a + (b - a) * j / 40 for j in range(1, 40)]
        if i == 0:
            cands.append(T0f)
        if i == n:
            cands.append(T1f)
        scored = sorted(((abs(float(mpmath.siegelz(t))), t) for t in cands), reverse=True)
        done = False
        for zabs, t in scored:
            tn = round(t * 2 ** tq)
            tn = min(max(tn, lo_tn), hi_tn)
            tt = tn / 2 ** tq
            if not (a < tt < b or (i == 0 and tt == T0f and T0f < inb[0])
                    or (i == n and tt == T1f and T1f > inb[-1])):
                continue
            z = float(mpmath.siegelz(tt))
            if z == 0:
                continue
            pos = z > 0
            eps = min(1e-3, abs(z) / 50)
            p = LIN.make_point(tn, tq, pos, eps, nl)
            ok, inf = LIN.pt_check(p, check_dir=False)
            if ok:
                pts.append(p)
                info.append({"t": tt, "Z": z, "N": p.N, "val": inf["val"], "err": inf["err"], "m": p.m})
                done = True
                break
        if not done:
            raise RuntimeError("band %d: no certifiable point in (%g, %g)" % (band["i"], a, b))
    T0n, T0d, T1n, T1d = T0.numerator, T0.denominator, T1.numerator, T1.denominator
    assert LIN.band_ok(T0n, T0d, T1n, T1d, n, pts), band["i"]
    return pts, info


def band_points_fast(band, tq, nl, ncand=12):
    """as band_points, the untrusted zeros from Arb4_zfast (count = the band plan's n, checked there)
    instead of a global zero list; grid points still certified by the exact Python mirror."""
    import numpy as np
    import Arb4_zfast as ZF
    T0, T1, n = band["T0"], band["T1"], band["n"]
    T0f, T1f = float(T0), float(T1)
    roots, ts, zv = ZF.zeros_between(T0f, T1f, n)
    edges = [T0f] + roots + [T1f]
    lo_tn = -(-(T0.numerator * 2 ** tq) // T0.denominator)
    hi_tn = (T1.numerator * 2 ** tq) // T1.denominator
    pts, info = [], []
    for i in range(n + 1):
        a, b = edges[i], edges[i + 1]
        cands = [a + (b - a) * j / 40 for j in range(1, 40)]
        if i == 0:
            cands.append(T0f)
        if i == n:
            cands.append(T1f)
        cz = ZF.Z(np.array(cands))
        order = np.argsort(-np.abs(cz))[:ncand]
        done = False
        for oi in order:
            t = cands[oi]
            tn = round(t * 2 ** tq)
            tn = min(max(tn, lo_tn), hi_tn)
            tt = tn / 2 ** tq
            if not (a < tt < b or (i == 0 and tt == T0f and T0f < roots[0])
                    or (i == n and tt == T1f and T1f > roots[-1])):
                continue
            z = float(ZF.Z(np.array([tt]))[0])
            if abs(z) < 1e-6:
                continue
            pos = z > 0
            eps = min(1e-3, abs(z) / 50)
            p = LIN.make_point(tn, tq, pos, eps, nl)
            ok, inf = LIN.pt_check(p, check_dir=False)
            if ok:
                pts.append(p)
                info.append({"t": tt, "Z": z, "N": p.N, "val": inf["val"], "err": inf["err"], "m": p.m})
                done = True
                break
        if not done:
            raise RuntimeError("band %d: no certifiable point in (%g, %g)" % (band["i"], a, b))
    T0n, T0d, T1n, T1d = T0.numerator, T0.denominator, T1.numerator, T1.denominator
    assert LIN.band_ok(T0n, T0d, T1n, T1d, n, pts), band["i"]
    return pts, info


# ------------------------------------------------------------------ Lean helpers

def qc(x):
    """(Q expression, proof of `(Q expr).val = <the Lean real literal of x>`) for a positive rational
    written as in the band tables: `(41 : ℝ)` / `(1 : ℝ)` / `(965 / 4 : ℝ)`."""
    x = Fr(x)
    if x.denominator == 1:
        if x.numerator == 1:
            return "(Q.ofNat 1)", "Q.cv_one"
        assert x.numerator >= 2
        return "(Q.ofNat %d)" % x.numerator, "(Q.cv_nat %d)" % x.numerator
    assert x.numerator >= 2 and x.denominator >= 2
    return "(Q.frac %d %d)" % (x.numerator, x.denominator), "(Q.cv_frac %d %d)" % (x.numerator, x.denominator)


def qc_sub(x, y):
    (qx, px), (qy, py) = qc(x), qc(y)
    return "(Q.sub %s %s)" % (qx, qy), "(Q.cv_sub _ _ _ _ %s %s)" % (px, py)


def qc_add(x, y):
    (qx, px), (qy, py) = qc(x), qc(y)
    return "(Q.add %s %s)" % (qx, qy), "(Q.cv_add _ _ _ _ %s %s)" % (px, py)

def fr_plain(x):
    x = Fr(x)
    return "%d" % x.numerator if x.denominator == 1 else "%d / %d" % (x.numerator, x.denominator)


def lower_forms(T0, cap):
    return "((%s : ℝ) - %s)" % (fr_plain(T0), fr_plain(cap)), "(%s : ℝ)" % fr_plain(T0)


def upper_forms(T1, cap):
    return "(%s : ℝ)" % fr_plain(T1), "((%s : ℝ) + %s)" % (fr_plain(T1), fr_plain(cap))


def slab_tag(kind, T):
    T = Fr(T)
    return "%s%s" % (kind, "%d" % T.numerator if T.denominator == 1 else "%d_%d" % (T.numerator, T.denominator))


def header(title, body, imports):
    L = ["/-  %s" % title]
    L += ["    " + ln if ln else "" for ln in body]
    L.append("    conjecture1_proved = False.  Finite verification up to a fixed height only.")
    L.append("-/")
    L += ["import %s" % m for m in imports]
    return L


def chunks(xs, k):
    return [xs[i:i + k] for i in range(0, len(xs), k)]


# ------------------------------------------------------------------ files

def emit_edges_file(H, k, edges, outdir, ns):
    mod = "Arb4_H%dEdges_%d" % (H, k)
    L = header("%s.lean -- lane Arb4: COMPACT kernel certificates of %d horizontal argument changes"
               % (mod, len(edges)),
               ["(GENERATED by ../Arb4_emit_seg.py; do not edit).  Each edge: the certificate data",
                "`Arb4.EdgeD` (pieces planned by emit_h1000_offline.plan_edge, unchanged) and ONE",
                "`decide +kernel` of `Arb4.edgeOK` (every octant piece with its evaluator run, the endpoint",
                "boxes, the corner slopes and the final pi / arctan inequalities), then `Arb4.edgeOK_sound`.",
                "Heights: %s." % ", ".join(str(e["T"]) for e in edges)],
               ["Arb4_Edge"])
    L += ["", "open Arb4 Arb4.Q", "", "namespace %s" % ns, ""]
    for e in edges:
        tag = A.edge_tag(e["T"])
        name = "E_%s" % tag
        L.append("/-- The edge `[2, -1] + i %s` (%d pieces, N = %d). -/" % (e["T"], len(e["pieces"]), e["N"]))
        L.append(A.edge_def(e, name))
        L.append("")
        L.append("theorem %s_ok : edgeOK %s = true := by decide +kernel" % (name, name))
        L.append("")
        L.append("/-- **The horizontal argument change at T = %s, hypothesis-free.** -/" % e["T"])
        L.append("theorem %s_hAH : DiffractionCore.argChangeHoriz riemannZeta %s 2 (-1) ∈" % (name, A.rl(e["T"])))
        L.append("    Set.Icc %s.Lo.val %s.Hi.val := by" % (name, name))
        L.append("  have h := edgeOK_sound %s %s_ok" % (name, name))
        L.append("  have hT : %s.T = %s := by" % (name, A.rl(e["T"])))
        L.append("    show ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) = %s" % (e["tn"], e["tq"], A.rl(e["T"])))
        L.append("    norm_num")
        L.append("  rw [hT] at h")
        L.append("  exact h")
        L.append("")
    L.append("end %s" % ns)
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    open(path, "w").write("\n".join(L))
    return mod, path


def emit_slabs_file(H, k, slabs, outdir, ns):
    mod = "Arb4_H%dSlabs_%d" % (H, k)
    rowed = any(len(slab_rows(sd)) > 1 for sd in slabs)
    body = ["(GENERATED by ../Arb4_emit_seg.py; do not edit).  Each slab: the certificate data",
            "`Arb4.SlabD` (cells planned by emit_h1000_offline.plan_slab, unchanged) and ONE",
            "`decide +kernel` of `Arb4.slabOK` (budget, Pochhammer bound, every cell with its evaluator",
            "run and rectangle geometry), then `Arb4.slabOK_sound`."]
    if rowed:
        body += ["A slab next to a zero on the line is cut into ROWS `[y_i, y_(i+1)]` (x-only cells per row,",
                 "Arb4_emit_seg.plan_slab_rows): one `Arb4.SlabD` and one `decide +kernel` per row, the rows",
                 "stacked by `Arb4.slabClear_join`."]
    body.append("Slabs: %s." % ", ".join(sd["tag"] + ("" if len(slab_rows(sd)) == 1 else " (%d rows)" % len(slab_rows(sd)))
                                        for sd in slabs))
    L = header("%s.lean -- lane Arb4: COMPACT kernel certificates of %d zero-free edge-clearance slabs"
               % (mod, len(slabs)), body, ["Arb4_Slab"] + (["Arb4_SlabRows"] if rowed else []))
    L += ["", "open Arb4 Arb4.Q", "", "namespace %s" % ns, ""]
    for sd in slabs:
        name = "S_%s" % sd["tag"]
        rows = slab_rows(sd)
        if len(rows) > 1:
            bq = [sd["lo_q"]] + [qc(r["b"])[0] for r in rows[:-1]] + [sd["hi_q"]]
            for j, r in enumerate(rows):
                assert r["a"] == (sd["a"] if j == 0 else rows[j - 1]["b"])
                r = dict(r)
                r["lo_q"], r["hi_q"] = bq[j], bq[j + 1]
                rn = "%s_r%d" % (name, j)
                L.append("/-- Row %d of %d of the slab `%s`: `(0, 1) x [%s, %s]` (%d cells, N = %d). -/"
                         % (j, len(rows), sd["tag"], r["a"], r["b"], len(A.slab_cells(r)), r["N"]))
                L.append(A.slab_def(r, rn))
                L.append("")
                L.append("theorem %s_ok : slabOK %s = true := by decide +kernel" % (rn, rn))
                L.append("")
                L.append("theorem %s_clear : EdgeClearGlue.SlabClear %s.val %s.val := slabOK_sound %s %s_ok"
                         % (rn, bq[j], bq[j + 1], rn, rn))
                L.append("")
            join = "%s_r0_clear" % name
            for j in range(1, len(rows)):
                join = "slabClear_join %s %s_r%d_clear" % (("(%s)" % join) if j > 1 else join, name, j)
            assert rows[-1]["b"] == sd["b"]
            L.append("/-- **The zero-free slab `SlabClear %s %s`, hypothesis-free** (%d rows). -/"
                     % (sd["alean"], sd["blean"], len(rows)))
            L.append("theorem %s_clear : EdgeClearGlue.SlabClear %s %s := by" % (name, sd["alean"], sd["blean"]))
            L.append("  have h := %s" % join)
            L.append("  have hlo : %s.val = %s := %s" % (bq[0], sd["alean"], sd["lo_cv"]))
            L.append("  have hhi : %s.val = %s := %s" % (bq[-1], sd["blean"], sd["hi_cv"]))
            L.append("  rw [hlo, hhi] at h")
            L.append("  exact h")
            L.append("")
            continue
        L.append("/-- The slab `(0, 1) x [%s, %s]` (%d cells, N = %d). -/" % (sd["a"], sd["b"], len(A.slab_cells(sd)), sd["N"]))
        L.append(A.slab_def(sd, name))
        L.append("")
        L.append("theorem %s_ok : slabOK %s = true := by decide +kernel" % (name, name))
        L.append("")
        L.append("/-- **The zero-free slab `SlabClear %s %s`, hypothesis-free.** -/" % (sd["alean"], sd["blean"]))
        L.append("theorem %s_clear : EdgeClearGlue.SlabClear %s %s := by" % (name, sd["alean"], sd["blean"]))
        L.append("  have h := slabOK_sound %s %s_ok" % (name, name))
        L.append("  have hlo : %s.lo.val = %s := %s" % (name, sd["alean"], sd["lo_cv"]))
        L.append("  have hhi : %s.hi.val = %s := %s" % (name, sd["blean"], sd["hi_cv"]))
        L.append("  rw [hlo, hhi] at h")
        L.append("  exact h")
        L.append("")
    L.append("end %s" % ns)
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    open(path, "w").write("\n".join(L))
    return mod, path


def ptd_lean(p):
    return "⟨%d, %d, %d, %d, %d, %d, %d, %d, %s⟩" % (p.tn, p.tq, p.N, p.Q, p.r, p.k, p.nl, p.m,
                                                  "true" if p.pos else "false")


def emit_lines_file(H, k, blist, outdir, ns, chunk=7):
    mod = "Arb4_H%dLines_%d" % (H, k)
    L = header("%s.lean -- lane Arb4: COMPACT on-line sign certificates of %d Turing bands" % (mod, len(blist)),
               ["(GENERATED by ../Arb4_emit_seg.py; do not edit).  Each band: its grid points `Arb4.PtD`",
                "(placed by the emit_h1000_line method; the evaluator states are NOT data, the kernel runs",
                "the evaluator once per point), split in chunks of %d points, ONE `decide +kernel` of" % chunk,
                "`Arb4.ptCheckC` per chunk, ONE `decide +kernel` of `H1000Line.bandOk` (order, edges,",
                "alternation) per band; `Arb4.bandC_sound` gives the band's verbatim hLine.",
                "Bands: %s." % ", ".join("%d [%s, %s] n = %d" % (b["i"], b["T0"], b["T1"], b["n"]) for b, _ in blist)],
               ["Arb4_Line"])
    L += ["", "open Arb4", "", "namespace %s" % ns, ""]
    for b, pts in blist:
        name = "B%02d" % b["i"]
        T0, T1 = b["T0"], b["T1"]
        L.append("/-! ### Band %d: [%s, %s], %d zeros, %d grid points -/" % (b["i"], T0, T1, b["n"], len(pts)))
        L.append("")
        parts = chunks(pts, chunk)
        for c, part in enumerate(parts):
            L.append("noncomputable def %s_%d : List PtD := [%s]" % (name, c, ",\n  ".join(ptd_lean(p) for p in part)))
            L.append("theorem %s_%d_ok : %s_%d.all (fun d => ptCheckC d.pt) = true := by decide +kernel" % (name, c, name, c))
        L.append("")
        L.append("noncomputable def %s : List PtD := %s" % (name, " ++ ".join("%s_%d" % (name, c) for c in range(len(parts)))))
        L.append("")
        L.append("theorem %s_band : H1000Line.bandOk %d %d %d %d %d (%s.map PtD.pt) = true := by decide +kernel" % (
            name, T0.numerator, T0.denominator, T1.numerator, T1.denominator, b["n"], name))
        L.append("")
        oks = "%s_0_ok" % name
        for c in range(1, len(parts)):
            oks = "(allC_append %s %s_%d_ok)" % (oks, name, c)
        L.append("/-- **hLine of band %d**: %d increasing zeros of `completedRiemannZeta` on the line in" % (b["i"], b["n"]))
        L.append("    `[%s, %s]`, kernel-checked, no hypotheses. -/" % (T0, T1))
        L.append("theorem %s_line : ∃ xs : List ℝ, xs.length = %d ∧ xs.IsChain (· < ·) ∧" % (name, b["n"]))
        L.append("    (∀ t ∈ xs, %s ≤ t ∧ t ≤ %s) ∧" % (A.rl(T0), A.rl(T1)))
        L.append("    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :=")
        L.append("  bandC_sound %s %s %d %d %d %d %d (by norm_num) (by norm_num) %s" % (
            A.rl(T0), A.rl(T1), T0.numerator, T0.denominator, T1.numerator, T1.denominator, b["n"], name))
        L.append("    (bandC_of %s %s_band)" % (oks, name))
        L.append("")
    L.append("end %s" % ns)
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    open(path, "w").write("\n".join(L))
    return mod, path


def gam_def(name, G):
    return "noncomputable def %s : GamD := ⟨%s, %s, %d, %s, %d, %d, %d, %d, %d⟩" % (
        name, qc(G["T"])[0], A.zl(G["k2"]), G["n2"], A.zl(G["km"]), G["nm"], G["md2"], G["N2"], G["mdm"], G["Nm"])


def prev_edge_emitted(outdir, H):
    """did the compact segment H - 1000 emit the edge at height H - 1000 (its top band ends there)?"""
    import glob
    P = H - 1000
    return any(("noncomputable def E_T%d : EdgeD where" % P) in open(f).read()
               for f in glob.glob(os.path.join(outdir, "Arb4_H%dEdges_*.lean" % P)))


def emit_capstone(H, cfg, bands, encl, gams, mods, outdir, ens, n_check):
    """the capstone module Arb4_h<H>."""
    mod = "Arb4_h%d" % H
    capns = "Arb4_h%d" % H
    seg_ns = cfg["seg_ns"]
    az = cfg["allzeros"]
    L = header("%s.lean -- lane Arb4: the height-%d ladder statement, HYPOTHESIS-FREE, from COMPACT"
               % (mod, H),
               ["certificates (GENERATED by ../Arb4_emit_seg.py; do not edit).",
                "",
                "    all_nontrivial_zeros_up_to_height_%d :" % H,
                "      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ %d → ρ.re = 1 / 2" % H,
                "",
                "Every input of the %d Turing bands of `%s.seg` (the band plan of `%s`) is" % (len(bands), seg_ns, az),
                "discharged in the kernel by ONE Boolean checker per certificate (lane Arb4):",
                "  * hLine: `Arb4.bandC` per band (`ptCheckC` chunks + `bandOk`; modules Arb4_H%dLines_*);" % H,
                "  * the edge-clearance slabs: `Arb4.slabOK` (Arb4_H%dSlabs_*)%s;" % (
                    H, "; band 0's lower slab is `H1000Line.slab0_band0` (height floor)" if H == 1000 else ""),
                "  * the horizontal argument changes: `Arb4.edgeOK` (Arb4_H%dEdges_*%s);" % (
                    H, "" if (H == 1000 or Fr(H - 1000) not in ens or not ens[Fr(H - 1000)].startswith("Arb4.H%d." % (H - 1000)))
                    else "; the edge at %d is Arb4_H%dEdges" % (H - 1000, H - 1000)),
                "  * K6a (`[-249/250, 249/250]`), K6b (`Arb4.k6B`: S2 / Sm1 brackets), the ball cover and the",
                "    pins of `Valid`: ONE `decide +kernel` of `Arb4.validB && Arb4.k6sideB` per band;",
                "  * hnzl, hnzb, hnzt, hins: K1 (`BandGlue.BandData.inputs_of_reduced`); hγ: `HeightFloor`.",
                "Composition: `Arb4.boxCert_of_parts` per band, then `%s`." % cfg["final_doc"],
                "Axioms [propext, Classical.choice, Quot.sound] (Arb4_AxiomGuard_h%d); no `sorry`." % H],
               ["Arb4_Seg", cfg["bandglue_mod"], "HeightFloor", "H1000Glue"] + cfg.get("extra_imports", []) + mods)
    L += ["", "open Complex Arb4 Arb4.Q", "", "namespace %s" % capns, ""]
    L.append("/-! ## The K6b certificates at the band edges -/")
    L.append("")
    for T in sorted(gams):
        L.append(gam_def("G_%s" % A.edge_tag(T), gams[T]))
    L.append("")
    for b in bands:
        i = b["i"]
        E = encl[i]
        T0, T1 = b["T0"], b["T1"]
        e1, e0 = ens[T1], ens[T0]
        L.append("/-! ### Band %d: `[%s, %s]`, %d zeros -/" % (i, T0, T1, b["n"]))
        L.append("")
        L.append("/-- The five enclosures of band %d: K6a, the edges at %s and %s, K6b. -/" % (i, T1, T0))
        L.append("noncomputable def E%d : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250, %s.Lo, %s.Hi, %s.Lo, %s.Hi,"
                 % (i, e1, e1, e0, e0))
        L.append("  %s, %s, %s, %s⟩" % (A.ql(E[6]), A.ql(E[7]), A.ql(E[8]), A.ql(E[9])))
        L.append("")
        L.append("theorem chk%d : (validB %s %s %s %s %d E%d && k6sideB G_%s G_%s E%d) = true := by decide +kernel"
                 % (i, qc(T0)[0], qc(T1)[0], qc(b["cim"])[0], qc(b["q"])[0], b["n"], i, A.edge_tag(T0),
                    A.edge_tag(T1), i))
        L.append("")
        L.append("theorem box%d : BandGlue.BoxCert (1 / 4000000) (3999999 / 4000000) (%s.bLo %d) (%s.bHi %d) := by"
                 % (i, az, i, az, i))
        L.append("  have hc := chk%d" % i)
        L.append("  rw [Bool.and_eq_true] at hc")
        L.append("  have hT0 : (%s.seg %d).T0 = %s.val := %s.symm" % (seg_ns, i, qc(T0)[0], qc(T0)[1]))
        L.append("  have hT1 : (%s.seg %d).T1 = %s.val := %s.symm" % (seg_ns, i, qc(T1)[0], qc(T1)[1]))
        L.append("  have hcc : (%s.seg %d).c = (⟨1 / 2, %s.val⟩ : ℂ) := by rw [%s]; rfl"
                 % (seg_ns, i, qc(b["cim"])[0], qc(b["cim"])[1]))
        L.append("  have hR : (%s.seg %d).R = Real.sqrt %s.val := by rw [%s]; rfl"
                 % (seg_ns, i, qc(b["q"])[0], qc(b["q"])[1]))
        L.append("  refine boxCert_of_parts (%s.seg %d) E%d (%s.seg_edge %d (by norm_num)).1" % (seg_ns, i, i, seg_ns, i))
        L.append("    (%s.seg_edge %d (by norm_num)).2 (valid_of_B _ _ _ _ _ E%d hT0 hT1 hcc hR hc.1)" % (seg_ns, i, i))
        L.append("    (%s.seg_geom %d (by norm_num)) ?_ ?_ ?_ (k6side_of_B _ G_%s G_%s E%d hT0 hT1 hc.2) ?_ ?_"
                 % (seg_ns, i, A.edge_tag(T0), A.edge_tag(T1), i))
        L.append("  · exact %s" % cfg["line_ref"](i))
        lo_ref = cfg["lower_slab_ref"](b)
        if lo_ref.startswith("H1000Line."):
            L.append("  · exact %s" % lo_ref)
        else:
            a_, b_ = lower_forms(T0, b["capLo"])
            L.append("  · show EdgeClearGlue.SlabClear %s %s" % (a_, b_))
            L.append("    exact %s" % lo_ref)
        a_, b_ = upper_forms(T1, b["capHi"])
        L.append("  · show EdgeClearGlue.SlabClear %s %s" % (a_, b_))
        L.append("    exact %s" % cfg["upper_slab_ref"](b))
        L.append("  · show DiffractionCore.argChangeHoriz riemannZeta %s 2 (-1) ∈ Set.Icc (%s.Lo).val (%s.Hi).val"
                 % (A.rl(T1), e1, e1))
        L.append("    exact %s_hAH" % e1)
        L.append("  · show DiffractionCore.argChangeHoriz riemannZeta %s 2 (-1) ∈ Set.Icc (%s.Lo).val (%s.Hi).val"
                 % (A.rl(T0), e0, e0))
        L.append("    exact %s_hAH" % e0)
        L.append("")
    L.append("/-- The segment's band hypothesis, kernel-checked. -/")
    L.append("theorem hbands : %s.BandHyp := by" % az)
    L.append("  intro i hi")
    L.append("  interval_cases i")
    for b in bands:
        L.append("  · exact (box%d).box" % b["i"])
    L.append("")
    L.append("/-- **Every nontrivial zero of ζ with `0 < Im ρ ≤ %d` lies on the critical line** -- kernel-checked," % H)
    L.append("    NO hypotheses (a finite verification; conjecture1_proved = False). -/")
    L.append("theorem all_nontrivial_zeros_up_to_height_%d :" % H)
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ %d → ρ.re = 1 / 2 :=" % H)
    L.append("  %s" % cfg["final_term"])
    L.append("")
    L.append("end %s" % capns)
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    open(path, "w").write("\n".join(L))
    return mod, path


def theorems_of(path):
    src = open(path).read()
    ns = re.findall(r"^namespace (\S+)", src, re.M)
    names = re.findall(r"^theorem (\S+)", src, re.M)
    return ["%s.%s" % (ns[0], n) if ns else n for n in names]


def emit_guard(H, paths, outdir, cap_mod):
    mod = "Arb4_AxiomGuard_h%d" % H
    L = ["/-  %s.lean -- lane Arb4: `#print axioms` of every theorem of the compact height-%d segment" % (mod, H),
         "    (GENERATED by ../Arb4_emit_seg.py).  Expected: every line within [propext, Classical.choice,",
         "    Quot.sound]; the `example` pins the capstone's statement (pure Mathlib, no binders).",
         "    conjecture1_proved = False.",
         "-/",
         "import %s" % cap_mod, ""]
    L.append("/-- The capstone has exactly the ladder conclusion and no hypotheses. -/")
    L.append("example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ %d → ρ.re = 1 / 2 :=" % H)
    L.append("  Arb4_h%d.all_nontrivial_zeros_up_to_height_%d" % (H, H))
    L.append("")
    n = 0
    for p in paths:
        for t in theorems_of(p):
            L.append("#print axioms %s" % t)
            n += 1
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    open(path, "w").write("\n".join(L))
    return mod, path, n


# ------------------------------------------------------------------ driver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seg", type=int, required=True)
    ap.add_argument("--outdir", default=os.path.join(HERE, "lean"))
    ap.add_argument("--json", default=None)
    ap.add_argument("--zeros", default=None)
    ap.add_argument("--edges-per-file", type=int, default=5)
    ap.add_argument("--slabs-per-file", type=int, default=10)
    ap.add_argument("--bands-per-file", type=int, default=5)
    ap.add_argument("--tq", type=int, default=10)
    ap.add_argument("--nl", type=int, default=48)
    ap.add_argument("--replan", action="store_true", help="ignore the plan cache")
    a = ap.parse_args()
    H = a.seg
    t_start = time.time()
    summ = dict(seg=H, conjecture1_proved=False)
    if H == 1000:
        bg_path = os.path.join(HERE, "lean", "BandGlue_h1000.lean")
        zeros = a.zeros or os.path.join(SCR, "a2_zeros.json")
        cfg = dict(seg_ns="BandGlue_h1000", allzeros="AllZeros_h1000", bandglue_mod="BandGlue_h1000",
                   final_doc="AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands",
                   final_term="AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands hbands "
                              "(HeightFloor.height_floor 1000)")
    elif H % 1000 == 0 and H >= 2000:
        P = H - 1000
        bg_path = os.path.join(HERE, "lean", "Arb4_BandGlue_h%d.lean" % H)
        zeros = a.zeros or (os.path.join(SCR, "arb4", "zeros2001.json") if H == 2000 else None)
        cfg = dict(seg_ns="Arb4.BandGlue_h%d" % H, allzeros="AllZeros_h%d" % H, bandglue_mod="Arb4_BandGlue_h%d" % H,
                   final_doc="AllZerosUpToHeight.height_chain (Arb4_h%d + AllZeros_h%d.segment_%d_%d)" % (P, H, P, H),
                   final_term="AllZerosUpToHeight.height_chain %d %d "
                              "Arb4_h%d.all_nontrivial_zeros_up_to_height_%d\n"
                              "    (AllZeros_h%d.segment_%d_%d hbands (HeightFloor.height_floor %d))"
                              % (P, H, P, P, H, P, H, H),
                   extra_imports=["Arb4_h%d" % P])
    else:
        sys.exit("unsupported segment")
    ns = "Arb4.H%d" % H
    bands = parse_bandglue(bg_path)
    assert [b["i"] for b in bands] == list(range(len(bands))) and len(bands) >= 1
    for b in bands:
        assert valid_ok(b), b["i"]
    zs = json.load(open(zeros)) if zeros else None
    heights = sorted(set([b["T0"] for b in bands] + [b["T1"] for b in bands]))
    reuse = {}
    if H >= 2000 and prev_edge_emitted(a.outdir, H):
        reuse[Fr(H - 1000)] = "Arb4.H%d.E_T%d" % (H - 1000, H - 1000)
    new_heights = [T for T in heights if T not in reuse]
    import pickle
    cache = os.path.join(SCR, "arb4", "plan_h%d.pkl" % H)
    plan = None
    if os.path.exists(cache) and not a.replan:
        plan = pickle.load(open(cache, "rb"))
        print("plan cache: %s" % cache, file=sys.stderr)
    # resumable planning: every planned edge / slab / band is saved at once to the partial cache
    partial_path = cache + ".partial"
    partial = dict(edges={}, slabs={}, lines={})
    if plan is None and os.path.exists(partial_path) and not a.replan:
        partial = pickle.load(open(partial_path, "rb"))
        print("partial plan cache: %d edges, %d slabs, %d bands" % tuple(len(partial[k]) for k in
              ("edges", "slabs", "lines")), file=sys.stderr)

    def save_partial():
        pickle.dump(partial, open(partial_path + ".tmp", "wb"))
        os.replace(partial_path + ".tmp", partial_path)
    # ---- edges
    t0 = time.time()
    edges = []
    for T in new_heights:
        if plan is not None:
            edges = plan["edges"]
            break
        if T in partial["edges"]:
            e = partial["edges"][T]
        else:
            e = OFF.edge_enclosure(OFF.plan_edge(T))
            partial["edges"][T] = e
            save_partial()
        edges.append(e)
    summ["edges"] = [dict(T=str(e["T"]), N=e["N"], pieces=len(e["pieces"]), Lo=str(e["Lv"]), Hi=str(e["Hv"]),
                          width=float(e["Hv"] - e["Lv"])) for e in edges]
    summ["edge_py_s"] = round(time.time() - t0, 1)
    ens = {e["T"]: "%s.E_%s" % (ns, A.edge_tag(e["T"])) for e in edges}
    ens.update(reuse)
    elo = {e["T"]: (e["Lv"], e["Hv"]) for e in edges}
    if Fr(H - 1000) in reuse:
        # the reused edge's enclosure (read back from the previous compact segment's modules)
        import glob
        P = H - 1000
        for f in sorted(glob.glob(os.path.join(a.outdir, "Arb4_H%dEdges_*.lean" % P))):
            src = open(f).read()
            m = re.search(r"noncomputable def E_T%d : EdgeD where.*?  Lo := \(Q\.frac \(?(-?\d+)\)? (\d+)\)\n"
                          r"  Hi := \(Q\.frac \(?(-?\d+)\)? (\d+)\)" % P, src, re.S)
            if m:
                elo[Fr(P)] = (Fr(int(m.group(1)), int(m.group(2))), Fr(int(m.group(3)), int(m.group(4))))
                break
        assert Fr(P) in elo, "previous segment's edge E_T%d not found" % P
    # ---- slabs
    t0 = time.time()
    slabs = []
    lower_ref, upper_ref = {}, {}
    for b in bands:
        i, T0, T1 = b["i"], b["T0"], b["T1"]
        specs = []
        if H == 1000 and i == 0:
            lower_ref[i] = "H1000Line.slab0_band0"
        else:
            a_, b_ = lower_forms(T0, b["capLo"])
            specs.append(("lo", slab_tag("L", T0), T0 - b["capLo"], T0, a_, b_))
        a_, b_ = upper_forms(T1, b["capHi"])
        specs.append(("hi", slab_tag("U", T1), T1, T1 + b["capHi"], a_, b_))
        for kind, tag, lo, hi, a_, b_ in specs:
            if plan is not None:
                sd = plan["slabs"][tag]
            elif tag in partial["slabs"]:
                sd = partial["slabs"][tag]
            else:
                # H <= 2000: plan_slab (never split in y there); H >= 3000: rows (see plan_slab_rows)
                sd = OFF.plan_slab(tag, lo, hi) if H <= 2000 else plan_slab_rowed(tag, lo, hi)
                partial["slabs"][tag] = sd
                save_partial()
            sd["alean"], sd["blean"] = a_, b_
            if kind == "lo":
                sd["lo_q"], sd["lo_cv"] = qc_sub(T0, b["capLo"])
                sd["hi_q"], sd["hi_cv"] = qc(T0)
            else:
                sd["lo_q"], sd["lo_cv"] = qc(T1)
                sd["hi_q"], sd["hi_cv"] = qc_add(T1, b["capHi"])
            slabs.append(sd)
            ref = "%s.S_%s_clear" % (ns, tag)
            (lower_ref if kind == "lo" else upper_ref)[i] = ref
    summ["slabs"] = [dict(tag=sd["tag"], N=sd["N"], rows=len(slab_rows(sd)), cells=slab_ncells(sd), F=str(sd["F"]))
                     for sd in slabs]
    summ["slab_py_s"] = round(time.time() - t0, 1)
    # ---- lines
    t0 = time.time()
    lines = []
    for b in bands:
        if plan is not None:
            pts = plan["lines"][b["i"]]
        elif b["i"] in partial["lines"]:
            pts = partial["lines"][b["i"]]
        else:
            pts, info = band_points(b, zs, a.tq, a.nl) if zs is not None else band_points_fast(b, a.tq, a.nl)
            for p in pts:
                ok, _ = LIN.pt_check(p, check_dir=True)
                assert ok, (b["i"], p.tn)
            partial["lines"][b["i"]] = pts
            save_partial()
        lines.append((b, pts))
        print("band %d: %d points (%.1fs)" % (b["i"], len(pts), time.time() - t0), file=sys.stderr, flush=True)
    summ["lines"] = [dict(i=b["i"], points=len(p), terms=sum(q.N for q in p)) for b, p in lines]
    if plan is None:
        pickle.dump(dict(edges=edges, slabs={sd["tag"]: sd for sd in slabs},
                         lines={b["i"]: p for b, p in lines}), open(cache, "wb"))
    summ["line_py_s"] = round(time.time() - t0, 1)
    # ---- K6b and pins
    gams = {T: gam_cert(T) for T in heights}
    encl, pins = {}, {}
    for b in bands:
        L4, H4, L5, H5 = k6_encl(gams[b["T0"]], gams[b["T1"]])
        L2, H2 = elo[b["T1"]]
        L3, H3 = elo[b["T0"]]
        E = (Fr(-249, 250), Fr(249, 250), L2, H2, L3, H3, L4, H4, L5, H5)
        ok, slo, shi = pin_ok(b["n"], E)
        assert ok, ("pin", b["i"], slo, shi)
        encl[b["i"]] = E
        pins[b["i"]] = (slo, shi)
    summ["pins"] = {str(k): v for k, v in pins.items()}
    # ---- files
    mods, paths = [], []
    for k, ch in enumerate(chunks(edges, a.edges_per_file)):
        m, p = emit_edges_file(H, k, ch, a.outdir, ns)
        mods.append(m); paths.append(p)
    for k, ch in enumerate(chunks(slabs, a.slabs_per_file)):
        m, p = emit_slabs_file(H, k, ch, a.outdir, ns)
        mods.append(m); paths.append(p)
    for k, ch in enumerate(chunks(lines, a.bands_per_file)):
        m, p = emit_lines_file(H, k, ch, a.outdir, ns)
        mods.append(m); paths.append(p)
    cfg["line_ref"] = lambda i: "%s.B%02d_line" % (ns, i)
    cfg["lower_slab_ref"] = lambda b: lower_ref[b["i"]]
    cfg["upper_slab_ref"] = lambda b: upper_ref[b["i"]]
    cap_mod, cap_path = emit_capstone(H, cfg, bands, encl, gams, mods, a.outdir, ens, None)
    g_mod, g_path, nthm = emit_guard(H, paths + [cap_path], a.outdir, cap_mod)
    summ["modules"] = mods + [cap_mod, g_mod]
    summ["guard_theorems"] = nthm
    summ["py_seconds"] = round(time.time() - t_start, 1)
    summ["total_pieces"] = sum(len(e["pieces"]) for e in edges)
    summ["total_cells"] = sum(s["cells"] for s in summ["slabs"])
    summ["total_points"] = sum(l["points"] for l in summ["lines"])
    if a.json:
        json.dump(summ, open(a.json, "w"), indent=1)
    print(json.dumps({k: summ[k] for k in ["modules", "total_pieces", "total_cells", "total_points",
                                           "guard_theorems", "py_seconds"]}))


if __name__ == "__main__":
    main()
