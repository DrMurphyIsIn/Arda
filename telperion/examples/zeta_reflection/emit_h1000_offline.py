"""Emit the kernel-checked OFF-LINE inputs of the 25 bands of the height-1000 segment (lane h1000-integrate).

usage: emit_h1000_offline.py [--outdir DIR] [--json FILE] [--only-edges T,T,...] [--only-slabs TAG,...]

What remains of the band inputs after lanes h1000-prep (hLine), offline (evaluator + one slab) and argch
(K6a/K6b/K6c) is
  * 27 horizontal argument changes `argChangeHoriz riemannZeta T 2 (-1)` at the band edges
    T in {1, 41, ..., 201, 241, 965/4, 281, ..., 481, 520, ..., 1000};
  * 48 edge-clearance slabs `EdgeClearGlue.SlabClear a b` (band 0's lower slab is H1000Glue.slab0_band0,
    band 24's upper slab is the offline lane's EMZetaOfflineSlab_T1000);
  * the 25 pins of the re-parametrised bands.

For every edge T this script builds an octant certificate for `ArgHoriz.hAH_of_octCert_boxes`:
pieces [x_{j+1}, x_j] of [-1, 2] (x_0 = 2, x_m = -1), one octant label per piece, and for each piece ONE
run of the off-line evaluator (lean/EMZetaOfflineEval.lean, mirrored bit-exactly by
arbecon/offline_model.py) at the piece center with 6 accumulators, and ONE kernel check
`H1000Oct.checkOct` (mirrored exactly below) certifying `0 < octX k zeta(x + iT)` on the whole piece via
`H1000Oct.piece_octX_pos`.  The first and last piece centers are x = 2 and x = -1; their k = 0
accumulators give the two endpoint point enclosures through `ArbEcon.Off.checkG` (mirrored in
arbecon/gen_offline.py).  The script REFUSES to emit a failing check.

For every slab it covers [1/2, 1] x [a, b] (the reflection covers (0, 1/2)) by cells, each with ONE
evaluator run and ONE `ArbEcon.Off.checkCell` (mirrored in arbecon/gen_offline_slab.py), assembled by
`H1000Oct.cell_zeta_ne_zero_R`; failing cells are split.

Output (OUTDIR, default ./lean): H1000Edge_<tag>.lean (27), H1000Slab_<tag>.lean (48),
AllZerosKernel_h1000.lean (the capstone), AxiomGuardAllZerosKernel_h1000.lean (the guard).
Numerical side conditions with small rationals are closed by `norm_num`; the evaluator runs and the
piece / cell / point checks by `decide +kernel`.  conjecture1_proved = False.
"""
import json
import math
import os
import re
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "arbecon"))
import arbecon_model as M  # noqa: E402
import offline_model as O  # noqa: E402
import gen_offline as G  # noqa: E402
import gen_offline_slab as GS  # noqa: E402

KEM = 6          # EM order 2K + 1 = 13
PT = 5           # Taylor order p (p + 1 = 6 accumulators)
PREC = 64
TWO64 = 2 ** 64
LBETA = G.LBETA
CP5 = Fr(PT + 2, math.factorial(PT + 1) * (PT + 1))
CK6 = Fr(84107, 10 ** 15)      # H1000Oct.CK_six_le
PI_LO, PI_HI = Fr(3141592, 10 ** 6), Fr(3141593, 10 ** 6)   # Real.pi_gt_d6 / pi_lt_d6

OA = [1, 1, 0, -1, -1, -1, 0, 1]
OB = [0, 1, 1, 1, 0, -1, -1, -1]


def octA(k):
    return OA[k % 8]


def octB(k):
    return OB[k % 8]


# ------------------------------------------------------------------ band table (BandGlue_h1000)

def parse_bands():
    src = open(os.path.join(HERE, "lean", "BandGlue_h1000.lean")).read()
    seg = src[src.index("noncomputable def seg"):src.index("noncomputable def capLo")]
    rows = re.findall(r"\| (\d+) => ⟨(.*?),\n", seg)
    bands = []
    for i, body in rows:
        parts = [p.strip() for p in split_top(body)]
        T0, T1, n = parse_num(parts[0]), parse_num(parts[1]), int(parts[2])
        bands.append((int(i), T0, T1, n))

    def table(name):
        blk = src[src.index("noncomputable def %s" % name):]
        blk = blk[:blk.index("| _ =>")]
        return {int(i): parse_num(v) for i, v in re.findall(r"\| (\d+) => (\(.*?\))\n", blk)}
    return bands, table("capLo"), table("capHi")


def split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return out


def parse_num(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    s = s.replace(" : ℝ", "")
    if "/" in s:
        a, b = s.split("/")
        return Fr(int(a.strip()), int(b.strip()))
    return Fr(int(s))


def parse_k6b():
    src = open(os.path.join(HERE, "lean", "ArgChangeH1000.lean")).read()
    out = {}
    for name in ["L4t", "H4t", "L5t", "H5t"]:
        blk = src[src.index("noncomputable def %s" % name):]
        blk = blk[:blk.index("| _ =>")]
        out[name] = {int(i): Fr(int(a), int(b)) for i, a, b in
                     re.findall(r"\| (\d+) => \((\d+) / (\d+) : ℝ\)", blk)}
    return out


# ------------------------------------------------------------------ Lean literals

def rl(x):
    """a rational as a Lean real literal"""
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)


def tl(x):
    """a height as it appears in BandGlue_h1000.seg ((41 : ℝ), (965 / 4 : ℝ))"""
    return rl(x)


def zl(k):
    return "(%d : ℤ)" % k


# ------------------------------------------------------------------ exact mirrors

def oct_lo(al, be, d):
    return al * d[0] + be * d[1] - (abs(al) * d[2] + abs(be) * d[3])


def oct_up(al, be, d):
    return abs(al * d[0] + be * d[1]) + abs(al) * d[2] + abs(be) * d[3]


def sum_oct(al, be, BreN, BimN, BD, rn, rd, p, k, ys1, ys2):
    s = 0
    for j, (x1, x2) in enumerate(zip(ys1, ys2)):
        kk = k + j
        s += (oct_up(al, be, GS.w_data(BreN, BimN, BD, x1, x2)) * rn ** kk * rd ** max(p - kk, 0)
              * (math.factorial(p) // math.factorial(kk)))
    return s


def check_oct(c, o, K, N, p, xs1, xs2, rn, rd, FN, FD, kk):
    x1, ys1 = xs1[0], list(xs1[1:])
    x2, ys2 = xs2[0], list(xs2[1:])
    BreN, BimN, BD = G.corr_data_g(K, o.a - o.b, o.q, 2 ** c.tq, c.tn, N)
    al, be = octA(kk), octB(kk)
    rhs = (sum_oct(al, be, BreN, BimN, BD, rn, rd, p, 1, ys1, ys2) * FD
           + (abs(al) + abs(be)) * FN * 2 ** c.P * BD * rd ** p * math.factorial(p))
    lhs = oct_lo(al, be, GS.w_data(BreN, BimN, BD, x1, x2)) * (rd ** p * math.factorial(p) * FD)
    ok = (1 <= K <= 6 and 2 <= N and 1 <= rd and 1 <= FD and 1 <= o.q and 1 <= c.tn
          and len(ys1) == p and len(ys2) == p and rhs < lhs)
    scale = 2 ** c.P * BD * rd ** p * math.factorial(p) * FD
    return ok, float(Fr(lhs - rhs, scale))


def w0_center(c, o, K, N, xs1, xs2):
    BreN, BimN, BD = G.corr_data_g(K, o.a - o.b, o.q, 2 ** c.tq, c.tn, N)
    d = GS.w_data(BreN, BimN, BD, xs1[0], xs2[0])
    sc = Fr(1, 2 ** c.P * BD)
    return complex(float(d[0] * sc), float(d[1] * sc))


# ------------------------------------------------------------------ evaluator runs

CFG = {}


def cfg_of(tn, tq):
    if (tn, tq) not in CFG:
        CFG[(tn, tq)] = M.make_cfg(PREC, tn, tq, lnbig=256, sqbig=256)
    return CFG[(tn, tq)]


def abq(sig):
    sig = Fr(sig)
    if sig >= 0:
        return sig.numerator, 0, sig.denominator
    return 0, -sig.numerator, sig.denominator


def run_center(tn, tq, sig, N, p):
    c = cfg_of(tn, tq)
    a, b, q = abq(sig)
    o = O.make_ocfg(c, a, b, q)
    s = O.init_state(c, p)
    fails = 0
    for _ in range(N - 2):
        if not O.ampl_ok(c, o, s.n + 1, s.g):
            fails += 1
        s = O.step(c, o, s)
    s1 = s
    if not O.ampl_ok(c, o, s1.n + 1, s1.g):
        fails += 1
    sN = O.step(c, o, s1)
    assert fails == 0 and s1.n == N - 1 and sN.n == N, "evaluator fallback"
    return c, o, s1, sN


# ------------------------------------------------------------------ exact budgets

def betaA(i):
    return abs(G.betaN(i))


def emcB(N, a, U):
    return Fr(N) / a + Fr(1, 2) + sum(Fr(betaA(i), LBETA) * U ** (i + 1) / Fr(N) ** (i + 1)
                                      for i in range(2 * KEM - 1))


def corrVar(N, R, a, U):
    return Fr(N) * R / a ** 2 + sum(Fr(betaA(i), LBETA) * ((U + R) ** (i + 1) - U ** (i + 1)) / Fr(N) ** (i + 1)
                                    for i in range(2 * KEM - 1))


def poch_norm_sq(sig, t, k):
    p = Fr(1)
    for j in range(k):
        p *= (sig + j) ** 2 + t * t
    return p


def ceil_sqrt_int(x):
    """smallest integer Q >= 0 with Q^2 >= x (x a Fraction)"""
    q = math.isqrt(math.ceil(x))
    while q * q < x:
        q += 1
    return q


def round_up_sig(n, digits=4):
    """round the positive integer n up to `digits` significant decimal digits"""
    if n < 10 ** digits:
        return n
    e = len(str(n)) - digits
    return -(-n // 10 ** e) * 10 ** e


def rpow_cert(N, a, b, q, Rd):
    """smallest Rn with Rd^q N^b <= Rn^q N^a"""
    lhs = Rd ** q * N ** b
    guess = max(1, int(Rd * float(N) ** (-(a - b) / q)) - 2)
    Rn = guess
    while Rn ** q * N ** a < lhs:
        Rn += 1
    while Rn > 1 and (Rn - 1) ** q * N ** a >= lhs:
        Rn -= 1
    return Rn


def floor_to(x, den):
    return Fr(math.floor(x * den), den)


def ceil_to(x, den):
    return Fr(math.ceil(x * den), den)


def nice_up(x, rel=Fr(1, 1000)):
    """a rational >= x (1 + rel) with a short decimal expansion"""
    y = x * (1 + rel)
    den = 10
    while True:
        z = ceil_to(y, den)
        if z <= x * (1 + 2 * rel):
            return z
        den *= 10


# ------------------------------------------------------------------ one octant piece

def piece_data(T, tn, tq, N, L, sig, r, kk, run):
    c, o, s1, sN = run
    d2 = (sig - 1) ** 2 + T * T
    a = floor_to(Fr(math.sqrt(float(d2))) - r, 1000) - Fr(1, 1000)
    assert a > 0 and (a + r) ** 2 <= d2
    U = Fr(ceil_sqrt_int((abs(sig) + 2 * KEM - 1) ** 2 + T * T))
    if sig >= 0:
        Gv, gd = Fr(1), None
    else:
        xm = floor_to(sig, 16)
        gb = int(-xm * 16)
        Gd = 2 ** 20
        Gn = rpow_cert(N, 0, gb, 16, Gd)
        Gv, gd = Fr(Gn, Gd), (gb, Gn, Gd, xm)
    xlo = floor_to(sig - r, 16)
    xhi = sig + r
    sigs = max(xhi, -xlo)
    ea, eb = (int(xlo * 16), 0) if xlo >= 0 else (0, int(-xlo * 16))
    Rd = 2 ** 20
    Rn = rpow_cert(N, ea, eb, 16, Rd)
    Qr = round_up_sig(ceil_sqrt_int(poch_norm_sq(sigs, T, 2 * KEM + 1)))
    E = nice_up(CK6 * Qr * Fr(Rn, Rd) / Fr(N) ** (2 * KEM) / (xlo + 2 * KEM))
    B = Gv * (CP5 * (r * L) ** (PT + 1) * ((N - 1) + emcB(N, a, U)) + 3 * corrVar(N, r, a, U)) + E
    F = nice_up(B)
    rn, rd = r.numerator, r.denominator
    ok, margin = check_oct(c, o, KEM, N, PT, s1.acc, sN.acc, rn, rd, F.numerator, F.denominator, kk)
    return ok, dict(sig=sig, r=r, kk=kk, a=a, U=U, G=Gv, gd=gd, xlo=xlo, xhi=xhi, sigs=sigs, ea=ea, eb=eb,
                    Rn=Rn, Rd=Rd, Qr=Qr, E=E, F=F, margin=margin, o=o, s1=s1, sN=sN)


def best_oct(w, kprev):
    ang = math.atan2(w.imag, w.real)
    k = round(ang / (math.pi / 4))
    if kprev is not None:
        while k - kprev > 4:
            k -= 8
        while kprev - k > 4:
            k += 8
    return k


RLIST = [Fr(1, 2 ** e) for e in range(2, 9)]


def choose_N(T):
    if T <= 2:
        return 3
    return max(8, int(math.ceil(0.3 * float(T))))


def plan_edge(T):
    T = Fr(T)
    tq = 0
    while (T * 2 ** tq).denominator != 1:
        tq += 1
    tn = int(T * 2 ** tq)
    N = choose_N(T)
    c = cfg_of(tn, tq)
    s_probe = O.init_state(c, PT)
    # L from the log bracket at n = N (independent of sigma)
    _, _, _, sN0 = run_center(tn, tq, Fr(2), N, PT)
    L = ceil_to(Fr(sN0.lhi, TWO64), 1000)
    pieces = []
    x = Fr(2)
    kprev = None
    first = True
    while True:
        placed = False
        # try to finish with a piece centred at -1
        if not first and x + 1 <= RLIST[0]:
            rr = x + 1
            run = run_center(tn, tq, Fr(-1), N, PT)
            w = w0_center(run[0], run[1], KEM, N, run[2].acc, run[3].acc)
            kk = best_oct(w, kprev)
            if abs(kk - kprev) <= 3 and rr * L <= 1:
                ok, pd = piece_data(T, tn, tq, N, L, Fr(-1), rr, kk, run)
                if ok:
                    pd.update(lo=Fr(-1), hi=x)
                    pieces.append(pd)
                    x = Fr(-1)
                    break
        for r in RLIST:
            if r * L > 1:
                continue
            sig = x if first else x - r
            lo = x - r if first else x - 2 * r
            if lo <= -1:
                continue      # the last piece is always the one centred at x = -1
            run = run_center(tn, tq, sig, N, PT)
            w = w0_center(run[0], run[1], KEM, N, run[2].acc, run[3].acc)
            kk = best_oct(w, kprev)
            if kprev is not None and abs(kk - kprev) > 3:
                continue
            ok, pd = piece_data(T, tn, tq, N, L, sig, r, kk, run)
            if ok:
                pd.update(lo=lo, hi=x)
                pieces.append(pd)
                kprev = kk
                x = lo
                first = False
                placed = True
                break
        if not placed:
            raise RuntimeError("edge T=%s: no piece fits at x=%s" % (T, x))
    return dict(T=T, tn=tn, tq=tq, N=N, L=L, pieces=pieces)


def endpoint_box(T, tn, tq, N, pd, D=10 ** 9, Rd=2 ** 32):
    """checkG point enclosure at the piece center (x = 2 or x = -1)."""
    c, o = cfg_of(tn, tq), pd["o"]
    u = 2 ** tq
    Qp, Rn = G.cert_Q_R(KEM, o.a, o.b, o.q, u, tn, N, Rd)
    ok, EN, ED = G.rem_odd_g(KEM, o.a, o.b, o.q, u, tn, N, Qp, Rn, Rd)
    assert ok
    x1, x2 = pd["s1"].acc[0], pd["sN"].acc[0]
    reLo, reHi, imLo, imHi, info = G.bounds(PREC, tq, tn, KEM, o.a - o.b, o.q, N, x1, x2, D, EN, ED)
    assert G.check_core_g(PREC, tq, tn, KEM, o.a - o.b, o.q, N, x1, x2, D, reLo, reHi, imLo, imHi, EN, ED)
    return dict(Qp=Qp, Rn=Rn, Rd=Rd, D=D, reLo=reLo, reHi=reHi, imLo=imLo, imHi=imHi,
                a0=Fr(reLo, D), a1=Fr(reHi, D), b0=Fr(imLo, D), b1=Fr(imHi, D))


def slopes(box, kk):
    al, be = octA(kk), octB(kk)
    qs = []
    for a in (box["a0"], box["a1"]):
        for b in (box["b0"], box["b1"]):
            X = al * a + be * b
            Y = al * b - be * a
            assert X > 0, "endpoint box not in the octant half-plane"
            qs.append(Y / X)
    qlo = floor_to(min(qs), 10 ** 6)
    qhi = ceil_to(max(qs), 10 ** 6)
    return qlo, qhi


def atan_lo(q):
    return q - q ** 3 / 3 if q >= 0 else q


def atan_hi(q):
    return q if q >= 0 else q - q ** 3 / 3


def edge_enclosure(e):
    p0, pm = e["pieces"][0], e["pieces"][-1]
    assert p0["sig"] == 2 and p0["hi"] == 2 and pm["sig"] == -1 and pm["lo"] == -1
    for u, v in zip(e["pieces"], e["pieces"][1:]):
        assert u["lo"] == v["hi"] and abs(u["kk"] - v["kk"]) <= 3
    for u in e["pieces"]:
        assert abs(u["hi"] - u["sig"]) <= u["r"] and abs(u["lo"] - u["sig"]) <= u["r"] and u["lo"] < u["hi"]
    b0 = endpoint_box(e["T"], e["tn"], e["tq"], e["N"], p0)
    b1 = endpoint_box(e["T"], e["tn"], e["tq"], e["N"], pm)
    q0 = slopes(b0, p0["kk"])
    q1 = slopes(b1, pm["kk"])
    dk = pm["kk"] - p0["kk"]
    pil, pih = (PI_LO, PI_HI) if dk >= 0 else (PI_HI, PI_LO)
    Lv = floor_to(dk * pil / 4 + atan_lo(q1[0]) - atan_hi(q0[1]), 10 ** 6) - Fr(1, 10 ** 6)
    Hv = ceil_to(dk * pih / 4 + atan_hi(q1[1]) - atan_lo(q0[0]), 10 ** 6) + Fr(1, 10 ** 6)
    e.update(box0=b0, box1=b1, q0=q0, q1=q1, Lv=Lv, Hv=Hv)
    return e


# ------------------------------------------------------------------ slabs

def check_cell_exact(c, o, N, xs1, xs2, rn, rd, F):
    return GS.check_cell(c, o, KEM, N, PT, list(xs1), list(xs2), rn, rd, F.numerator, F.denominator)


def slab_N(b):
    return max(8, int(math.ceil(0.3 * float(b))))


def plan_slab(tag, a, b, J0=3, tq=14):
    a, b = Fr(a), Fr(b)
    N = slab_N(b)
    U = Fr(ceil_sqrt_int(Fr(2 * KEM) ** 2 + b * b))
    Qr = round_up_sig(ceil_sqrt_int(poch_norm_sq(Fr(1), b, 2 * KEM + 1)))
    r0 = math.isqrt(N)
    E = CK6 * Qr / (Fr(N) ** (2 * KEM) * r0) / (2 * KEM + Fr(1, 2))

    def cell_geom(xl, xr, yl, yh):
        sig = (xl + xr) / 2
        tc = Fr(round((yl + yh) / 2 * 2 ** tq), 2 ** tq)
        w = (xr - xl) / 2
        hh = max(tc - yl, yh - tc)
        rd = 10000
        rn = math.isqrt(int((w * w + hh * hh) * rd * rd)) + 1
        while Fr(rn, rd) ** 2 < w * w + hh * hh:
            rn += 1
        return sig, tc, w, hh, rn, rd

    # the budget radius: the root cells
    root = [(Fr(1, 2) + Fr(j, 2 * J0), Fr(1, 2) + Fr(j + 1, 2 * J0), a, b) for j in range(J0)]
    R = max(Fr(cell_geom(*cl)[4], cell_geom(*cl)[5]) for cl in root)
    _, _, _, sN0 = run_center(round(a * 2 ** tq), tq, Fr(3, 4), N, PT)
    L = ceil_to(Fr(sN0.lhi, TWO64), 1000)
    assert R * L <= 1
    B = CP5 * (R * L) ** (PT + 1) * ((N - 1) + emcB(N, a, U)) + 3 * corrVar(N, R, a, U) + E
    F = nice_up(B, Fr(1, 100))

    def solve(xl, xr, yl, yh, depth):
        sig, tc, w, hh, rn, rd = cell_geom(xl, xr, yl, yh)
        tn = int(tc * 2 ** tq)
        run = run_center(tn, tq, sig, N, PT)
        c, o, s1, sN = run
        ok, margin = check_cell_exact(c, o, N, s1.acc, sN.acc, rn, rd, F)
        if ok:
            return dict(leaf=True, xl=xl, xr=xr, yl=yl, yh=yh, sig=sig, tc=tc, tn=tn, w=w, hh=hh, rn=rn, rd=rd,
                        o=o, s1=s1, sN=sN, margin=margin)
        assert depth < 8, "slab %s: cell does not certify" % tag
        if (xr - xl) >= (yh - yl):
            xm = (xl + xr) / 2
            return dict(leaf=False, axis="x", m=xm, lo=solve(xl, xm, yl, yh, depth + 1),
                        hi=solve(xm, xr, yl, yh, depth + 1))
        ym = (yl + yh) / 2
        return dict(leaf=False, axis="y", m=ym, lo=solve(xl, xr, yl, ym, depth + 1),
                    hi=solve(xl, xr, ym, yh, depth + 1))

    trees = [solve(*cl, 0) for cl in root]
    return dict(tag=tag, a=a, b=b, N=N, U=U, Qr=Qr, r0=r0, E=E, R=R, L=L, F=F, root=root, trees=trees, tq=tq)


def leaves(t):
    if t["leaf"]:
        return [t]
    return leaves(t["lo"]) + leaves(t["hi"])


# ------------------------------------------------------------------ Lean emission helpers

def nl(n):
    return "((%d : ℕ) : ℝ)" % n


def cfg_term(tn, tq):
    return "(ArbEcon.OrderK.cfg64 %d %d)" % (tn, tq)


def emit_run(Lines, pre, cfgt, o, s1, sN, N, p):
    """data defs are emitted separately; this emits chunk theorems + invariants"""
    pass


def edge_tag(T):
    T = Fr(T)
    if T.denominator == 1:
        return "T%d" % T.numerator
    return "T%d_%d" % (T.numerator, T.denominator)


def emit_edge(e, outdir):
    T, tn, tq, N, Lval = e["T"], e["tn"], e["tq"], e["N"], e["L"]
    tag = edge_tag(T)
    ns = "H1000Edge.%s" % tag
    cfgt = cfg_term(tn, tq)
    Tl = tl(T)
    ps = e["pieces"]
    m = len(ps)
    L = []
    L.append("/-  H1000Edge_%s.lean -- the horizontal argument change of zeta along [2, -1] + i T, T = %s," % (tag, T))
    L.append("    KERNEL-CHECKED (lane h1000-integrate; GENERATED by ../emit_h1000_offline.py; do not edit).")
    L.append("")
    L.append("    An octant certificate (`ArgHoriz.OctCert`) with %d pieces [x_{j+1}, x_j] of [-1, 2]; piece j is" % m)
    L.append("    certified by ONE run of the off-line evaluator at its center (N = %d terms, 6 accumulators," % N)
    L.append("    `decide +kernel`) and ONE `H1000Oct.checkOct` (`decide +kernel`), assembled by")
    L.append("    `H1000Oct.piece_octX_pos` (order-13 Euler-Maclaurin Taylor model + remainder).  The endpoint")
    L.append("    enclosures at x = 2 and x = -1 are `ArbEcon.Off.checkG` runs on the first and last piece centers.")
    L.append("    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) then gives")
    L.append("        argChangeHoriz riemannZeta %s 2 (-1) ∈ [%s, %s]." % (T, e["Lv"], e["Hv"]))
    L.append("    conjecture1_proved = False.  One edge of a finite zero count; nothing about RH.")
    L.append("-/")
    L.append("import H1000Octant")
    L.append("")
    L.append("open Complex ZetaReflection ZetaReflection.EMHigh")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    for j, pd in enumerate(ps):
        o = pd["o"]
        L.append("def oc%d : ArbEcon.Off.OCfg := ⟨%d, %d, %d, %d, %d⟩" % (j, o.a, o.b, o.q, o.oneQ, o.nfuel))
        L.append("def s%d_1 : ArbEcon.Off.StO := %s" % (j, O.st_lean(pd["s1"])))
        L.append("def s%d_N : ArbEcon.Off.StO := %s" % (j, O.st_lean(pd["sN"])))
    L.append("")
    L.append("/-- The breakpoints `2 = x_0 > x_1 > … > x_m = -1`. -/")
    L.append("def pts : ℕ → ℝ := fun j => match j with")
    for j, pd in enumerate(ps):
        L.append("  | %d => %s" % (j, rl(pd["hi"])))
    L.append("  | _ => (-1 : ℝ)")
    L.append("/-- The octant labels (a continuous lift of the argument, in units of π/4). -/")
    L.append("def labs : ℕ → ℤ := fun j => match j with")
    for j, pd in enumerate(ps):
        L.append("  | %d => %d" % (j, pd["kk"]))
    L.append("  | _ => 0")
    L.append("/-- The octant certificate. -/")
    L.append("def cert : ArgHoriz.OctCert := ⟨%d, pts, labs⟩" % m)
    L.append("")
    L.append("end")
    L.append("")
    L.append("theorem ht : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (Tl, tn, tq))
    L.append("theorem valid : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht" % (cfgt, Tl, tn, tq))
    L.append("")
    for j, pd in enumerate(ps):
        o, sig, r = pd["o"], pd["sig"], pd["r"]
        rn, rd = r.numerator, r.denominator
        F = pd["F"]
        sl = rl(sig)
        L.append("/-! ### Piece %d: center %s, radius %s, octant %d -/" % (j, sig, r, pd["kk"]))
        L.append("")
        L.append("theorem chunk%d_1 : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d %d (ArbEcon.Off.StO.init %s 5)) s%d_1 = true := by" % (j, cfgt, j, N - 2, cfgt, j))
        L.append("  decide +kernel")
        L.append("theorem chunk%d_N : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d 1 s%d_1) s%d_N = true := by" % (j, cfgt, j, j, j))
        L.append("  decide +kernel")
        L.append("theorem check%d : H1000Oct.checkOct %s oc%d 6 %d 5 s%d_1.acc s%d_N.acc %d %d %d %d %s = true := by" % (j, cfgt, j, N, j, j, rn, rd, F.numerator, F.denominator, zl(pd["kk"])))
        L.append("  decide +kernel")
        L.append("theorem hσ%d : %s = (((%d : ℕ) : ℝ) - ((%d : ℕ) : ℝ)) / ((%d : ℕ) : ℝ) := by norm_num" % (j, sl, o.a, o.b, o.q))
        L.append("theorem ovalid%d : ArbEcon.Off.OValid %s oc%d %s := ⟨by decide +kernel, by decide, hσ%d⟩" % (j, cfgt, j, sl, j))
        L.append("theorem inv%d_1 : ArbEcon.Off.InvO %s %s %s (%d - 1) s%d_1 :=" % (j, cfgt, sl, Tl, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid ovalid%d %d 1 (ArbEcon.Off.StO.init %s 5) s%d_1" % (j, j, N - 2, cfgt, j))
        L.append("    (ArbEcon.Off.initO_sound _ _ _ 5 valid.one_eq) chunk%d_1" % j)
        L.append("theorem inv%d_N : ArbEcon.Off.InvO %s %s %s %d s%d_N :=" % (j, cfgt, sl, Tl, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid ovalid%d 1 %d s%d_1 s%d_N inv%d_1 chunk%d_N" % (j, j, N - 1, j, j, j, j))
        # G
        if pd["gd"] is None:
            Gl = "(1 : ℝ)"
            L.append("theorem hG%d : ∀ n : ℕ, 1 ≤ n → n ≤ %d → ‖(n : ℂ) ^ (-ArbEcon.Off.sOfG %s %s)‖ ≤ %s :=" % (j, N, sl, Tl, Gl))
            L.append("  H1000Oct.natCpow_norm_le_one %d %s %s (by norm_num)" % (N, sl, Tl))
        else:
            gb, Gn, Gd, xm = pd["gd"]
            Gl = "(((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ))" % (Gn, Gd)
            L.append("theorem hG%d : ∀ n : ℕ, 1 ≤ n → n ≤ %d → ‖(n : ℂ) ^ (-ArbEcon.Off.sOfG %s %s)‖ ≤ %s :=" % (j, N, sl, Tl, Gl))
            L.append("  H1000Oct.natCpow_norm_le_of_pow %d (by norm_num) 0 %d 16 (by norm_num) %d %d (by norm_num) (by norm_num)" % (N, gb, Gn, Gd))
            L.append("    (by norm_num) %s %s (by norm_num)" % (sl, Tl))
        # E
        El = rl(pd["E"])
        xlo, xhi, sigs = pd["xlo"], pd["xhi"], pd["sigs"]
        L.append("theorem hE%d : ∀ x : ℝ, |x - %s| ≤ ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) →" % (j, sl, rn, rd))
        L.append("    ‖riemannZeta (ArbEcon.Off.sOfG x %s) - emFinite 6 (ArbEcon.Off.sOfG x %s) %d‖ ≤ %s := by" % (Tl, Tl, N, El))
        L.append("  have hR := H1000Oct.rpow_cert %d (by norm_num) %d %d 16 (by norm_num) %d %d (by norm_num) (by norm_num)" % (N, pd["ea"], pd["eb"], pd["Rn"], pd["Rd"]))
        L.append("    %s (by norm_num)" % rl(xlo))
        L.append("  exact H1000Oct.hE_of_range 6 %d %s %s (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ)) %s %s %s (by norm_num) (by norm_num)" % (N, Tl, sl, rn, rd, rl(xlo), rl(xhi), El))
        L.append("    (H1000Oct.em_remainder_horiz6 %d (by norm_num) %s (by norm_num) %s %s %s (by norm_num) (by norm_num)" % (N, Tl, rl(xlo), rl(xhi), rl(sigs)))
        L.append("      (by norm_num) (%d : ℝ) (by norm_num) (by simp only [pochNormSq]; norm_num) _ hR %s (by norm_num))" % (pd["Qr"], El))
        # budget
        al = rl(pd["a"])
        Ul = rl(pd["U"])
        Rl = rl(r)
        Ll = rl(Lval)
        L.append("theorem budget%d : %s * (ArbEcon.Off.Cp 5 * (%s * %s) ^ (5 + 1) * ((((%d : ℕ) : ℝ)) - 1" % (j, Gl, Rl, Ll, N))
        L.append("      + ArbEcon.Off.emcB 6 %d %s %s) + 3 * ArbEcon.Off.corrVar 6 %d %s %s %s) + %s" % (N, al, Ul, N, Rl, al, Ul, El))
        L.append("    ≤ ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) := by" % (F.numerator, F.denominator))
        L.append("  rw [H1000Oct.emcB_betaN 6 %d (by norm_num), H1000Oct.corrVar_betaN 6 %d (by norm_num)]" % (N, N))
        L.append("  unfold ArbEcon.Off.Cp")
        L.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ArbEcon.OrderK.betaN, ArbEcon.OrderK.Lbeta]")
        L.append("  norm_num [Nat.factorial]")
        L.append("theorem hlhi%d : (s%d_N.lhi : ℝ) ≤ %s * 2 ^ (%s).P := by" % (j, j, Ll, cfgt))
        L.append("  show ((%d : ℕ) : ℝ) ≤ %s * 2 ^ (64 : ℕ)" % (pd["sN"].lhi, Ll))
        L.append("  norm_num")
        L.append("/-- **Piece %d**: `0 < octX %d (ζ(x + i T))` for `|x - %s| ≤ %s`. -/" % (j, pd["kk"], sig, r))
        L.append("theorem piece%d : ∀ x : ℝ, |x - %s| ≤ ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) →" % (j, sl, rn, rd))
        L.append("    0 < ArgHoriz.octX %s (riemannZeta ((x : ℂ) + (%s : ℂ) * I)) :=" % (zl(pd["kk"]), Tl))
        L.append("  H1000Oct.piece_octX_pos %s oc%d %s %s hσ%d ht 6 %d 5 (by norm_num) s%d_1 s%d_N inv%d_1 inv%d_N" % (cfgt, j, sl, Tl, j, N, j, j, j, j))
        L.append("    %d %d %d %d %s check%d %s %s %s %s %s %s (by norm_num) hlhi%d (by norm_num) (by norm_num)" % (rn, rd, F.numerator, F.denominator, zl(pd["kk"]), j, Rl, Ll, al, Ul, Gl, El, j))
        L.append("    (by norm_num) (by norm_num) (by norm_num) hG%d hE%d budget%d" % (j, j, j))
        L.append("")
    # certificate facts
    L.append("theorem stepOK : cert.StepOK := by")
    L.append("  intro j hj")
    L.append("  have hm : cert.m = %d := rfl" % m)
    L.append("  rw [hm] at hj")
    L.append("  have hj' : j < %d := by omega" % (m - 1))
    L.append("  interval_cases j <;> decide")
    L.append("")
    L.append("theorem noCross : cert.NoCross riemannZeta %s := by" % Tl)
    L.append("  intro j hj x hx")
    L.append("  have hm : cert.m = %d := rfl" % m)
    L.append("  rw [hm] at hj")
    L.append("  interval_cases j")
    for j, pd in enumerate(ps):
        L.append("  · exact piece%d x (H1000Oct.abs_sub_le_of_mem_uIcc (a := %s) (b := %s) hx (by norm_num) (by norm_num))"
                 % (j, rl(pd["hi"]), rl(pd["lo"])))
    L.append("")
    # endpoint boxes
    for which, pd, bx, jj in (("0", ps[0], e["box0"], 0), ("1", ps[-1], e["box1"], m - 1)):
        sl = rl(pd["sig"])
        L.append("theorem g%s : ArbEcon.Off.checkG %s oc%d 6 %d (s%d_1.acc.headD ArbEcon.Off.Acc.zero) (s%d_N.acc.headD ArbEcon.Off.Acc.zero)"
                 % (which, cfgt, jj, N, jj, jj))
        L.append("    %d (%d) (%d) (%d) (%d) %d %d %d = true := by" % (bx["D"], bx["reLo"], bx["reHi"], bx["imLo"], bx["imHi"], bx["Qp"], bx["Rn"], bx["Rd"]))
        L.append("  decide +kernel")
        a0 = "(((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ))" % (bx["reLo"], bx["D"])
        a1 = "(((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ))" % (bx["reHi"], bx["D"])
        b0 = "(((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ))" % (bx["imLo"], bx["D"])
        b1 = "(((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ))" % (bx["imHi"], bx["D"])
        L.append("theorem box%s : ArgHoriz.InBox (riemannZeta ((%s : ℂ) + (%s : ℂ) * I)) %s %s %s %s :=" % (which, sl, Tl, a0, a1, b0, b1))
        L.append("  H1000Oct.inBox_of_checkG %s oc%d %s %s hσ%d ht 6 %d s%d_1 s%d_N inv%d_1 inv%d_N (List.cons_ne_nil _ _)"
                 % (cfgt, jj, sl, Tl, jj, N, jj, jj, jj, jj))
        L.append("    (List.cons_ne_nil _ _) %d (%d) (%d) (%d) (%d) %d %d %d g%s" % (bx["D"], bx["reLo"], bx["reHi"], bx["imLo"], bx["imHi"], bx["Qp"], bx["Rn"], bx["Rd"], which))
        kk = pd["kk"]
        al, be = octA(kk), octB(kk)
        q = e["q0"] if which == "0" else e["q1"]
        L.append("theorem corners%s : ∀ a ∈ ({%s, %s} : Set ℝ), ∀ b ∈ ({%s, %s} : Set ℝ)," % (which, a0, a1, b0, b1))
        L.append("    0 < ((%d : ℤ) : ℝ) * a + ((%d : ℤ) : ℝ) * b ∧" % (al, be))
        L.append("      %s * (((%d : ℤ) : ℝ) * a + ((%d : ℤ) : ℝ) * b) ≤ ((%d : ℤ) : ℝ) * b - ((%d : ℤ) : ℝ) * a ∧"
                 % (rl(q[0]), al, be, al, be))
        L.append("      ((%d : ℤ) : ℝ) * b - ((%d : ℤ) : ℝ) * a ≤ %s * (((%d : ℤ) : ℝ) * a + ((%d : ℤ) : ℝ) * b) := by"
                 % (al, be, rl(q[1]), al, be))
        L.append("  intro a ha b hb")
        L.append("  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb")
        L.append("  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num")
        L.append("")
    k0, km = ps[0]["kk"], ps[-1]["kk"]
    q0, q1 = e["q0"], e["q1"]
    L.append("/-- **The horizontal argument change at T = %s, hypothesis-free.** -/" % T)
    L.append("theorem hAH : DiffractionCore.argChangeHoriz riemannZeta %s 2 (-1) ∈ Set.Icc %s %s := by" % (Tl, rl(e["Lv"]), rl(e["Hv"])))
    L.append("  have hA0 : ArgHoriz.octA (cert.k 0) = %s := by decide" % zl(octA(k0)))
    L.append("  have hB0 : ArgHoriz.octB (cert.k 0) = %s := by decide" % zl(octB(k0)))
    L.append("  have hA1 : ArgHoriz.octA (cert.k (cert.m - 1)) = %s := by decide" % zl(octA(km)))
    L.append("  have hB1 : ArgHoriz.octB (cert.k (cert.m - 1)) = %s := by decide" % zl(octB(km)))
    L.append("  have hk0 : cert.k 0 = %s := rfl" % zl(k0))
    L.append("  have hk1 : cert.k (cert.m - 1) = %s := rfl" % zl(km))
    L.append("  refine ArgHoriz.hAH_of_octCert_boxes (T := %s) (L := %s) (H := %s) (by norm_num) cert (by decide) rfl rfl"
             % (Tl, rl(e["Lv"]), rl(e["Hv"])))
    L.append("    stepOK noCross (qlo0 := %s) (qhi0 := %s) box0 (by rw [hA0, hB0]; exact corners0)" % (rl(q0[0]), rl(q0[1])))
    L.append("    (qlo1 := %s) (qhi1 := %s) box1 (by rw [hA1, hB1]; exact corners1) ?_ ?_" % (rl(q1[0]), rl(q1[1])))
    L.append("  · rw [hk1, hk0]")
    L.append("    have h1 := ArgHoriz.atanLo_le %s" % rl(q1[0]))
    L.append("    have h2 := ArgHoriz.le_atanHi %s" % rl(q0[1]))
    L.append("    have hp1 := Real.pi_gt_d6")
    L.append("    have hp2 := Real.pi_lt_d6")
    L.append("    norm_num [ArgHoriz.atanLo, ArgHoriz.atanHi] at h1 h2 hp1 hp2 ⊢")
    L.append("    linarith")
    L.append("  · rw [hk1, hk0]")
    L.append("    have h1 := ArgHoriz.le_atanHi %s" % rl(q1[1]))
    L.append("    have h2 := ArgHoriz.atanLo_le %s" % rl(q0[0]))
    L.append("    have hp1 := Real.pi_gt_d6")
    L.append("    have hp2 := Real.pi_lt_d6")
    L.append("    norm_num [ArgHoriz.atanLo, ArgHoriz.atanHi] at h1 h2 hp1 hp2 ⊢")
    L.append("    linarith")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    fname = os.path.join(outdir, "H1000Edge_%s.lean" % tag)
    with open(fname, "w") as f:
        f.write("\n".join(L))
    return fname


def slab_tag(kind, T):
    T = Fr(T)
    s = "%d" % T.numerator if T.denominator == 1 else "%d_%d" % (T.numerator, T.denominator)
    return "%s%s" % (kind, s)


def emit_slab(sd, outdir):
    tag, a, b, N, Lval, R, F = sd["tag"], sd["a"], sd["b"], sd["N"], sd["L"], sd["R"], sd["F"]
    tq = sd["tq"]
    al_, bl_ = sd["alean"], sd["blean"]   # Lean forms matching BandGlue_h1000 (e.g. ((41 : ℝ) - 5773 / 100000))
    ns = "H1000Slab.%s" % tag
    U, Qr, r0 = sd["U"], sd["Qr"], sd["r0"]
    cells = []
    for tr in sd["trees"]:
        cells += leaves(tr)
    L = []
    L.append("/-  H1000Slab_%s.lean -- a KERNEL-CHECKED zero-free edge slab `SlabClear a b`, a = %s, b = %s" % (tag, a, b))
    L.append("    (lane h1000-integrate; GENERATED by ../emit_h1000_offline.py; do not edit).")
    L.append("")
    L.append("    %d cells cover [1/2, 1] x [a, b] (the reflection `ArbEcon.Off.slabClear_of_right_half` covers" % len(cells))
    L.append("    (0, 1/2)); each cell: ONE off-line evaluator run at its center (N = %d, 6 accumulators) and ONE" % N)
    L.append("    `ArbEcon.Off.checkCell` (`decide +kernel`), assembled by `H1000Oct.cell_zeta_ne_zero_R` with the")
    L.append("    slab's error budget F = %s at radius R = %s (`norm_num`)." % (F, R))
    L.append("    conjecture1_proved = False.  A finite zero-free slab; nothing about RH.")
    L.append("-/")
    L.append("import H1000Octant")
    L.append("")
    L.append("open Complex ZetaReflection ZetaReflection.EMHigh")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    for j, cl in enumerate(cells):
        o = cl["o"]
        L.append("def oc%d : ArbEcon.Off.OCfg := ⟨%d, %d, %d, %d, %d⟩" % (j, o.a, o.b, o.q, o.oneQ, o.nfuel))
        L.append("def s%d_1 : ArbEcon.Off.StO := %s" % (j, O.st_lean(cl["s1"])))
        L.append("def s%d_N : ArbEcon.Off.StO := %s" % (j, O.st_lean(cl["sN"])))
    L.append("")
    L.append("end")
    L.append("")
    Rl, Ll, Ul = rl(R), rl(Lval), rl(U)
    L.append("theorem budget : ArbEcon.Off.Cp 5 * (%s * %s) ^ (5 + 1) * ((((%d : ℕ) : ℝ)) - 1 + ArbEcon.Off.emcB 6 %d %s %s)" % (Rl, Ll, N, N, al_, Ul))
    L.append("    + 3 * ArbEcon.Off.corrVar 6 %d %s %s %s" % (N, Rl, al_, Ul))
    L.append("    + ArbEcon.Off.CK 6 * (%d : ℝ) / ((((%d : ℕ) : ℝ)) ^ (2 * 6) * ((%d : ℕ) : ℝ)) / ((((2 * 6 : ℕ)) : ℝ) + 1 / 2)" % (Qr, N, r0))
    L.append("      ≤ ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) := by" % (F.numerator, F.denominator))
    L.append("  have hC := H1000Oct.CK_six_le")
    L.append("  have hC0 := ArbEcon.Off.CK_nonneg 6")
    L.append("  have hm : ArbEcon.Off.CK 6 * (%d : ℝ) / ((((%d : ℕ) : ℝ)) ^ (2 * 6) * ((%d : ℕ) : ℝ)) / ((((2 * 6 : ℕ)) : ℝ) + 1 / 2)" % (Qr, N, r0))
    L.append("      ≤ (84107 / 1000000000000000 : ℝ) * (%d : ℝ) / ((((%d : ℕ) : ℝ)) ^ (2 * 6) * ((%d : ℕ) : ℝ)) / ((((2 * 6 : ℕ)) : ℝ) + 1 / 2) := by" % (Qr, N, r0))
    L.append("    gcongr")
    L.append("  refine le_trans (add_le_add (le_refl _) hm) ?_")
    L.append("  rw [H1000Oct.emcB_betaN 6 %d (by norm_num), H1000Oct.corrVar_betaN 6 %d (by norm_num)]" % (N, N))
    L.append("  unfold ArbEcon.Off.Cp")
    L.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ArbEcon.OrderK.betaN, ArbEcon.OrderK.Lbeta]")
    L.append("  norm_num [Nat.factorial]")
    L.append("")
    L.append("theorem hQ : pochNormSq 1 %s (2 * 6 + 1) ≤ (%d : ℝ) ^ 2 := by" % (bl_, Qr))
    L.append("  simp only [pochNormSq]")
    L.append("  norm_num")
    L.append("")
    for j, cl in enumerate(cells):
        o, sig, tc, tn = cl["o"], cl["sig"], cl["tc"], cl["tn"]
        cfgt = cfg_term(tn, tq)
        sl, tcl = rl(sig), rl(tc)
        rn, rd = cl["rn"], cl["rd"]
        L.append("/-! ### Cell %d: [%s, %s] x [%s, %s] -/" % (j, cl["xl"], cl["xr"], cl["yl"], cl["yh"]))
        L.append("")
        L.append("theorem chunk%d_1 : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d %d (ArbEcon.Off.StO.init %s 5)) s%d_1 = true := by" % (j, cfgt, j, N - 2, cfgt, j))
        L.append("  decide +kernel")
        L.append("theorem chunk%d_N : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d 1 s%d_1) s%d_N = true := by" % (j, cfgt, j, j, j))
        L.append("  decide +kernel")
        L.append("theorem check%d : ArbEcon.Off.checkCell %s oc%d 6 %d 5 s%d_1.acc s%d_N.acc %d %d %d %d = true := by" % (j, cfgt, j, N, j, j, rn, rd, F.numerator, F.denominator))
        L.append("  decide +kernel")
        L.append("theorem ht%d : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (j, tcl, tn, tq))
        L.append("theorem valid%d : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht%d" % (j, cfgt, tcl, tn, tq, j))
        L.append("theorem hσ%d : %s = (((%d : ℕ) : ℝ) - ((%d : ℕ) : ℝ)) / ((%d : ℕ) : ℝ) := by norm_num" % (j, sl, o.a, o.b, o.q))
        L.append("theorem ovalid%d : ArbEcon.Off.OValid %s oc%d %s := ⟨by decide +kernel, by decide, hσ%d⟩" % (j, cfgt, j, sl, j))
        L.append("theorem inv%d_1 : ArbEcon.Off.InvO %s %s %s (%d - 1) s%d_1 :=" % (j, cfgt, sl, tcl, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid%d ovalid%d %d 1 (ArbEcon.Off.StO.init %s 5) s%d_1" % (j, j, j, N - 2, cfgt, j))
        L.append("    (ArbEcon.Off.initO_sound _ _ _ 5 valid%d.one_eq) chunk%d_1" % (j, j))
        L.append("theorem inv%d_N : ArbEcon.Off.InvO %s %s %s %d s%d_N :=" % (j, cfgt, sl, tcl, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid%d ovalid%d 1 %d s%d_1 s%d_N inv%d_1 chunk%d_N" % (j, j, j, N - 1, j, j, j, j))
        L.append("theorem cell%d : ∀ x y : ℝ, %s ≤ x → x ≤ %s → %s ≤ y → y ≤ %s → x ≤ 1 →" % (j, rl(cl["xl"]), rl(cl["xr"]), rl(cl["yl"]), rl(cl["yh"])))
        L.append("    riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by")
        L.append("  intro x y hx0 hx1 hy0 hy1 hx1'")
        L.append("  have hlhi : (s%d_N.lhi : ℝ) ≤ %s * 2 ^ (%s).P := by" % (j, Ll, cfgt))
        L.append("    show ((%d : ℕ) : ℝ) ≤ %s * 2 ^ (64 : ℕ)" % (cl["sN"].lhi, Ll))
        L.append("    norm_num")
        L.append("  have hcell := H1000Oct.cell_zeta_ne_zero_R %s oc%d %s %s hσ%d ht%d 6 %d 5 (by norm_num) (by norm_num)" % (cfgt, j, sl, tcl, j, j, N))
        L.append("    s%d_1 s%d_N inv%d_1 inv%d_N %d %d %d %d check%d %s %s %s %s %s (%d : ℝ) %d (by norm_num) hlhi" % (j, j, j, j, rn, rd, F.numerator, F.denominator, j, Rl, Ll, al_, Ul, bl_, Qr, r0))
        L.append("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hQ")
        L.append("    (by norm_num) (by norm_num) budget")
        L.append("  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp")
        L.append("  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp")
        L.append("  apply hcell")
        L.append("  · apply ArbEcon.Off.dist_le_of_box x y %s %s %s %s (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ))" % (sl, tcl, rl(cl["w"]), rl(cl["hh"]), rn, rd))
        L.append("    · rw [abs_le]; constructor <;> linarith")
        L.append("    · rw [abs_le]; constructor <;> linarith")
        L.append("    · norm_num")
        L.append("    · norm_num")
        L.append("  · rw [him]; linarith")
        L.append("  · rw [him]; linarith")
        L.append("  · rw [hre]; linarith")
        L.append("  · rw [hre]; exact hx1'")
        L.append("")
    # tree nodes
    cid = {id(cl): j for j, cl in enumerate(cells)}
    node_names = {}
    counter = [0]

    def emit_node(t):
        if t["leaf"]:
            return "cell%d" % cid[id(t)], (t["xl"], t["xr"], t["yl"], t["yh"])
        n1, b1 = emit_node(t["lo"])
        n2, b2 = emit_node(t["hi"])
        xl, xr, yl, yh = b1[0], b2[1], b1[2], b2[3]
        if t["axis"] == "y":
            xl, xr, yl, yh = b1[0], b1[1], b1[2], b2[3]
        name = "node%d" % counter[0]
        counter[0] += 1
        m_ = t["m"]
        L.append("theorem %s : ∀ x y : ℝ, %s ≤ x → x ≤ %s → %s ≤ y → y ≤ %s → x ≤ 1 →" % (name, rl(xl), rl(xr), rl(yl), rl(yh)))
        L.append("    riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by")
        L.append("  intro x y hx0 hx1 hy0 hy1 hx1'")
        if t["axis"] == "x":
            L.append("  by_cases h : x ≤ %s" % rl(m_))
            L.append("  · exact %s x y hx0 h hy0 hy1 hx1'" % n1)
            L.append("  · exact %s x y (by linarith) hx1 hy0 hy1 hx1'" % n2)
        else:
            L.append("  by_cases h : y ≤ %s" % rl(m_))
            L.append("  · exact %s x y hx0 hx1 hy0 h hx1'" % n1)
            L.append("  · exact %s x y hx0 hx1 (by linarith) hy1 hx1'" % n2)
        L.append("")
        return name, (xl, xr, yl, yh)

    roots = [emit_node(tr) for tr in sd["trees"]]
    L.append("/-- The right half of the slab. -/")
    L.append("theorem right_half : ∀ x y : ℝ, 1 / 2 ≤ x → x < 1 → %s ≤ y → y ≤ %s →" % (al_, bl_))
    L.append("    riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by")
    L.append("  intro x y hx0 hx1 hy0 hy1")
    for k, (nm, bb) in enumerate(roots[:-1]):
        L.append("  by_cases h%d : x ≤ %s" % (k, rl(bb[1])))
        L.append("  · exact %s x y (by linarith) h%d (by linarith) (by linarith) (by linarith)" % (nm, k))
    L.append("  exact %s x y (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)" % roots[-1][0])
    L.append("")
    L.append("/-- **The edge-clearance slab `SlabClear %s %s`, hypothesis-free.** -/" % (a, b))
    L.append("theorem slabClear : EdgeClearGlue.SlabClear %s %s :=" % (al_, bl_))
    L.append("  ArbEcon.Off.slabClear_of_right_half _ _ right_half")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    fname = os.path.join(outdir, "H1000Slab_%s.lean" % tag)
    with open(fname, "w") as f:
        f.write("\n".join(L))
    return fname


# ------------------------------------------------------------------ the capstone and the guard

def fr_lean_plain(x):
    """rational literal as it appears inside BandGlue_h1000 tables: 41, 965 / 4, 5773 / 100000"""
    x = Fr(x)
    if x.denominator == 1:
        return "%d" % x.numerator
    return "%d / %d" % (x.numerator, x.denominator)


def lower_forms(T0, cap):
    return "((%s : ℝ) - %s)" % (fr_lean_plain(T0), fr_lean_plain(cap)), "(%s : ℝ)" % fr_lean_plain(T0)


def upper_forms(T1, cap):
    return "(%s : ℝ)" % fr_lean_plain(T1), "((%s : ℝ) + %s)" % (fr_lean_plain(T1), fr_lean_plain(cap))


def pin_check(n, E):
    L1, H1, L2, H2, L3, H3, L4, H4, L5, H5 = E
    lo = 2 * Fr(31416, 10000) * (n - 1) < 2 * L1 + L2 - H3 + L4 + L5
    hi = 2 * H1 + H2 - L3 + H4 + H5 < 2 * Fr(314, 100) * (n + 1)
    slo = 2 * L1 + L2 - H3 + L4 + L5 - 2 * Fr(31416, 10000) * (n - 1)
    shi = 2 * Fr(314, 100) * (n + 1) - (2 * H1 + H2 - L3 + H4 + H5)
    return lo and hi, float(slo), float(shi)


def el(k, v):
    """enclosure literal: L1 in the exact form of `ArgChangeH1000.segK` (`-(249 / 250)`), so the K6
    side conditions of `segK i` transfer to `segWith i (E i)` by definitional unfolding"""
    if k == 0:
        assert v == Fr(-249, 250)
        return "-(249 / 250 : ℝ)"
    return rl(v)


def emit_capstone(bands, capLo, capHi, k6b, edges, outdir, slab_tags):
    encl = {e["T"]: (e["Lv"], e["Hv"]) for e in edges}
    L = []
    L.append("/-  AllZerosKernel_h1000.lean -- the height-1000 ladder statement, HYPOTHESIS-FREE")
    L.append("    (lane h1000-integrate; GENERATED by ../emit_h1000_offline.py; do not edit).")
    L.append("")
    L.append("        all_nontrivial_zeros_up_to_height_1000 :")
    L.append("          ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2")
    L.append("")
    L.append("    Every input of the 25 Turing bands of `BandGlue_h1000.seg` (the [1, 1000] segment of")
    L.append("    `AllZeros_h1000`) is discharged in the kernel:")
    L.append("      * hLine (on-line zeros): `H1000Line.seg_lineHyp` (lane h1000-prep);")
    L.append("      * hγ (height floor 55/16): `HeightFloor.height_floor`;")
    L.append("      * hnzl: `EdgeClearGlue.hnzl_discharged` (K1); hnzb / hnzt / hins: K1 from 50 zero-free")
    L.append("        slabs -- band 0's lower slab `H1000Glue.slab0_band0`, band 24's upper slab")
    L.append("        `ArbEcon.Off.Slab_T1000.band24_top_slabClear` (lane offline), the other 48 `H1000Slab_*`;")
    L.append("      * hAV2: K6a generic `[-249/250, 249/250]` (`ArgZetaTwo`); hAG1 / hAG2: K6b closed-form")
    L.append("        brackets (`ArgGammaR`, the rationals of `ArgChangeH1000.segK_side_i`);")
    L.append("      * hAHt / hAHb: 27 kernel-checked octant certificates `H1000Edge_*.hAH` (K6c + the off-line")
    L.append("        evaluator);")
    L.append("      * the pins `H1000Line.PinOk i (E i)`: `norm_num`.")
    L.append("    The composition is `H1000Line.all_nontrivial_zeros_up_to_height_1000_of_encl`.")
    L.append("    Axioms [propext, Classical.choice, Quot.sound] (AxiomGuardAllZerosKernel_h1000); no `sorry`.")
    L.append("    conjecture1_proved = False.  A FINITE verification up to height 1000; it says nothing about")
    L.append("    the Riemann Hypothesis.")
    L.append("-/")
    L.append("import H1000Line_All")
    L.append("import ArgChangeH1000")
    L.append("import EMZetaOfflineSlabBand")
    for e in edges:
        L.append("import H1000Edge_%s" % edge_tag(e["T"]))
    for t in slab_tags:
        L.append("import H1000Slab_%s" % t)
    L.append("")
    L.append("open Complex")
    L.append("")
    L.append("namespace AllZerosKernel_h1000")
    L.append("")
    Evals = {}
    for (i, T0, T1, n) in bands:
        L2, H2 = encl[T1]
        L3, H3 = encl[T0]
        Evals[i] = (Fr(-249, 250), Fr(249, 250), L2, H2, L3, H3, k6b["L4t"][i], k6b["H4t"][i], k6b["L5t"][i], k6b["H5t"][i])
    L.append("/-- The five enclosures of every band: K6a, the two kernel-checked horizontal edges, K6b. -/")
    L.append("noncomputable def E : ℕ → H1000Line.Encl := fun i => match i with")
    for (i, T0, T1, n) in bands:
        L.append("  | %d => ⟨%s⟩" % (i, ", ".join(el(k, v) for k, v in enumerate(Evals[i]))))
    L.append("  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩")
    L.append("")
    pins = {}
    for (i, T0, T1, n) in bands:
        ok, slo, shi = pin_check(n, Evals[i])
        assert ok, "pin fails at band %d" % i
        pins[i] = (slo, shi)
        E_ = Evals[i]
        L.append("theorem pin%d : H1000Line.PinOk %d (E %d) := by" % (i, i, i))
        L.append("  show 2 * 3.1416 * (((%d : ℕ) : ℝ) - 1) < 2 * %s + %s - %s + %s + %s ∧"
                 % (n, el(0, E_[0]), rl(E_[2]), rl(E_[5]), rl(E_[6]), rl(E_[8])))
        L.append("    2 * %s + %s - %s + %s + %s < 2 * 3.14 * (((%d : ℕ) : ℝ) + 1)"
                 % (rl(E_[1]), rl(E_[3]), rl(E_[4]), rl(E_[7]), rl(E_[9]), n))
        L.append("  norm_num")
        L.append("")
    L.append("theorem hpin : ∀ i, i < 25 → H1000Line.PinOk i (E i) := by")
    L.append("  intro i hi")
    L.append("  interval_cases i")
    for (i, T0, T1, n) in bands:
        L.append("  · exact pin%d" % i)
    L.append("")
    for (i, T0, T1, n) in bands:
        L.append("theorem side%d : ArgChangeGlue.K6Side (H1000Line.segWith %d (E %d)) :=" % (i, i, i))
        L.append("  ⟨(ArgChangeH1000.segK_side_%d).hT0, (ArgChangeH1000.segK_side_%d).hT1, (ArgChangeH1000.segK_side_%d).hL1," % (i, i, i))
        L.append("    (ArgChangeH1000.segK_side_%d).hH1, (ArgChangeH1000.segK_side_%d).hL4, (ArgChangeH1000.segK_side_%d).hH4," % (i, i, i))
        L.append("    (ArgChangeH1000.segK_side_%d).hL5, (ArgChangeH1000.segK_side_%d).hH5⟩" % (i, i))
        L.append("theorem horiz%d : ArgChangeGlue.HorizHyp (H1000Line.segWith %d (E %d)) :=" % (i, i, i))
        L.append("  ⟨H1000Edge.%s.hAH, H1000Edge.%s.hAH⟩" % (edge_tag(T1), edge_tag(T0)))
        L.append("")
    L.append("theorem henc : ∀ i, i < 25 → (H1000Line.segWith i (E i)).EnclHyp := by")
    L.append("  intro i hi")
    L.append("  interval_cases i")
    for (i, T0, T1, n) in bands:
        L.append("  · exact ArgChangeGlue.enclHyp_of_K6 side%d horiz%d" % (i, i))
    L.append("")
    L.append("theorem hslab0 : ∀ i, 1 ≤ i → i < 25 → EdgeClearGlue.SlabClear")
    L.append("    ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i) (BandGlue_h1000.seg i).T0 := by")
    L.append("  intro i h1 hi")
    L.append("  interval_cases i")
    for (i, T0, T1, n) in bands:
        if i == 0:
            continue
        a_, b_ = lower_forms(T0, capLo[i])
        L.append("  · show EdgeClearGlue.SlabClear %s %s" % (a_, b_))
        L.append("    exact H1000Slab.%s.slabClear" % slab_tag("L", T0))
    L.append("")
    L.append("theorem hslab1 : ∀ i, i < 25 → EdgeClearGlue.SlabClear (BandGlue_h1000.seg i).T1")
    L.append("    ((BandGlue_h1000.seg i).T1 + BandGlue_h1000.capHi i) := by")
    L.append("  intro i hi")
    L.append("  interval_cases i")
    for (i, T0, T1, n) in bands:
        if i == 24:
            L.append("  · exact ArbEcon.Off.Slab_T1000.band24_top_slabClear")
            continue
        a_, b_ = upper_forms(T1, capHi[i])
        L.append("  · show EdgeClearGlue.SlabClear %s %s" % (a_, b_))
        L.append("    exact H1000Slab.%s.slabClear" % slab_tag("U", T1))
    L.append("")
    L.append("/-- **Every nontrivial zero of ζ with `0 < Im ρ ≤ 1000` lies on the critical line** -- kernel-checked,")
    L.append("    NO hypotheses (a finite verification; conjecture1_proved = False). -/")
    L.append("theorem all_nontrivial_zeros_up_to_height_1000 :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  H1000Line.all_nontrivial_zeros_up_to_height_1000_of_encl E hpin henc hslab0 hslab1")
    L.append("")
    L.append("end AllZerosKernel_h1000")
    L.append("")
    fname = os.path.join(outdir, "AllZerosKernel_h1000.lean")
    with open(fname, "w") as f:
        f.write("\n".join(L))
    return fname, pins


def theorems_of(fname):
    src = open(fname).read()
    nss = re.findall(r"^namespace (\S+)", src, re.M)
    names = re.findall(r"^theorem (\S+)", src, re.M)
    ns = nss[0] if nss else ""
    return ["%s.%s" % (ns, n) if ns else n for n in names]


def neg_controls(e, sd):
    """kernel negative controls on edge `e` (piece 0) and slab `sd` (cell 0): each `= false` by decide."""
    L = []
    T, tn, tq, N = e["T"], e["tn"], e["tq"], e["N"]
    ns = "H1000Edge.%s" % edge_tag(T)
    cfgt = cfg_term(tn, tq)
    pd = e["pieces"][0]
    r, F, kk = pd["r"], pd["F"], pd["kk"]
    c, o = cfg_of(tn, tq), pd["o"]
    ok_opp, _ = check_oct(c, o, KEM, N, PT, pd["s1"].acc, pd["sN"].acc, r.numerator, r.denominator, F.numerator, F.denominator, kk + 4)
    ok_big, _ = check_oct(c, o, KEM, N, PT, pd["s1"].acc, pd["sN"].acc, r.numerator, r.denominator, 1000, 1, kk)
    assert not ok_opp and not ok_big
    L.append("/-- Negative control: the opposite octant (label + 4) is rejected by the kernel. -/")
    L.append("example : H1000Oct.checkOct %s %s.oc0 6 %d 5 %s.s0_1.acc %s.s0_N.acc %d %d %d %d %s = false := by"
             % (cfgt, ns, N, ns, ns, r.numerator, r.denominator, F.numerator, F.denominator, zl(kk + 4)))
    L.append("  decide +kernel")
    L.append("/-- Negative control: an error budget F = 1000 cannot be certified. -/")
    L.append("example : H1000Oct.checkOct %s %s.oc0 6 %d 5 %s.s0_1.acc %s.s0_N.acc %d %d 1000 1 %s = false := by"
             % (cfgt, ns, N, ns, ns, r.numerator, r.denominator, zl(kk)))
    L.append("  decide +kernel")
    bx = e["box0"]
    L.append("/-- Negative control: the endpoint box at x = 2 shrunk to a point (Re) is rejected. -/")
    L.append("example : ArbEcon.Off.checkG %s %s.oc0 6 %d (%s.s0_1.acc.headD ArbEcon.Off.Acc.zero) (%s.s0_N.acc.headD ArbEcon.Off.Acc.zero)"
             % (cfgt, ns, N, ns, ns))
    L.append("    %d (%d) (%d) (%d) (%d) %d %d %d = false := by" % (bx["D"], bx["reLo"], bx["reLo"], bx["imLo"], bx["imHi"], bx["Qp"], bx["Rn"], bx["Rd"]))
    L.append("  decide +kernel")
    cl = leaves(sd["trees"][0])[0]
    cfgs = cfg_term(cl["tn"], sd["tq"])
    nss = "H1000Slab.%s" % sd["tag"]
    L.append("/-- Negative control: a slab cell with error budget F = 10 is rejected. -/")
    L.append("example : ArbEcon.Off.checkCell %s %s.oc0 6 %d 5 %s.s0_1.acc %s.s0_N.acc %d %d 10 1 = false := by"
             % (cfgs, nss, sd["N"], nss, nss, cl["rn"], cl["rd"]))
    L.append("  decide +kernel")
    return L


def emit_guard(outdir, files, parts=6, negs=None):
    allnames = []
    for f in files:
        allnames += theorems_of(f)
    chunks = [allnames[k::parts] for k in range(parts)]
    roots = []
    for k, ch in enumerate(chunks):
        L = []
        L.append("/-  AxiomGuardAllZerosKernel_h1000_%d.lean -- `#print axioms` of every new theorem of lane" % k)
        L.append("    h1000-integrate, part %d of %d (GENERATED by ../emit_h1000_offline.py).  Expected: every line" % (k + 1, parts))
        L.append("    within [propext, Classical.choice, Quot.sound].  conjecture1_proved = False.")
        L.append("-/")
        L.append("import AllZerosKernel_h1000")
        L.append("")
        for n in ch:
            L.append("#print axioms %s" % n)
        L.append("")
        fname = os.path.join(outdir, "AxiomGuardAllZerosKernel_h1000_%d.lean" % k)
        with open(fname, "w") as f:
            f.write("\n".join(L))
        roots.append("AxiomGuardAllZerosKernel_h1000_%d" % k)
    # the statement-shape / capstone guard
    L = []
    L.append("/-  AxiomGuardAllZerosKernel_h1000.lean -- the capstone guard of lane h1000-integrate (GENERATED by")
    L.append("    ../emit_h1000_offline.py).  Statement-shape checks (the capstone is the ladder conclusion of")
    L.append("    `AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands`, verbatim, with NO binders),")
    L.append("    `#print axioms` of the capstone, and kernel negative controls.  conjecture1_proved = False.")
    L.append("-/")
    L.append("import AllZerosKernel_h1000")
    L.append("")
    L.append("/-- The capstone has exactly the ladder conclusion and no hypotheses. -/")
    L.append("example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000")
    L.append("")
    L.append("/-- Same conclusion as the existing conditional ladder capstone (its two binders discharged). -/")
    L.append("example : AllZeros_h1000.BandHyp → (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 →")
    L.append("    55 / 16 ≤ |ρ.im|) → ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  fun _ _ => AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000")
    L.append("")
    L.append("#print axioms AllZerosKernel_h1000.all_nontrivial_zeros_up_to_height_1000")
    L.append("")
    if negs:
        L += negs
        L.append("")
    fname = os.path.join(outdir, "AxiomGuardAllZerosKernel_h1000.lean")
    with open(fname, "w") as f:
        f.write("\n".join(L))
    return ["AxiomGuardAllZerosKernel_h1000"] + roots, len(allnames)


# ------------------------------------------------------------------ driver

def main():
    argv = sys.argv[1:]
    opts, i = {}, 0
    while i < len(argv):
        opts[argv[i][2:]] = argv[i + 1]
        i += 2
    outdir = opts.get("outdir", os.path.join(HERE, "lean"))
    t0 = time.time()
    bands, capLo, capHi = parse_bands()
    assert len(bands) == 25
    k6b = parse_k6b()
    heights = sorted(set([b[1] for b in bands] + [b[2] for b in bands]))
    assert len(heights) == 27, heights
    only_e = opts.get("only-edges")
    only_s = opts.get("only-slabs")
    edges, files = [], []
    summary = dict(edges=[], slabs=[])
    for T in heights:
        e = edge_enclosure(plan_edge(T))
        edges.append(e)
        if only_e is None or edge_tag(T) in only_e.split(","):
            files.append(emit_edge(e, outdir))
        summary["edges"].append(dict(T=str(T), N=e["N"], pieces=len(e["pieces"]), L=str(e["Lv"]), H=str(e["Hv"]),
                                     width=float(e["Hv"] - e["Lv"]),
                                     min_margin=min(p["margin"] for p in e["pieces"]),
                                     radii=[str(p["r"]) for p in e["pieces"]],
                                     labels=[p["kk"] for p in e["pieces"]]))
    slab_tags = []
    for (i, T0, T1, n) in bands:
        specs = []
        if i >= 1:
            a_, b_ = lower_forms(T0, capLo[i])
            specs.append((slab_tag("L", T0), T0 - capLo[i], T0, a_, b_))
        if i <= 23:
            a_, b_ = upper_forms(T1, capHi[i])
            specs.append((slab_tag("U", T1), T1, T1 + capHi[i], a_, b_))
        for (tag, a, b, a_, b_) in specs:
            sd = plan_slab(tag, a, b)
            sd["alean"], sd["blean"] = a_, b_
            if not slab_tags:
                first_slab = sd
            slab_tags.append(tag)
            if only_s is None or tag in only_s.split(","):
                files.append(emit_slab(sd, outdir))
            lv = [l for tr in sd["trees"] for l in leaves(tr)]
            summary["slabs"].append(dict(tag=tag, a=str(a), b=str(b), N=sd["N"], cells=len(lv), F=str(sd["F"]),
                                         R=str(sd["R"]), min_margin=min(l["margin"] for l in lv)))
    assert len(slab_tags) == 48
    cap, pins = emit_capstone(bands, capLo, capHi, k6b, edges, outdir, slab_tags)
    summary["pins"] = {str(k): v for k, v in pins.items()}
    gfiles = [os.path.join(HERE, "lean", "H1000Octant.lean")]
    gfiles += [os.path.join(outdir, "H1000Edge_%s.lean" % edge_tag(T)) for T in heights]
    gfiles += [os.path.join(outdir, "H1000Slab_%s.lean" % t) for t in slab_tags]
    gfiles += [cap]
    negs = neg_controls(edges[heights.index(Fr(41))], first_slab)
    groots, nthm = emit_guard(outdir, gfiles, negs=negs)
    summary["guard_roots"] = groots
    summary["guard_theorems"] = nthm
    summary["edge_tags"] = [edge_tag(T) for T in heights]
    summary["slab_tags"] = slab_tags
    summary["py_seconds"] = round(time.time() - t0, 1)
    summary["total_pieces"] = sum(len(e["pieces"]) for e in edges)
    summary["total_cells"] = sum(s["cells"] for s in summary["slabs"])
    js = opts.get("json")
    if js:
        with open(js, "w") as f:
            json.dump(summary, f, indent=1)
    print(json.dumps(dict((k, summary[k]) for k in ["total_pieces", "total_cells", "guard_theorems", "py_seconds"])))


if __name__ == "__main__":
    main()
