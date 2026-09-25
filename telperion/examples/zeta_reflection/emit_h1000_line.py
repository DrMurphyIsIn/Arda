"""Emit the kernel-checked on-line sign certificates of the height-1000 ladder segment (lane h1000-prep).

usage: emit_h1000_line.py [--bands 0-24] [--outdir DIR] [--tq 10] [--nl 48] [--zeros FILE] [--json FILE]

For each of the 25 Turing bands of `BandGlue_h1000.seg` (the [1, 1000] segment of `AllZeros_h1000`) this
picks n+1 grid points t = tn / 2^tq separating the band's n zeros (one point below the first zero, one
between each consecutive pair, one above the last), and for each point computes, with an EXACT Python
mirror of the Lean checker `H1000Line.ptCheck` (H1000Point.lean / H1000Phase.lean):

  * the ArbEconomics evaluator states after N-1 and N Dirichlet terms (arbecon/arbecon_model.py, the
    bit-exact mirror of Probes/ArbEconomics_Eval.lean) at the shared configuration `cfg64 tn tq`;
  * the order-13 (K = 6) odd-saw Euler-Maclaurin remainder certificate (Q, r) and correction factor
    (arbecon/gen_emhigh_k.py mirrors of EMZetaHighCheck.remOdd / corrData);
  * the phase interval [phaseLo, phaseHi] (scale 2^64) of phi = Lam - (t/2) log pi from the theta bracket,
    the 2 pi m shift, and cos/sin by the evaluator's `trig`;
  * the product ball sCtr +- sRad of S * 2^64 * W, S = cos phi Re zeta - sin phi Im zeta,

and REFUSES to emit a point whose check fails (or a band whose `bandOk` fails).  Output (OUTDIR, default
./lean):

  H1000Line_Bxx.lean   band xx: the points `p_i`, `ok_i : ptCheck p_i = true` (decide +kernel), `pts`,
                       `all : AllOk pts`, `band : bandOk ... pts = true` (decide +kernel), and
                       `lineHyp` (the band's verbatim hLine, via H1000Line.band_sound);
  H1000Line_All.lean   `(BandGlue_h1000.seg i).LineHyp` for all i < 25, `lineHyp_of_edges` (any band data
                       with the same T0, T1, n), and the height-1000 ladder statement from the remaining
                       (off-line) inputs only.

The zero list (untrusted, only used to PLACE the grid points) comes from mpmath.zetazero; nothing about
it is trusted: the kernel re-derives every sign.  Prints a JSON summary.  conjecture1_proved = False.
"""
import sys
import os
import json
import math
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "arbecon"))
import arbecon_model as M  # noqa: E402
import gen_emhigh_k as G  # noqa: E402

ONE = 2 ** 64
L2LO, L2HI = 12786308645202588812, 12786308645202719885
LPLO, LPHI = 21116539237789363774, 21116539237791978907
P8LO, P8HI = 7244019458077122842, 7244019458077122843
TPLO, TPHI = 115904311329233965478, 115904311329233965479
KEM = 6

# The 25 bands of BandGlue_h1000.seg: (T0 num, T0 den, T1 num, T1 den, n), in box order.
BANDS = [(1, 1, 41, 1, 7), (41, 1, 81, 1, 14), (81, 1, 121, 1, 17), (121, 1, 161, 1, 20),
         (161, 1, 201, 1, 21), (201, 1, 965, 4, 24), (241, 1, 281, 1, 24), (281, 1, 321, 1, 24),
         (321, 1, 361, 1, 26), (361, 1, 401, 1, 26), (401, 1, 441, 1, 27), (441, 1, 481, 1, 27),
         (481, 1, 520, 1, 27), (520, 1, 560, 1, 29), (560, 1, 600, 1, 29), (600, 1, 640, 1, 29),
         (640, 1, 680, 1, 30), (680, 1, 720, 1, 30), (720, 1, 760, 1, 30), (760, 1, 800, 1, 31),
         (800, 1, 840, 1, 31), (840, 1, 880, 1, 31), (880, 1, 920, 1, 32), (920, 1, 960, 1, 32),
         (960, 1, 1000, 1, 32)]


# ------------------------------------------------------------------ exact mirror of H1000Phase

def fdiv(a, b):
    """H1000Line.fdiv: Int.ediv by a positive Nat = floor."""
    return a // b


def cdiv(a, b):
    """H1000Line.cdiv: -((-a) / b)."""
    return -((-a) // b)


def lser(one, a, b, n):
    """H1000Line.lser one a b n 0 a b 0."""
    i, pa, pb, acc = 0, a, b, 0
    for _ in range(n):
        acc, i, pa, pb = acc + pa * one // (pb * (i + 1)), i + 1, pa * a, pb * b
    return acc, pa, pb


def ln_box(a, b, nl):
    """H1000Line.lnBox a b nl."""
    r1, pa, pb = lser(ONE, a, b, nl)
    EU = pa * ONE * b // (pb * (b - a)) + 1
    return r1 - EU, r1 + nl + EU


def AA(tn, tq):
    return 2 ** tq * 2 ** tq + 4 * tn * tn


def phase_ok(tn, tq, k):
    A = AA(tn, tq)
    return 2 ** k <= A and A < 2 * 2 ** k and 2 * tq + 4 <= k and 1 <= tn and 2 ** tq <= 2 * tn


def inner_box(tn, tq, k, nl):
    j = max(k - (2 * tq + 4), 0)
    lb = ln_box(AA(tn, tq) - 2 ** k, AA(tn, tq), nl)
    return j * L2LO + lb[0], j * L2HI + lb[1]


def phase_lo(tn, tq, k, nl):
    u = 2 ** tq
    return (fdiv(inner_box(tn, tq, k, nl)[0] * tn, 4 * u)
            + (fdiv(u * ONE, 8 * tn) - cdiv(u * u * u * ONE, 96 * tn * tn * tn) - P8HI)
            + fdiv(-(tn * ONE), 2 * u)
            + fdiv(-(tn * LPHI), 2 * u)
            - cdiv(u * ONE, 2 * tn))


def phase_hi(tn, tq, k, nl):
    u = 2 ** tq
    return (cdiv(inner_box(tn, tq, k, nl)[1] * tn, 4 * u)
            + (cdiv(u * ONE, 8 * tn) - P8LO)
            + cdiv(-(tn * ONE), 2 * u)
            + cdiv(-(tn * LPLO), 2 * u))


# ------------------------------------------------------------------ exact mirror of H1000Point

class Pt:
    __slots__ = ("tn", "tq", "N", "s1", "s2", "Q", "r", "k", "nl", "m", "pos")

    def __init__(self, **kw):
        for key, val in kw.items():
            setattr(self, key, val)


def cfg_of(p):
    return M.make_cfg(64, p.tn, p.tq, lnbig=256, sqbig=256)


def dir_ok(p, c):
    if p.N < 2:
        return False
    s1 = M.run(c, M.init_state(c), p.N - 2)
    s2 = M.run(c, p.s1, 1)
    return s1 == p.s1 and s2 == p.s2


def zball(p):
    u = 2 ** p.tq
    ok, EN, ED = G.rem_odd(KEM, u, p.tn, p.N, p.Q, p.r)
    BreN, BimN, BD = G.corr_data(KEM, u, p.tn, p.N)
    s1, s2 = p.s1, p.s2
    a1, b1 = s1.reP - s1.reN, s1.imP - s1.imN
    za, zb = (s2.reP - s2.reN) - a1, (s2.imP - s2.imN) - b1
    zra, zrb = s2.reR + s1.reR, s2.imR + s1.imR
    zcX = ED * (a1 * BD + za * BreN - zb * BimN)
    zrX = ED * (s1.reR * BD + zra * abs(BreN) + zrb * abs(BimN)) + BD * EN * ONE
    zcY = ED * (b1 * BD + za * BimN + zb * BreN)
    zrY = ED * (s1.imR * BD + zra * abs(BimN) + zrb * abs(BreN)) + BD * EN * ONE
    zW = ONE * BD * ED
    return ok, ED, zcX, zrX, zcY, zrY, zW


def th_lo(p):
    return phase_lo(p.tn, p.tq, p.k, p.nl) + p.m * TPLO


def th_hi(p):
    return phase_hi(p.tn, p.tq, p.k, p.nl) + p.m * TPHI


def sgnI(b):
    return 1 if b else -1


def pt_check(p, check_dir=True):
    """H1000Line.ptCheck p (returns (ok, info))."""
    c = cfg_of(p)
    if check_dir and not dir_ok(p, c):
        return False, {"why": "dir"}
    okR, ED, zcX, zrX, zcY, zrY, zW = zball(p)
    if not (okR and ED > 0):
        return False, {"why": "rem"}
    if not phase_ok(p.tn, p.tq, p.k):
        return False, {"why": "phaseOk"}
    lo, hi = th_lo(p), th_hi(p)
    if lo < 0:
        return False, {"why": "thLo<0"}
    (cm, cs, cr), (sm, ss, sr) = M.trig(c, max(lo, 0), max(hi, 0))
    ctr = sgnI(cs) * cm * zcX - sgnI(ss) * sm * zcY
    rad = cr * (abs(zcX) + zrX) + cm * zrX + sr * (abs(zcY) + zrY) + sm * zrY
    ok = (rad < ctr) if p.pos else (ctr + rad < 0)
    return ok, {"val": ctr / (ONE * zW), "err": rad / (ONE * zW)}


def band_ok(T0n, T0d, T1n, T1d, n, ps):
    """H1000Line.bandOk."""
    if len(ps) != n + 1 or T0d <= 0 or T1d <= 0:
        return False
    for a, b in zip(ps, ps[1:]):
        if not (a.tn * 2 ** b.tq < b.tn * 2 ** a.tq and a.pos != b.pos):
            return False
    if not T0n * 2 ** ps[0].tq <= ps[0].tn * T0d:
        return False
    if not ps[-1].tn * T1d <= T1n * 2 ** ps[-1].tq:
        return False
    return True


# ------------------------------------------------------------------ point construction

def make_point(tn, tq, pos, eps, nl):
    """Build a point at t = tn / 2^tq with the minimal EM cut for remainder <= eps."""
    u = 2 ** tq
    N = max(G.minimal_N(KEM, tn, eps, odd=True, u=u), 3)
    Q = G.q_for(KEM, u, tn, True)
    r = math.isqrt(N)
    A = AA(tn, tq)
    k = A.bit_length() - 1
    m = 0
    while phase_lo(tn, tq, k, nl) + m * TPLO < 0:
        m += 1
    c = M.make_cfg(64, tn, tq, lnbig=256, sqbig=256)
    s1 = M.run(c, M.init_state(c), N - 2)
    s2 = M.step(c, s1)
    return Pt(tn=tn, tq=tq, N=N, s1=s1, s2=s2, Q=Q, r=r, k=k, nl=nl, m=m, pos=pos)


def load_zeros(path):
    if path and os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    import mpmath
    mpmath.mp.dps = 30
    zs, n = [], 1
    while True:
        t = float(mpmath.zetazero(n).imag)
        if t > 1001:
            break
        zs.append(t)
        n += 1
    if path:
        with open(path, "w") as f:
            json.dump(zs, f)
    return zs


def band_points(bi, zs, tq, nl):
    """Choose and certify the n+1 grid points of band bi (mirror-checked)."""
    import mpmath
    mpmath.mp.dps = 25
    T0n, T0d, T1n, T1d, n = BANDS[bi]
    T0, T1 = T0n / T0d, T1n / T1d
    inb = [z for z in zs if T0 <= z <= T1]
    assert len(inb) == n, (bi, len(inb), n)
    edges = [T0] + inb + [T1]
    lo_tn = -(-(T0n * 2 ** tq) // T0d)          # ceil(T0 * 2^tq)
    hi_tn = (T1n * 2 ** tq) // T1d              # floor(T1 * 2^tq)
    pts, info = [], []
    for i in range(n + 1):
        a, b = edges[i], edges[i + 1]
        cands = []
        for j in range(1, 40):
            cands.append(a + (b - a) * j / 40)
        if i == 0:
            cands.append(T0)
        if i == n:
            cands.append(T1)
        scored = sorted(((abs(float(mpmath.siegelz(t))), t) for t in cands), reverse=True)
        done = False
        for zabs, t in scored:
            tn = round(t * 2 ** tq)
            tn = min(max(tn, lo_tn), hi_tn)
            tt = tn / 2 ** tq
            if not (a < tt < b or (i == 0 and tt == T0 and T0 < inb[0]) or (i == n and tt == T1 and T1 > inb[-1])):
                continue
            z = float(mpmath.siegelz(tt))
            if z == 0:
                continue
            pos = z > 0
            eps = min(1e-3, abs(z) / 50)
            p = make_point(tn, tq, pos, eps, nl)
            ok, inf = pt_check(p, check_dir=False)
            if ok:
                pts.append(p)
                info.append({"t": tt, "Z": z, "N": p.N, "val": inf["val"], "err": inf["err"], "m": p.m})
                done = True
                break
        if not done:
            raise RuntimeError("band %d: no certifiable point in (%g, %g)" % (bi, a, b))
    assert band_ok(T0n, T0d, T1n, T1d, n, pts), bi
    # signs must alternate by the true zero count (checked by band_ok); every sign agrees with Z
    return pts, info


# ------------------------------------------------------------------ Lean emission

def st_lean(s):
    return M.st_lean(s)


def pt_lean(p):
    return "⟨%d, %d, %d, %s, %s, %d, %d, %d, %d, %d, %s⟩" % (
        p.tn, p.tq, p.N, st_lean(p.s1), st_lean(p.s2), p.Q, p.r, p.k, p.nl, p.m,
        "true" if p.pos else "false")


def real_lit(num, den):
    return "(%d : ℝ)" % num if den == 1 else "(%d / %d : ℝ)" % (num, den)


def emit_band(bi, pts, info, outdir):
    T0n, T0d, T1n, T1d, n = BANDS[bi]
    tag = "B%02d" % bi
    mod = "H1000Line_%s" % tag
    ns = "H1000Line.%s" % tag
    L = []
    L.append("/-  %s.lean -- band %d of the height-1000 segment: `hLine` of `BandGlue_h1000.seg %d`" % (mod, bi, bi))
    L.append("    (GENERATED by telperion/examples/zeta_reflection/emit_h1000_line.py; do not edit).")
    L.append("")
    L.append("    Band [%s, %s], n = %d on-line zeros.  %d grid points t = tn / 2^tq, each certified by ONE" % (
        "%d/%d" % (T0n, T0d) if T0d != 1 else T0n, "%d/%d" % (T1n, T1d) if T1d != 1 else T1n, n, n + 1))
    L.append("    `decide +kernel` run of `H1000Line.ptCheck` (Dirichlet chunks, order-13 Euler-Maclaurin ball,")
    L.append("    RS-phase bracket, trig, product-ball sign test); `band` checks order, edges and alternation;")
    L.append("    `lineHyp` is the band's verbatim `hLine` (`H1000Line.band_sound`).  No hypotheses.")
    L.append("    Grid (t, Z(t) by mpmath [untrusted, placement only], EM cut N, certified S, radius):")
    for j, d in enumerate(info):
        L.append("      p%-3d t = %-12.6f Z = %+.5f  N = %-4d S = %+.5f +- %.5f%s" % (
            j, d["t"], d["Z"], d["N"], d["val"], d["err"], "  (2 pi shift)" if d["m"] else ""))
    L.append("    conjecture1_proved = False.  Finite interval arithmetic and the IVT; nothing about RH.")
    L.append("-/")
    L.append("import H1000Line")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    for j, p in enumerate(pts):
        L.append("def p%d : H1000Line.LinePt :=" % j)
        L.append("  %s" % pt_lean(p))
        L.append("theorem ok%d : H1000Line.ptCheck p%d = true := by decide +kernel" % (j, j))
        L.append("")
    L.append("/-- The band's grid, in increasing order. -/")
    L.append("def pts : List H1000Line.LinePt := [%s]" % ", ".join("p%d" % j for j in range(len(pts))))
    L.append("")
    L.append("theorem all : H1000Line.AllOk pts :=")
    expr = "H1000Line.AllOk.nil"
    for j in reversed(range(len(pts))):
        expr = "H1000Line.AllOk.cons ok%d (%s)" % (j, expr)
    L.append("  %s" % expr)
    L.append("")
    L.append("theorem band : H1000Line.bandOk %d %d %d %d %d pts = true := by decide +kernel" % (T0n, T0d, T1n, T1d, n))
    L.append("")
    L.append("/-- **`hLine` of band %d**: %d strictly increasing zeros of `completedRiemannZeta` on the" % (bi, n))
    L.append("    critical line in `[T0, T1]`, kernel-checked, no hypotheses. -/")
    L.append("theorem lineHyp : ∃ xs : List ℝ, xs.length = %d ∧ xs.IsChain (· < ·) ∧" % n)
    L.append("    (∀ t ∈ xs, %s ≤ t ∧ t ≤ %s) ∧" % (real_lit(T0n, T0d), real_lit(T1n, T1d)))
    L.append("    (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :=")
    L.append("  H1000Line.band_sound %s %s %d %d %d %d %d (by norm_num) (by norm_num) pts all band" % (
        real_lit(T0n, T0d), real_lit(T1n, T1d), T0n, T0d, T1n, T1d, n))
    L.append("")
    L.append("end")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    path = os.path.join(outdir, mod + ".lean")
    with open(path, "w") as f:
        f.write("\n".join(L))
    return mod, path


def cap_numbers(leandir):
    """(t0, t1, cim, q) of every band, as Lean literals, from BandGlue_h1000.seg_geom."""
    import re
    src = open(os.path.join(leandir, "BandGlue_h1000.lean")).read()
    rows = re.findall(r"CapGeom\.of_sqrt \(δ0 := [^)]*\)\) \(δ1 := [^)]*\)\) (\(.*?\)) (\(.*?\)) (\(.*?\)) (\(.*?\))\n", src)
    assert len(rows) == 25, len(rows)
    return rows


def emit_all(outdir, bands):
    L = []
    L.append("/-  H1000Line_All.lean -- `hLine` of ALL 25 bands of the height-1000 segment, and the ladder")
    L.append("    statement from the remaining inputs only")
    L.append("    (GENERATED by telperion/examples/zeta_reflection/emit_h1000_line.py; do not edit).")
    L.append("")
    L.append("    * `seg_lineHyp`   : `(BandGlue_h1000.seg i).LineHyp` for every `i < 25` (bands `H1000Line_B00..B24`).")
    L.append("    * `lineHyp_of_edges` : the same `hLine` for ANY `BandGlue.BandData` with the segment band's")
    L.append("                        `T0`, `T1`, `n` (so an integration stage may re-choose the enclosure")
    L.append("                        data of a band, e.g. wider kernel-provable boxes, and keep this `hLine`).")
    L.append("    * `all_nontrivial_zeros_up_to_height_1000_of_certs` : the same statement by the certificate route")
    L.append("                        (any band data with the same `T0`, `T1`, `n`, its own enclosures and pins).")
    L.append("    * `all_nontrivial_zeros_up_to_height_1000_of_offline` : the height-1000 ladder statement with")
    L.append("                        `hLine` (here) and `hγ` (`HeightFloor.height_floor`) discharged; the only")
    L.append("                        remaining inputs are, per band, the two edge-clearance slabs and the five")
    L.append("                        RvM enclosures (`BandGlue.BandData.ReducedInputs` minus `LineHyp`).")
    L.append("    * `segWith_valid` : `BandGlue.BandData.Valid` for band `i` with ANY enclosures `E` satisfying")
    L.append("                        the two pins (`H1000Glue.PinOk`).")
    L.append("    * `all_nontrivial_zeros_up_to_height_1000_of_encl` : THE INTEGRATION TARGET -- the ladder")
    L.append("                        statement from, per band, enclosure data `E i`, its pins, its five")
    L.append("                        enclosures, and the edge-clearance slabs (49 of them: band 0's lower")
    L.append("                        slab is discharged by the height floor, `H1000Glue.slab0_band0`).")
    L.append("    Axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.")
    L.append("    conjecture1_proved = False.")
    L.append("-/")
    for bi in bands:
        L.append("import H1000Line_B%02d" % bi)
    L.append("import H1000Glue")
    L.append("")
    L.append("namespace H1000Line")
    L.append("")
    L.append("/-- **`hLine` of every band of `AllZeros_h1000`**, kernel-checked (no hypotheses). -/")
    L.append("theorem seg_lineHyp : ∀ i, i < 25 → (BandGlue_h1000.seg i).LineHyp := by")
    L.append("  intro i hi")
    L.append("  interval_cases i")
    for bi in bands:
        L.append("  · exact H1000Line.B%02d.lineHyp" % bi)
    L.append("")
    L.append("/-- `hLine` depends on a band only through `T0`, `T1`, `n`. -/")
    L.append("theorem lineHyp_of_edges (i : ℕ) (hi : i < 25) (d : BandGlue.BandData)")
    L.append("    (h0 : d.T0 = (BandGlue_h1000.seg i).T0) (h1 : d.T1 = (BandGlue_h1000.seg i).T1)")
    L.append("    (hn : d.n = (BandGlue_h1000.seg i).n) : d.LineHyp := by")
    L.append("  have h := seg_lineHyp i hi")
    L.append("  unfold BandGlue.BandData.LineHyp at h ⊢")
    L.append("  rw [h0, h1, hn]")
    L.append("  exact h")
    L.append("")
    L.append("/-- **The height-1000 ladder statement from the OFF-LINE inputs only.**  `hLine` of all 25 bands")
    L.append("    (this lane) and the height floor `hγ` (`HeightFloor.height_floor`) are discharged; what remains")
    L.append("    per band is the edge clearance below `T0` and above `T1` (heights `capLo i`, `capHi i`) and the")
    L.append("    five RvM argument-change enclosures `EnclHyp`. -/")
    L.append("theorem all_nontrivial_zeros_up_to_height_1000_of_offline")
    L.append("    (hslab0 : ∀ i, i < 25 → EdgeClearGlue.SlabClear ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i)")
    L.append("      (BandGlue_h1000.seg i).T0)")
    L.append("    (hslab1 : ∀ i, i < 25 → EdgeClearGlue.SlabClear (BandGlue_h1000.seg i).T1")
    L.append("      ((BandGlue_h1000.seg i).T1 + BandGlue_h1000.capHi i))")
    L.append("    (henc : ∀ i, i < 25 → (BandGlue_h1000.seg i).EnclHyp) :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  BandGlue_h1000.all_nontrivial_zeros_up_to_height_1000_of_reduced")
    L.append("    (fun i hi => ⟨seg_lineHyp i hi, hslab0 i hi, hslab1 i hi, henc i hi⟩)")
    L.append("    (HeightFloor.height_floor 1000)")
    L.append("")
    L.append("/-- **The certificate route.**  The integration stage may re-choose each band's enclosure data")
    L.append("    (e.g. wider kernel-provable enclosures, as long as the pins of `Valid` hold) and ball geometry:")
    L.append("    for every band, ANY `BandGlue.BandData` with the segment band's `T0`, `T1`, `n`, its decidable")
    L.append("    side conditions `Valid`, the K1 cap geometry, the two edge-clearance slabs and ITS five")
    L.append("    enclosures gives the band's box claim, `hLine` being supplied by this lane and `hγ` by")
    L.append("    `HeightFloor`. -/")
    L.append("theorem all_nontrivial_zeros_up_to_height_1000_of_certs")
    L.append("    (hcert : ∀ i, i < 25 → ∃ d : BandGlue.BandData, ∃ δ0 δ1 : ℝ,")
    L.append("      d.T0 = (BandGlue_h1000.seg i).T0 ∧ d.T1 = (BandGlue_h1000.seg i).T1 ∧")
    L.append("      d.n = (BandGlue_h1000.seg i).n ∧ d.Valid (1 / 4000000) (3999999 / 4000000) ∧")
    L.append("      d.CapGeom δ0 δ1 ∧ EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0 ∧")
    L.append("      EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1) ∧ d.EnclHyp) :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by")
    L.append("  apply AllZeros_h1000.all_nontrivial_zeros_up_to_height_1000_of_bands _ (HeightFloor.height_floor 1000)")
    L.append("  intro i hi")
    L.append("  obtain ⟨d, δ0, δ1, h0, h1, hn, hV, hG, hs0, hs1, hE⟩ := hcert i hi")
    L.append("  have hL : d.LineHyp := lineHyp_of_edges i hi d h0 h1 hn")
    L.append("  have hc : BandGlue.BoxCert (1 / 4000000) (3999999 / 4000000) (AllZeros_h1000.bLo i)")
    L.append("      (AllZeros_h1000.bHi i) :=")
    L.append("    BandGlue.BoxCert.of_valid d (by rw [h0]; exact (BandGlue_h1000.seg_edge i hi).1)")
    L.append("      (by rw [h1]; exact (BandGlue_h1000.seg_edge i hi).2) hV")
    L.append("      (BandGlue.BandData.inputs_of_reduced hG ⟨hL, hs0, hs1, hE⟩)")
    L.append("  exact hc.box")
    L.append("")
    L.append("/-- `Valid` for band `i` with ANY enclosures `E` satisfying the two pins: the band's ball-cover")
    L.append("    geometry is re-proved from its explicit numbers (`H1000Glue.valid_of_sqrt`). -/")
    L.append("theorem segWith_valid (i : ℕ) (hi : i < 25) (E : Encl) (hp : PinOk i E) :")
    L.append("    (segWith i E).Valid (1 / 4000000) (3999999 / 4000000) := by")
    L.append("  interval_cases i")
    caps = cap_numbers(outdir)
    for bi in bands:
        t0, t1, cim, q = caps[bi]
        n = BANDS[bi][4]
        L.append("  · exact valid_of_sqrt _ %s %s %s %s rfl rfl rfl rfl (by show 1 ≤ %d; norm_num)" % (t0, t1, cim, q, n))
        L.append("      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
        L.append("      (by norm_num) hp.1 hp.2")
    L.append("")
    L.append("/-- **THE INTEGRATION TARGET: the height-1000 ladder statement from the off-line facts only.**")
    L.append("    Per band `i < 25`: enclosure data `E i` with its two pins (`PinOk`, decidable), its five RvM")
    L.append("    enclosures (`(segWith i (E i)).EnclHyp`), the edge clearance above `T1` (`hslab1`) and, for")
    L.append("    `i ≥ 1`, below `T0` (`hslab0`; band 0's lower slab is `slab0_band0`).  `hLine` (this lane),")
    L.append("    `hnzl` (EdgeClearGlue), `hγ` (HeightFloor), the ball geometry and the band statements are")
    L.append("    all discharged. -/")
    L.append("theorem all_nontrivial_zeros_up_to_height_1000_of_encl (E : ℕ → Encl)")
    L.append("    (hpin : ∀ i, i < 25 → PinOk i (E i))")
    L.append("    (henc : ∀ i, i < 25 → (segWith i (E i)).EnclHyp)")
    L.append("    (hslab0 : ∀ i, 1 ≤ i → i < 25 → EdgeClearGlue.SlabClear")
    L.append("      ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i) (BandGlue_h1000.seg i).T0)")
    L.append("    (hslab1 : ∀ i, i < 25 → EdgeClearGlue.SlabClear (BandGlue_h1000.seg i).T1")
    L.append("      ((BandGlue_h1000.seg i).T1 + BandGlue_h1000.capHi i)) :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 := by")
    L.append("  apply all_nontrivial_zeros_up_to_height_1000_of_certs")
    L.append("  intro i hi")
    L.append("  have hs0 : EdgeClearGlue.SlabClear ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i)")
    L.append("      (BandGlue_h1000.seg i).T0 := by")
    L.append("    rcases Nat.eq_zero_or_pos i with h | h")
    L.append("    · subst h; exact slab0_band0")
    L.append("    · exact hslab0 i h hi")
    L.append("  exact ⟨segWith i (E i), BandGlue_h1000.capLo i, BandGlue_h1000.capHi i, rfl, rfl, rfl,")
    L.append("    segWith_valid i hi (E i) (hpin i hi), capGeom_segWith (E i) (BandGlue_h1000.seg_geom i hi),")
    L.append("    hs0, hslab1 i hi, henc i hi⟩")
    L.append("")
    L.append("end H1000Line")
    L.append("")
    path = os.path.join(outdir, "H1000Line_All.lean")
    with open(path, "w") as f:
        f.write("\n".join(L))
    return path


CORE_THEOREMS = {
    "H1000Phase": ["fdiv_le", "le_cdiv", "ONE_eq", "lser_zero", "lser_succ", "lser_spec", "lser_spec0",
                   "lnBox_sound", "log2_scaled", "logpi_scaled", "pi8_scaled", "twopi_scaled",
                   "phaseOk_spec", "log_inner_eq", "innerBox_sound", "arctan_part", "phase_sound"],
    "H1000Point": ["dirOk_sound", "ball_scale", "zball_sound", "prod_ball", "sgnI_cast", "trig_phase",
                   "s_ball", "gLine_eq_mag_mul"],
    "H1000Line": ["ptCheck_unfold", "ptCheck_spec", "ptCheck_sound", "tlt_sound", "chainOk_get",
                  "AllOk.nil", "AllOk.cons", "AllOk_get", "firstGe_sound", "lastLe_sound", "band_sound"],
    "H1000Line_All": ["seg_lineHyp", "lineHyp_of_edges", "all_nontrivial_zeros_up_to_height_1000_of_offline",
                      "all_nontrivial_zeros_up_to_height_1000_of_certs", "segWith_valid",
                      "all_nontrivial_zeros_up_to_height_1000_of_encl"],
    "H1000Glue": ["box_ball_of_sqrt", "valid_of_sqrt", "capGeom_segWith", "slabClear_low", "slab0_band0"],
}


def emit_guard(outdir, npts):
    """AxiomGuardH1000Line.lean: #print axioms for EVERY new theorem, plus binder-shape checks."""
    L = []
    L.append("/-  AxiomGuardH1000Line.lean -- kernel guard (`#print axioms`) of lane h1000-prep")
    L.append("    (GENERATED by telperion/examples/zeta_reflection/emit_h1000_line.py; do not edit).")
    L.append("")
    L.append("    Prints `#print axioms` for every theorem of H1000Phase, H1000Point, H1000Line, the 25 band")
    L.append("    modules H1000Line_B00..B24 (every `ok_i`, `all`, `band`, `lineHyp`) and H1000Line_All.")
    L.append("    Expected: each line is a subset of [propext, Classical.choice, Quot.sound].  The `example`s")
    L.append("    re-state the two integration-facing results with their intended types, so a drift in the")
    L.append("    statement is a type error here.  conjecture1_proved = False.")
    L.append("-/")
    L.append("import H1000Line_All")
    L.append("")
    for mod in ["H1000Phase", "H1000Point", "H1000Line", "H1000Glue", "H1000Line_All"]:
        for th in CORE_THEOREMS[mod]:
            L.append("#print axioms H1000Line.%s" % th)
    for bi in range(25):
        for j in range(npts[bi]):
            L.append("#print axioms H1000Line.B%02d.ok%d" % (bi, j))
        for th in ["all", "band", "lineHyp"]:
            L.append("#print axioms H1000Line.B%02d.%s" % (bi, th))
    L.append("")
    L.append("/-- `hLine` of every band of the height-1000 segment, hypothesis-free. -/")
    L.append("example : ∀ i, i < 25 → (BandGlue_h1000.seg i).LineHyp := H1000Line.seg_lineHyp")
    L.append("")
    L.append("/-- The ladder statement from the off-line inputs only (hLine and hγ discharged). -/")
    L.append("example")
    L.append("    (hslab0 : ∀ i, i < 25 → EdgeClearGlue.SlabClear ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i)")
    L.append("      (BandGlue_h1000.seg i).T0)")
    L.append("    (hslab1 : ∀ i, i < 25 → EdgeClearGlue.SlabClear (BandGlue_h1000.seg i).T1")
    L.append("      ((BandGlue_h1000.seg i).T1 + BandGlue_h1000.capHi i))")
    L.append("    (henc : ∀ i, i < 25 → (BandGlue_h1000.seg i).EnclHyp) :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  H1000Line.all_nontrivial_zeros_up_to_height_1000_of_offline hslab0 hslab1 henc")
    L.append("")
    L.append("/-- The integration target: enclosure data, pins, enclosures and 49 slabs only. -/")
    L.append("example (E : ℕ → H1000Line.Encl) (hpin : ∀ i, i < 25 → H1000Line.PinOk i (E i))")
    L.append("    (henc : ∀ i, i < 25 → (H1000Line.segWith i (E i)).EnclHyp)")
    L.append("    (hslab0 : ∀ i, 1 ≤ i → i < 25 → EdgeClearGlue.SlabClear")
    L.append("      ((BandGlue_h1000.seg i).T0 - BandGlue_h1000.capLo i) (BandGlue_h1000.seg i).T0)")
    L.append("    (hslab1 : ∀ i, i < 25 → EdgeClearGlue.SlabClear (BandGlue_h1000.seg i).T1")
    L.append("      ((BandGlue_h1000.seg i).T1 + BandGlue_h1000.capHi i)) :")
    L.append("    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 1000 → ρ.re = 1 / 2 :=")
    L.append("  H1000Line.all_nontrivial_zeros_up_to_height_1000_of_encl E hpin henc hslab0 hslab1")
    L.append("")
    import re
    src = open(os.path.join(outdir, "BandGlue_h1000.lean")).read()
    mods = re.findall(r"exact (RHInBoxT_[0-9a-z_]+)\.statement_match", src)
    assert len(mods) == 25, len(mods)
    L.append("/-! Each band's own `rh_in_box_*` theorem accepts this lane's `lineHyp` as its `hLine` argument")
    L.append("    (so the binder and the proved statement agree verbatim, band by band). -/")
    for bi, mod in enumerate(mods):
        L.append("example := %s.%s H1000Line.B%02d.lineHyp" % (mod, mod.replace("RHInBoxT_", "rh_in_box_"), bi))
    L.append("")
    path = os.path.join(outdir, "AxiomGuardH1000Line.lean")
    with open(path, "w") as f:
        f.write("\n".join(L))
    return path


def parse_range(s):
    out = []
    for part in s.split(","):
        if "-" in part:
            a, b = part.split("-")
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return out


def main():
    argv = sys.argv[1:]
    opts = {}
    i = 0
    while i < len(argv):
        opts[argv[i].lstrip("-")] = argv[i + 1]
        i += 2
    bands = parse_range(opts.get("bands", "0-24"))
    outdir = opts.get("outdir", os.path.join(HERE, "lean"))
    tq = int(opts.get("tq", 10))
    nl = int(opts.get("nl", 48))
    zeros = load_zeros(opts.get("zeros"))
    summary = {"bands": {}, "tq": tq, "nl": nl, "conjecture1_proved": False}
    t0 = time.time()
    for bi in bands:
        tb = time.time()
        pts, info = band_points(bi, zeros, tq, nl)
        # full re-check including the Dirichlet chunks (as the kernel will)
        for p in pts:
            ok, _ = pt_check(p, check_dir=True)
            assert ok, (bi, p.tn)
        mod, path = emit_band(bi, pts, info, outdir)
        summary["bands"][bi] = {"module": mod, "points": len(pts), "terms": sum(p.N for p in pts),
                                "worst_ratio": min(abs(d["val"]) / d["err"] for d in info),
                                "min_abs_S": min(abs(d["val"]) for d in info),
                                "py_seconds": round(time.time() - tb, 2)}
        print("band %2d: %s, %d points, %d terms, worst |S|/err %.1f (%.1fs)" % (
            bi, mod, len(pts), summary["bands"][bi]["terms"], summary["bands"][bi]["worst_ratio"],
            time.time() - tb), file=sys.stderr)
    if len(bands) == 25:
        summary["all"] = emit_all(outdir, bands)
        summary["guard"] = emit_guard(outdir, [summary["bands"][bi]["points"] for bi in range(25)])
    summary["total_points"] = sum(b["points"] for b in summary["bands"].values())
    summary["total_terms"] = sum(b["terms"] for b in summary["bands"].values())
    summary["seconds"] = round(time.time() - t0, 1)
    if "json" in opts:
        with open(opts["json"], "w") as f:
            json.dump(summary, f, indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "bands"}))


if __name__ == "__main__":
    main()
