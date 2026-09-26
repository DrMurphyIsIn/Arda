"""Generate an OFF-LINE order-(2K+1) Euler-Maclaurin enclosure instance of zeta(sigma + i t) in the
kernel-only format (lane offline, lean/EMZetaOfflineCheck.lean).

usage: gen_offline.py TAG a b q tn tq K N [--D 1000000000] [--chunk 500] [--Rd 4294967296]
  sigma = (a - b)/q, t = tn / 2^tq, K in 1..6, EM cut N (Dirichlet sum over n = 1..N-1).
writes ../lean/EMZetaOfflineI_<TAG>.lean: the chunk-boundary states, the kernel chunk theorems
(`decide +kernel` on `ArbEcon.Off.runO`), the invariant chain (`chunkO_sound`), ONE kernel check
`ArbEcon.Off.checkG ... = true` and the final theorem `zeta_box` from `checkG_sound`.
The Python side mirrors `checkG` exactly (integer arithmetic) and refuses to emit a failing check.
conjecture1_proved = False.
"""
import json
import math
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arbecon_model as M  # noqa: E402
import offline_model as O  # noqa: E402

LBETA = 1307674368000
BETAN = {0: 108972864000, 2: -1816214400, 4: 43243200, 6: -1081080, 8: 27300, 10: -691}


def betaN(i):
    return BETAN.get(i, 0)


def gpochG(sN, q, u, tn, k):
    x, y = 1, 0
    for j in range(k):
        re_, im_ = (sN + j * q) * u, tn * q
        x, y = x * re_ - y * im_, x * im_ + y * re_
    return x, y


def corr_data_g(K, sN, q, u, tn, N):
    M_ = 2 * K - 1
    W = q * u * N
    q2 = (sN - q) ** 2 * u ** 2 + tn ** 2 * q ** 2
    base = LBETA * W ** M_
    S1 = S2 = 0
    for j in range(M_):
        g = gpochG(sN, q, u, tn, j + 1)
        S1 += betaN(j) * g[0] * W ** (M_ - 1 - j)
        S2 += betaN(j) * g[1] * W ** (M_ - 1 - j)
    return (2 * N * q * u ** 2 * (sN - q) * base + q2 * base + 2 * q2 * S1,
            -(2 * N * q ** 2 * u * tn * base) + 2 * q2 * S2,
            2 * q2 * base)


def pnG(sN, q, u, tn, k):
    p = 1
    for j in range(k):
        p *= (sN + j * q) ** 2 * u ** 2 + tn ** 2 * q ** 2
    return p


def rem_odd_g(K, a, b, q, u, tn, N, Qp, Rn, Rd):
    sN = a - b
    ok = (1 <= Rd and 1 <= K and pnG(sN, q, u, tn, 2 * K + 1) <= Qp * Qp
          and Rd ** q * N ** b <= Rn ** q * N ** a and 0 < sN + 2 * K * q)
    EN = (2 * (6000000000000 * 2 ** (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ** (2 * K + 1)
          * Qp * Rn * q)
    ED = (6000000000000 * 2 ** (2 * K - 1) * 6283184 ** (2 * K + 1) * (q * u) ** (2 * K + 1) * Rd
          * N ** (2 * K) * (sN + 2 * K * q))
    return ok, EN, ED


def cert_Q_R(K, a, b, q, u, tn, N, Rd):
    sN = a - b
    p = pnG(sN, q, u, tn, 2 * K + 1)
    Qp = math.isqrt(p)
    if Qp * Qp < p:
        Qp += 1
    # smallest Rn with Rd^q N^b <= Rn^q N^a
    lhs = Rd ** q * N ** b
    sig = Fraction(a - b, q)
    guess = max(1, int(Rd * float(N) ** (-float(sig))) - 2)
    Rn = guess
    while Rn ** q * N ** a < lhs:
        Rn += 1
    while Rn > 1 and (Rn - 1) ** q * N ** a >= lhs:
        Rn -= 1
    return Qp, Rn


def core_terms(P, tq, tn, K, sN, q, N, x1, x2):
    u = 2 ** tq
    BreN, BimN, BD = corr_data_g(K, sN, q, u, tn, N)
    a1 = x1.reP - x1.reN
    b1 = x1.imP - x1.imN
    za = (x2.reP - x2.reN) - a1
    zb = (x2.imP - x2.imN) - b1
    zra = x2.reR + x1.reR
    zrb = x2.imR + x1.imR
    aB, aC = abs(BreN), abs(BimN)
    CreN = a1 * BD + za * BreN - zb * BimN
    RreN = x1.reR * BD + zra * aB + zrb * aC
    CimN = b1 * BD + za * BimN + zb * BreN
    RimN = x1.imR * BD + zra * aC + zrb * aB
    return dict(BD=BD, CreN=CreN, RreN=RreN, CimN=CimN, RimN=RimN)


def check_core_g(P, tq, tn, K, sN, q, N, x1, x2, D, reLo, reHi, imLo, imHi, EN, ED):
    x = core_terms(P, tq, tn, K, sN, q, N, x1, x2)
    BD, two = x["BD"], 2 ** P
    ok = 1 <= K <= 6 and 2 <= N and 1 <= D and 0 < ED and 1 <= q and 1 <= tn
    ok = ok and reLo * two * BD * ED <= D * ED * (x["CreN"] - x["RreN"]) - D * BD * EN * two
    ok = ok and D * ED * (x["CreN"] + x["RreN"]) + D * BD * EN * two <= reHi * two * BD * ED
    ok = ok and imLo * two * BD * ED <= D * ED * (x["CimN"] - x["RimN"]) - D * BD * EN * two
    ok = ok and D * ED * (x["CimN"] + x["RimN"]) + D * BD * EN * two <= imHi * two * BD * ED
    return ok


def bounds(P, tq, tn, K, sN, q, N, x1, x2, D, EN, ED):
    x = core_terms(P, tq, tn, K, sN, q, N, x1, x2)
    BD, two = x["BD"], 2 ** P
    E = Fraction(EN, ED)
    reC, reR = Fraction(x["CreN"], two * BD), Fraction(x["RreN"], two * BD) + E
    imC, imR = Fraction(x["CimN"], two * BD), Fraction(x["RimN"], two * BD) + E
    reLo = math.floor((reC - reR) * D)
    reHi = math.ceil((reC + reR) * D)
    imLo = math.floor((imC - imR) * D)
    imHi = math.ceil((imC + imR) * D)
    return reLo, reHi, imLo, imHi, (reC, reR, imC, imR, E)


def complex_lit(x):
    x = Fraction(x)
    if x.denominator == 1:
        return "(%d : ℂ)" % x.numerator
    return "(%d / %d : ℂ)" % (x.numerator, x.denominator)


def real_lit(x):
    """a rational as a Lean real literal: `(3 / 10 : ℝ)`, `(1000 : ℝ)`, `(-1 : ℝ)`"""
    x = Fraction(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)


def generate(tag, a, b, q, tn, tq, K, N, D=10 ** 9, chunk=500, Rd=2 ** 32, outdir=None, write=True):
    c = M.make_cfg(64, tn, tq, lnbig=256, sqbig=256)
    o = O.make_ocfg(c, a, b, q)
    t0 = time.time()
    s = O.init_state(c, 0)
    states, lens = [s], []
    total, done = N - 2, 0
    fails = 0
    while done < total:
        L = min(chunk, total - done)
        for _ in range(L):
            if not O.ampl_ok(c, o, s.n + 1, s.g):
                fails += 1
            s = O.step(c, o, s)
        states.append(s)
        lens.append(L)
        done += L
    if not O.ampl_ok(c, o, s.n + 1, s.g):
        fails += 1
    sN = O.step(c, o, states[-1])
    pyt = time.time() - t0
    assert fails == 0, "amplitude validation fallback taken %d times" % fails
    assert states[-1].n == N - 1 and sN.n == N
    u = 2 ** tq
    Qp, Rn = cert_Q_R(K, a, b, q, u, tn, N, Rd)
    ok, EN, ED = rem_odd_g(K, a, b, q, u, tn, N, Qp, Rn, Rd)
    assert ok, "remainder certificate fails"
    x1, x2 = states[-1].acc[0], sN.acc[0]
    reLo, reHi, imLo, imHi, info = bounds(64, tq, tn, K, a - b, q, N, x1, x2, D, EN, ED)
    assert check_core_g(64, tq, tn, K, a - b, q, N, x1, x2, D, reLo, reHi, imLo, imHi, EN, ED)
    # negative control: shrink the real interval by one unit at the top -> must fail
    assert not check_core_g(64, tq, tn, K, a - b, q, N, x1, x2, D, reLo, reHi - (reHi - reLo), imLo, imHi, EN, ED)
    sig_r = real_lit(Fraction(a - b, q))
    t_r = real_lit(Fraction(tn, 2 ** tq))
    ns = "ArbEcon.Off.I_%s" % tag
    cfgt = "(ArbEcon.OrderK.cfg64 %d %d)" % (tn, tq)
    L = []
    L.append("/-  EMZetaOfflineI_%s.lean -- KERNEL-CHECKED order-%d Euler-Maclaurin enclosure of zeta(sigma + i t) OFF the" % (tag, 2 * K + 1))
    L.append("    critical line, sigma = (%d - %d)/%d, t = %d / 2^%d  (GENERATED by arbecon/gen_offline.py; do not edit)." % (a, b, q, tn, tq))
    L.append("")
    L.append("      * the Dirichlet sum over n = 1..%d: %d `decide +kernel` chunks of the off-line evaluator" % (N - 1, len(lens)))
    L.append("        `ArbEcon.Off.runO` at `EMZetaHighCfg64.cfg64 %d %d` (amplitude m^(-sigma) by a validated Newton" % (tn, tq))
    L.append("        root), composed by `ArbEcon.Off.chunkO_sound`, plus one step for the term n = %d;" % N)
    L.append("      * `check`: ONE `decide +kernel` run of `ArbEcon.Off.checkG` (exact correction factor, the")
    L.append("        order-%d odd-saw remainder valid for sigma > -2K, the four final inequalities, in Int);" % (2 * K + 1))
    L.append("      * `zeta_box` = `ArbEcon.Off.checkG_sound` (general, proved once).")
    L.append("    Certified: Re in [%s, %s], Im in [%s, %s] (denominator %d); remainder E = %.3g." % (
        reLo, reHi, imLo, imHi, D, float(info[4])))
    L.append("    conjecture1_proved = False.  One point, finite interval arithmetic; nothing about RH.")
    L.append("-/")
    L.append("import EMZetaOfflineCheck")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    L.append("def oc : ArbEcon.Off.OCfg := ⟨%d, %d, %d, %d, %d⟩" % (o.a, o.b, o.q, o.oneQ, o.nfuel))
    for i, st in enumerate(states):
        if i == 0:
            continue
        L.append("def s%d : ArbEcon.Off.StO := %s" % (i, O.st_lean(st)))
    L.append("def sN : ArbEcon.Off.StO := %s" % O.st_lean(sN))
    L.append("")
    L.append("end")
    L.append("")
    for i, Ln in enumerate(lens):
        src = "(ArbEcon.Off.StO.init %s 0)" % cfgt if i == 0 else "s%d" % i
        L.append("theorem chunk_%d : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc %d %s) s%d = true := by decide +kernel" % (
            i, cfgt, Ln, src, i + 1))
    L.append("theorem chunk_N : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc 1 s%d) sN = true := by decide +kernel" % (cfgt, len(lens)))
    L.append("")
    L.append("theorem ht : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (t_r, tn, tq))
    L.append("theorem hσ : %s = (((%d : ℕ) : ℝ) - ((%d : ℕ) : ℝ)) / ((%d : ℕ) : ℝ) := by norm_num" % (sig_r, a, b, q))
    L.append("theorem valid : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht" % (cfgt, t_r, tn, tq))
    L.append("theorem ovalid : ArbEcon.Off.OValid %s oc %s := ⟨by decide +kernel, by decide, hσ⟩" % (cfgt, sig_r))
    L.append("")
    L.append("theorem inv_0 : ArbEcon.Off.InvO %s %s %s 1 (ArbEcon.Off.StO.init %s 0) :=" % (cfgt, sig_r, t_r, cfgt))
    L.append("  ArbEcon.Off.initO_sound _ _ _ 0 valid.one_eq")
    n = 1
    for i, Ln in enumerate(lens):
        prev = "(ArbEcon.Off.StO.init %s 0)" % cfgt if i == 0 else "s%d" % i
        L.append("theorem inv_%d : ArbEcon.Off.InvO %s %s %s %d s%d :=" % (i + 1, cfgt, sig_r, t_r, n + Ln, i + 1))
        L.append("  ArbEcon.Off.chunkO_sound _ oc _ _ 9 valid ovalid %d %d %s s%d inv_%d chunk_%d" % (Ln, n, prev, i + 1, i, i))
        n += Ln
    L.append("theorem inv_N : ArbEcon.Off.InvO %s %s %s %d sN :=" % (cfgt, sig_r, t_r, N))
    L.append("  ArbEcon.Off.chunkO_sound _ oc _ _ 9 valid ovalid 1 %d s%d sN inv_%d chunk_N" % (N - 1, len(lens), len(lens)))
    L.append("")
    x1l, x2l = O.acc_lean(x1), O.acc_lean(x2)
    L.append("/-- The whole order-%d assembly as ONE kernel computation (Int arithmetic). -/" % (2 * K + 1))
    L.append("theorem check : ArbEcon.Off.checkG %s oc %d %d %s %s %d (%d) (%d) (%d) (%d) %d %d %d = true := by" % (
        cfgt, K, N, x1l, x2l, D, reLo, reHi, imLo, imHi, Qp, Rn, Rd))
    L.append("  decide +kernel")
    L.append("")
    zeta = "riemannZeta (((%s : ℝ) : ℂ) + ((%s : ℝ) : ℂ) * Complex.I)" % (sig_r, t_r)
    L.append("/-- Negative control: the same data with the real interval collapsed to its lower end is REJECTED")
    L.append("    by the kernel checker. -/")
    L.append("theorem check_neg : ArbEcon.Off.checkG %s oc %d %d %s %s %d (%d) (%d) (%d) (%d) %d %d %d = false := by" % (
        cfgt, K, N, x1l, x2l, D, reLo, reLo, imLo, imHi, Qp, Rn, Rd))
    L.append("  decide +kernel")
    L.append("")
    L.append("/-- **Re and Im of zeta(sigma + i t)**, sigma = (%d - %d)/%d, t = %d/2^%d: kernel-checked, no hypotheses. -/" % (a, b, q, tn, tq))
    L.append("theorem zeta_box :")
    L.append("    (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ) ≤ (%s).re ∧" % (reLo, D, zeta))
    L.append("      (%s).re ≤ ((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) ∧" % (zeta, reHi, D))
    L.append("    (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ) ≤ (%s).im ∧" % (imLo, D, zeta))
    L.append("      (%s).im ≤ ((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) :=" % (zeta, imHi, D))
    L.append("  ArbEcon.Off.checkG_sound %s oc _ _ hσ ht %d %d _ _" % (cfgt, K, N))
    L.append("    (ArbEcon.Off.accOK_head _ _ _ _ _ _ _ inv_%d rfl) (ArbEcon.Off.accOK_head _ _ _ _ _ _ _ inv_N rfl)" % len(lens))
    L.append("    %d (%d) (%d) (%d) (%d) %d %d %d check" % (D, reLo, reHi, imLo, imHi, Qp, Rn, Rd))
    L.append("")
    zc = "riemannZeta (%s + %s * Complex.I)" % (complex_lit(Fraction(a - b, q)), complex_lit(Fraction(tn, 2 ** tq)))
    L.append("/-- Literal form (cast normalisation only): `zeta(sigma + i t)` with complex literals. -/")
    L.append("theorem zeta_re_im :")
    L.append("    ((%d / %d : ℝ) ≤ (%s).re ∧ (%s).re ≤ (%d / %d : ℝ)) ∧" % (reLo, D, zc, zc, reHi, D))
    L.append("    ((%d / %d : ℝ) ≤ (%s).im ∧ (%s).im ≤ (%d / %d : ℝ)) := by" % (imLo, D, zc, zc, imHi, D))
    L.append("  have h := zeta_box")
    L.append("  push_cast at h")
    L.append("  exact h")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    if outdir is None:
        outdir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean")
    fname = os.path.join(outdir, "EMZetaOfflineI_%s.lean" % tag)
    if write:
        with open(fname, "w") as f:
            f.write("\n".join(L))
    return dict(tag=tag, sigma=float(Fraction(a - b, q)), t=tn / 2 ** tq, K=K, N=N, chunks=len(lens),
                re=[reLo / D, reHi / D], im=[imLo / D, imHi / D], E=float(info[4]),
                re_rad=float(info[1]), py_s=round(pyt, 3), Qp_digits=len(str(Qp)), Rn=Rn, Rd=Rd, file=fname)


def main():
    argv = sys.argv[1:]
    opts, args, i = {}, [], 0
    while i < len(argv):
        if argv[i].startswith("--"):
            opts[argv[i][2:]] = argv[i + 1]
            i += 2
        else:
            args.append(argv[i])
            i += 1
    tag = args[0]
    a, b, q, tn, tq, K, N = map(int, args[1:8])
    r = generate(tag, a, b, q, tn, tq, K, N, D=int(opts.get("D", 10 ** 9)), chunk=int(opts.get("chunk", 500)),
                 Rd=int(opts.get("Rd", 2 ** 32)))
    print(json.dumps(r, indent=1))


if __name__ == "__main__":
    main()
