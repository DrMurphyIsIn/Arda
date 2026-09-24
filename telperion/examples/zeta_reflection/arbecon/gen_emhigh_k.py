"""Generate an order-(2K+1) Euler-Maclaurin instance in the KERNEL-ONLY format (lane emhigh).

usage: gen_emhigh_k.py TAG tn K N [--tq Q] [--chunk C] [--cpf F] [--outdir DIR] [--digits D]
  height t = tn / 2^tq, K in 1..6, EM cut N (Dirichlet sum over n = 1..N-1).
writes (OUTDIR default = ../lean):
  EMZetaHighK_<TAG>_Cfg.lean  the chunk-boundary states only (config = EMZetaHighCfg64.cfg64 tn tq)
  EMZetaHighK_<TAG>_P<j>.lean kernel chunk theorems (decide +kernel)
  EMZetaHighK_<TAG>.lean      assembly: invariant chain (ArbEcon.chunk_sound + valid64), ONE kernel
                              check `EMZetaHighCheck.checkK … = true` (decide +kernel), and the final
                              theorem `zeta_box` from `EMZetaHighCheck.checkK_sound` -- no norm_num.
The Python side mirrors `checkK` exactly (integer arithmetic) and refuses to emit a failing check.
Prints a JSON summary.  conjecture1_proved = False.
"""
import sys
import os
import json
import time
import math
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arbecon_model as M

LBETA = 1307674368000
BETAN = {0: 108972864000, 2: -1816214400, 4: 43243200, 6: -1081080, 8: 27300, 10: -691}


def betaN(i):
    return BETAN.get(i, 0)


def gpoch(U, T2, k):
    x, y = 1, 0
    for j in range(k):
        x, y = x * ((2 * j + 1) * U) - y * T2, x * T2 + y * ((2 * j + 1) * U)
    return x, y


def corr_data(K, u, tn, N):
    U, T2, M_ = u, 2 * tn, 2 * K - 1
    W = 2 * u * N
    q = U * U + T2 * T2
    base = LBETA * W ** M_
    S1 = S2 = 0
    for j in range(M_):
        g = gpoch(U, T2, j + 1)
        S1 += betaN(j) * g[0] * W ** (M_ - 1 - j)
        S2 += betaN(j) * g[1] * W ** (M_ - 1 - j)
    return (-(4 * u * N) * U * base + q * base + 2 * q * S1,
            -(4 * u * N) * T2 * base + 2 * q * S2,
            2 * q * base)


def pnK(u, tn, k):
    p = 1
    for j in range(k):
        p *= (2 * j + 1) ** 2 * u ** 2 + 4 * tn ** 2
    return p


def rem_even(K, u, tn, N, Q, r):
    """EMZetaHighCheck.remEven: (ok, EN, ED)"""
    ok = 1 <= r and r * r <= N and pnK(u, tn, 2 * K) <= Q * Q
    return ok, 2 * abs(betaN(2 * K - 2)) * Q, LBETA * (2 * u) ** (2 * K) * N ** (2 * K - 1) * r * (4 * K - 1)


def rem_odd(K, u, tn, N, Q, r):
    """EMZetaHighCheck.remOdd: (ok, EN, ED)"""
    ok = 1 <= r and r * r <= N and pnK(u, tn, 2 * K + 1) <= Q * Q
    EN = 4 * (6000000000000 * 2 ** (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ** (2 * K + 1) * Q
    ED = (6000000000000 * 2 ** (2 * K - 1) * 6283184 ** (2 * K + 1) * (2 * u) ** (2 * K + 1) * N ** (2 * K)
          * r * (4 * K + 1))
    return ok, EN, ED


def q_for(K, u, tn, odd):
    p = pnK(u, tn, 2 * K + 1 if odd else 2 * K)
    Q = math.isqrt(p)
    return Q if Q * Q >= p else Q + 1


def rem_E(K, u, tn, N, odd):
    Q, r = q_for(K, u, tn, odd), math.isqrt(N)
    _, EN, ED = (rem_odd if odd else rem_even)(K, u, tn, N, Q, r)
    return Fraction(EN, ED)


def minimal_N(K, tn, eps, odd=True, u=1):
    lo, hi = 2, 10 ** 8
    e = Fraction(eps).limit_denominator(10 ** 12)
    while lo < hi:
        m = (lo + hi) // 2
        if rem_E(K, u, tn, m, odd) <= e:
            hi = m
        else:
            lo = m + 1
    return lo


def check_terms(c, K, N, s1, s2, D, EN, ED):
    """the integer quantities of EMZetaHighCheck.checkCore (exact mirror)"""
    u = 2 ** c.tq
    BreN, BimN, BD = corr_data(K, u, c.tn, N)
    two = 2 ** c.P
    a1 = s1.reP - s1.reN
    b1 = s1.imP - s1.imN
    za = (s2.reP - s2.reN) - a1
    zb = (s2.imP - s2.imN) - b1
    zra = s2.reR + s1.reR
    zrb = s2.imR + s1.imR
    aB, aC = abs(BreN), abs(BimN)
    CreN = a1 * BD + za * BreN - zb * BimN
    RreN = s1.reR * BD + zra * aB + zrb * aC
    CimN = b1 * BD + za * BimN + zb * BreN
    RimN = s1.imR * BD + zra * aC + zrb * aB
    return dict(BD=BD, ED=ED, EN=EN, two=two, CreN=CreN, RreN=RreN, CimN=CimN, RimN=RimN, u=u)


def checkK(c, K, N, s1, s2, D, reLo, reHi, imLo, imHi, Q, r, odd):
    u = 2 ** c.tq
    ok, EN, ED = (rem_odd if odd else rem_even)(K, u, c.tn, N, Q, r)
    x = check_terms(c, K, N, s1, s2, D, EN, ED)
    BD, two = x["BD"], x["two"]
    ok = ok and 1 <= K <= 6 and 2 <= N and 1 <= D and 0 < ED
    ok = ok and reLo * two * BD * ED <= D * ED * (x["CreN"] - x["RreN"]) - D * BD * EN * two
    ok = ok and D * ED * (x["CreN"] + x["RreN"]) + D * BD * EN * two <= reHi * two * BD * ED
    ok = ok and imLo * two * BD * ED <= D * ED * (x["CimN"] - x["RimN"]) - D * BD * EN * two
    ok = ok and D * ED * (x["CimN"] + x["RimN"]) + D * BD * EN * two <= imHi * two * BD * ED
    return ok


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
    tag, tn, K, N = args[0], int(args[1]), int(args[2]), int(args[3])
    tq = int(opts.get("tq", 0))
    chunk = int(opts.get("chunk", 500))
    cpf = int(opts.get("cpf", 40))
    digits = int(opts.get("digits", 8))
    odd = opts.get("odd", "1") == "1"
    outdir = opts.get("outdir", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean"))
    assert 1 <= K <= 6 and N >= 2
    c = M.make_cfg(64, tn, tq, lnbig=256, sqbig=256)
    t0 = time.time()
    s = M.init_state(c)
    states, lens, idx = [s], [], [1]
    total, done = N - 2, 0
    while done < total:
        L = min(chunk, total - done)
        s = M.run(c, s, L)
        states.append(s)
        lens.append(L)
        done += L
        idx.append(idx[-1] + L)
    sN = M.step(c, states[-1])
    pyt = time.time() - t0
    assert states[-1].n == N - 1 and sN.n == N
    base = "EMZetaHighK_%s" % tag
    ns = "ArbEcon.IKK_%s" % tag
    cfgmod = base + "_Cfg"
    nch = len(lens)
    cfgterm = "(ArbEcon.OrderK.cfg64 %d %d)" % (tn, tq)
    # ------------------------------------------------------------ states module
    L = []
    L.append("/-  %s.lean -- order-(2K+1) EM instance states (GENERATED by arbecon/gen_emhigh_k.py; do not edit)." % cfgmod)
    L.append("")
    L.append("    t = %d / 2^%d, EM cut N = %d; the %d chunk-boundary states of the unchanged ArbEconomics" % (tn, tq, N, len(states)))
    L.append("    evaluator at the shared configuration `EMZetaHighCfg64.cfg64 %d %d`.  conjecture1_proved = False." % (tn, tq))
    L.append("-/")
    L.append("import EMZetaHighCfg64")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    for i, st in enumerate(states):
        L.append("def s%d : ArbEcon.St := %s" % (i, M.st_lean(st)))
    L.append("def sN : ArbEcon.St := %s" % M.st_lean(sN))
    L.append("")
    L.append("end")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    with open(os.path.join(outdir, cfgmod + ".lean"), "w") as f:
        f.write("\n".join(L))
    # ------------------------------------------------------------ chunk parts
    parts = []
    for j, start in enumerate(range(0, nch, cpf)):
        stop = min(start + cpf, nch)
        pm = "%s_P%d" % (base, j)
        L = []
        L.append("/-  %s.lean -- kernel chunks %d..%d (GENERATED by arbecon/gen_emhigh_k.py; do not edit)." % (pm, start, stop - 1))
        L.append("    Each `chunk_i` is a kernel `decide +kernel` check that `ArbEcon.run` maps s_i to s_(i+1).")
        L.append("    conjecture1_proved = False.")
        L.append("-/")
        L.append("import %s" % cfgmod)
        L.append("")
        L.append("namespace %s" % ns)
        L.append("")
        for i in range(start, stop):
            L.append("theorem chunk_%d : ArbEcon.St.beq (ArbEcon.run %s %d s%d) s%d = true := by decide +kernel"
                     % (i, cfgterm, lens[i], i, i + 1))
        if stop == nch:
            L.append("theorem chunk_N : ArbEcon.St.beq (ArbEcon.run %s 1 s%d) sN = true := by decide +kernel" % (cfgterm, nch))
        L.append("")
        L.append("end %s" % ns)
        L.append("")
        with open(os.path.join(outdir, pm + ".lean"), "w") as f:
            f.write("\n".join(L))
        parts.append(pm)
    # ------------------------------------------------------------ the kernel check data
    s1 = states[-1]
    u = 2 ** tq
    Q = q_for(K, u, tn, odd)
    r = math.isqrt(N)
    D = 10 ** digits
    _, EN, ED = (rem_odd if odd else rem_even)(K, u, tn, N, Q, r)
    x = check_terms(c, K, N, s1, sN, D, EN, ED)
    BD, two = x["BD"], x["two"]
    cre = Fraction(x["CreN"], BD) / two
    rre = Fraction(x["RreN"], BD) / two + Fraction(EN, ED)
    cim = Fraction(x["CimN"], BD) / two
    rim = Fraction(x["RimN"], BD) / two + Fraction(EN, ED)
    reLo = math.floor((cre - rre) * D)
    reHi = math.ceil((cre + rre) * D)
    imLo = math.floor((cim - rim) * D)
    imHi = math.ceil((cim + rim) * D)
    assert checkK(c, K, N, s1, sN, D, reLo, reHi, imLo, imHi, Q, r, odd), "checkK mirror fails"
    E = Fraction(EN, ED)
    t = Fraction(tn, u)
    tlean = "(%d : ℝ)" % tn if tq == 0 else "((%d : ℝ) / %d)" % (tn, u)
    # ------------------------------------------------------------ assembly module
    L = []
    L.append("/-  %s.lean -- KERNEL-CHECKED order-%d Euler-Maclaurin enclosure of zeta(1/2 + i t), t = %s" % (base, 2 * K + 1, str(t)))
    L.append("    (GENERATED by arbecon/gen_emhigh_k.py; do not edit).  KERNEL-ONLY FORMAT: no norm_num.")
    L.append("")
    L.append("      * the Dirichlet sum over n = 1..%d: %d `decide +kernel` chunks of the unchanged ArbEconomics" % (N - 1, nch))
    L.append("        evaluator at `EMZetaHighCfg64.cfg64 %d %d`, composed by `ArbEcon.chunk_sound` + `valid64`;" % (tn, tq))
    L.append("      * `check`: ONE `decide +kernel` run of `EMZetaHighCheck.checkK` (the exact correction factor")
    L.append("        B_%d(t, N), the order-%d remainder (%s-saw certificate), and the four final inequalities,"
             % (K, 2 * K + 1, "odd" if odd else "even"))
    L.append("        all in Int);")
    L.append("      * `zeta_box` = `EMZetaHighCheck.checkK_sound` (general, proved once; the remainder is")
    L.append("        `EMZetaHigh.em_line_remainder_%sle`, the general-K Euler-Maclaurin theorem)." % ("odd_" if odd else ""))
    L.append("    Certified: Re in [%s, %s], Im in [%s, %s], remainder E = %.3g." % (
        float(Fraction(reLo, D)), float(Fraction(reHi, D)), float(Fraction(imLo, D)), float(Fraction(imHi, D)), float(E)))
    L.append("    conjecture1_proved = False.  One height, finite interval arithmetic; nothing about RH.")
    L.append("-/")
    L.append("import EMZetaHighCheck")
    for pm in parts:
        L.append("import %s" % pm)
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("theorem ht : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (tlean, tn, tq))
    L.append("")
    L.append("theorem valid : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht" % (cfgterm, tlean, tn, tq))
    L.append("")
    L.append("theorem inv_0 : ArbEcon.Inv %s %s 1 s0 := ArbEcon.inv_init _ _ valid.one_eq" % (cfgterm, tlean))
    for i in range(nch):
        L.append("theorem inv_%d : ArbEcon.Inv %s %s %d s%d :=\n  ArbEcon.chunk_sound _ _ 9 valid %d %d s%d s%d inv_%d chunk_%d"
                 % (i + 1, cfgterm, tlean, idx[i + 1], i + 1, lens[i], idx[i], i, i + 1, i, i))
    L.append("theorem inv_N : ArbEcon.Inv %s %s %d sN :=\n  ArbEcon.chunk_sound _ _ 9 valid 1 %d s%d sN inv_%d chunk_N"
             % (cfgterm, tlean, N, N - 1, nch, nch))
    L.append("")
    L.append("/-- The whole order-%d assembly as ONE kernel computation (Int arithmetic). -/" % (2 * K + 1))
    L.append("theorem check : ArbEcon.OrderK.checkK %s %d %d s%d sN %d (%d) (%d) (%d) (%d) %d %d %s = true := by"
             % (cfgterm, K, N, nch, D, reLo, reHi, imLo, imHi, Q, r, "true" if odd else "false"))
    L.append("  decide +kernel")
    L.append("")
    L.append("/-- **Re and Im of zeta(1/2 + i t), t = %s**, kernel-checked, no hypotheses (order-%d Euler-Maclaurin). -/" % (str(t), 2 * K + 1))
    L.append("theorem zeta_box :")
    L.append("    (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ) ≤ (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).re ∧" % (reLo, D, tlean))
    L.append("      (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).re ≤ ((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) ∧" % (tlean, reHi, D))
    L.append("    (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ) ≤ (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).im ∧" % (imLo, D, tlean))
    L.append("      (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).im ≤ ((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) :=" % (tlean, imHi, D))
    L.append("  ArbEcon.OrderK.checkK_sound _ _ ht %d %d s%d sN inv_%d inv_N %d (%d) (%d) (%d) (%d) %d %d %s check"
             % (K, N, nch, nch, D, reLo, reHi, imLo, imHi, Q, r, "true" if odd else "false"))
    L.append("")
    L.append("/-- Real-literal form of the real part (cast normalisation only). -/")
    L.append("theorem zeta_re : (%d / %d : ℝ) ≤ (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).re ∧" % (reLo, D, tlean))
    L.append("    (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).re ≤ (%d / %d : ℝ) := by" % (tlean, reHi, D))
    L.append("  have h := zeta_box.1")
    L.append("  push_cast at h")
    L.append("  exact h")
    L.append("")
    L.append("/-- Real-literal form of the imaginary part (cast normalisation only). -/")
    L.append("theorem zeta_im : (%d / %d : ℝ) ≤ (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).im ∧" % (imLo, D, tlean))
    L.append("    (riemannZeta ((1 / 2 : ℂ) + (%s : ℂ) * Complex.I)).im ≤ (%d / %d : ℝ) := by" % (tlean, imHi, D))
    L.append("  have h := zeta_box.2")
    L.append("  push_cast at h")
    L.append("  exact h")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    with open(os.path.join(outdir, base + ".lean"), "w") as f:
        f.write("\n".join(L))
    try:
        import mpmath
        mpmath.mp.dps = 30
        z = mpmath.zeta(mpmath.mpc(0.5, mpmath.mpf(tn) / u))
        inside = bool(Fraction(reLo, D) <= Fraction(str(z.real)) <= Fraction(reHi, D) and
                      Fraction(imLo, D) <= Fraction(str(z.imag)) <= Fraction(imHi, D))
        zre, zim = float(z.real), float(z.imag)
    except ImportError:
        inside, zre, zim = None, None, None
    summary = dict(tag=tag, format="kernel", odd=odd, tn=tn, tq=tq, t=float(t), K=K, order=2 * K + 1, N=N, chunk=chunk,
                   nchunks=nch, terms=N - 1, python_seconds=round(pyt, 2), cfg_module=cfgmod, parts=parts,
                   assembly=base, lo_re=reLo / D, hi_re=reHi / D, lo_im=imLo / D, hi_im=imHi / D, E=float(E),
                   Q=Q, r=r, D=D, mpmath_re=zre, mpmath_im=zim, mpmath_inside=inside,
                   eval_rad_re=float(Fraction(x["RreN"], BD) / two))
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
