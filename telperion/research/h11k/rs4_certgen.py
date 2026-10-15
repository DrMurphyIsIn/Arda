# UNTRUSTED generator of lane-B4 RS4 certificates (P = 64, `ArbEcon.OrderK.cfg64`) for the RS5 band emitters.
#
# Every field it produces is RE-VERIFIED by the Lean kernel (`RS4.check` / `RS5.check5` via `decide +kernel`):
# nothing here is trusted, and a wrong field makes the kernel reject the sample, never accept a false one.
#
# Replaces the lost lane-B4 emitter `emit.py` (it lived in a session scratchpad, ef083c48-.../scratchpad/b4, and is in
# no git branch), whose only function the band emitters used was `cert(tn, tq) -> (cert, info)`.  Rebuilt by the RSC0
# agent (2026-10-15) from the check list of RS4_Eval.lean (`RS4.Checks`):
#
#   A0 A1, N, Y0 Y1, LG0 LG1, Q0 Q1, U0 U1, V0 V1  : exact integer floor/ceil brackets, computed here;
#   TH0 TH1                                          : from the Dirichlet log bracket (llo, lhi) of `RS4.dstate`;
#   F0 F1                                            : from the cos balls `ArbEcon.trig` of U and V;
#   zlo zhi                                          : placeholders 0 (the caller sets the exact `RS4.zBox` box).
#
# (llo, lhi) and the two trig balls are evaluated by the Lean evaluator itself (`#reduce`, batched in ONE Lean run per
# call), so no Nat kernel (lnf64, hc64, hs64) is re-implemented in Python.  The enclosure half-width of the resulting box
# is certificate-independent to < 1e-10 (it is 2(|Re S| + |Im S|)/t, set by the theta ball |phi - thetaMain| <= 1/t; RSC0
# PLAN §14), so this generator's boxes are as tight as any valid certificate's.
#
# conjecture1_proved = False.  A certificate factory for finite interval arithmetic; nothing about RH.
import math
import os
import subprocess
import tempfile

import mpmath as mp

ISL = str(__import__('pathlib').Path(__file__).resolve().parents[2] / 'examples/zeta_reflection/lean')
LOCK = os.environ.get('ARDA_LEANLOCK', os.path.expanduser('~/hodge-engine/leanlock.sh'))

# cfg64 (EMZetaHighCfg64.lean :38-46): P, one, hp (|pi/2 * 2^P - hp| <= rp), rp
P = 64
o = 1 << P
hp, rp = 28976077832308491369, 2

FIELDS = ['N', 'A0', 'A1', 'Y0', 'Y1', 'LG0', 'LG1', 'TH0', 'TH1', 'Q0', 'Q1', 'U0', 'U1', 'V0', 'V1', 'F0', 'F1',
          'zlo', 'zhi']


def _csqrt(n):
    r = math.isqrt(n)
    return r if r * r >= n else r + 1


def _cdiv(a, b):
    return -((-a) // b)


def _lpPos(Y):
    return 840 * Y * o ** 8 + 280 * Y ** 3 * o ** 6 + 168 * Y ** 5 * o ** 4 + 120 * Y ** 7 * o ** 2


def _lpNeg(Y):
    return 420 * Y ** 2 * o ** 7 + 210 * Y ** 4 * o ** 5 + 140 * Y ** 6 * o ** 3 + 105 * Y ** 8 * o


def stage1(tn, tq):
    """The brackets that need no Lean evaluation (RS4.Checks hA0..hV1, hLG0/hLG1, hQ0/hQ1)."""
    Q = 1 << tq
    A0 = math.isqrt((tn * o ** 3) // (Q * 4 * (hp + rp)))
    A1 = _csqrt(_cdiv(tn * o ** 3, Q * 4 * (hp - rp)))
    N = A0 // o
    if not (N >= 1 and N * o < A0 and A1 < (N + 1) * o):
        raise ValueError(f'a = sqrt(t/2pi) too close to an integer at tn={tn}, tq={tq}')
    Y0 = (A0 - N * o) // N
    Y1 = _cdiv(A1 - N * o, N)
    LG0 = (_lpPos(Y0) - _lpNeg(Y0) - 1680 * Y0 ** 9) // (840 * o ** 8)
    LG1 = _cdiv(_lpPos(Y1) + 1680 * Y1 ** 9 - _lpNeg(Y1), 840 * o ** 8)
    Q0 = math.isqrt(o ** 3 // A1)
    Q1 = _csqrt(_cdiv(o ** 3, A0))
    d0, d1 = A0 - N * o, A1 - N * o
    U0 = 4 * (hp - rp) * d0 // o
    U1 = _cdiv(4 * (hp + rp) * d1, o)
    V0 = (hp - rp) * (16 * d0 * o + o * o - 16 * d1 * d1) // (4 * o * o)
    V1 = max(0, _cdiv((hp + rp) * (16 * d1 * o + o * o) - (hp + rp) * 16 * d0 * d0, 4 * o * o))
    return dict(N=N, A0=A0, A1=A1, Y0=Y0, Y1=Y1, LG0=LG0, LG1=LG1, TH0=0, TH1=0, Q0=Q0, Q1=Q1, U0=U0, U1=U1,
                V0=V0, V1=V1, F0=0, F1=0, zlo=0, zhi=0)


def cert_str(c):
    return '(⟨' + ', '.join(str(c[k]) for k in FIELDS) + '⟩ : RS4.Cert)'


def lean_reduce(lines, workdir=None, tag='rs4cg', lock=None, isl=None):
    """Run `#reduce` lines under the lean lock in the island; the .lean file goes to `workdir` (default: a fresh temp
    directory, never the repository)."""
    workdir = workdir or tempfile.mkdtemp(prefix='rs4_certgen_')
    fn = os.path.join(workdir, f'reduce_{tag}.lean')
    with open(fn, 'w') as f:
        f.write('import RS5_Eval\nopen RS4 ArbEcon\nset_option maxRecDepth 100000\nset_option format.width 100000\n')
        f.write('\n'.join(lines) + '\n')
    r = subprocess.run(['sh', lock or LOCK, 'lake', 'env', 'lean', fn], cwd=isl or ISL, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip().splitlines()
    if r.returncode != 0:
        raise RuntimeError('\n'.join(out[-30:]))
    return out


def certs(pts, workdir=None, tag='rs4cg', lock=None, isl=None):
    """Certificates for a list of (tn, tq), batched in ONE Lean run.  Returns a list of 19-field lists in RS4.Cert order
    with the box fields zlo = zhi = 0 (placeholders for the caller's exact `RS4.zBox`)."""
    C = [stage1(tn, tq) for tn, tq in pts]
    lines = []
    for (tn, tq), c in zip(pts, C):
        cfg = f'(ArbEcon.OrderK.cfg64 {tn} {tq})'
        lines += [f'#reduce (fun s : St => (s.llo, s.lhi)) (dstate {cfg} {cert_str(c)})',
                  f'#reduce (fun x : Trig => (x.cm, x.cs, x.cr)) (trig {cfg} {c["U0"]} {c["U1"]})',
                  f'#reduce (fun x : Trig => (x.cm, x.cs, x.cr)) (trig {cfg} {c["V0"]} {c["V1"]})']
    out = lean_reduce(lines, workdir, tag, lock, isl)
    tup = [ln.strip().strip('()').split(', ') for ln in out if ln.strip().startswith('(')]
    if len(tup) != 3 * len(pts):
        raise RuntimeError(f'got {len(tup)} reductions for {3 * len(pts)} requests:\n' + '\n'.join(out[-20:]))
    res = []
    for i, ((tn, tq), c) in enumerate(zip(pts, C)):
        Q = 1 << tq
        llo, lhi = int(tup[3 * i][0]), int(tup[3 * i][1])
        U, V = tup[3 * i + 1], tup[3 * i + 2]
        Ucm, Ucs, Ucr = int(U[0]), U[1] == 'true', int(U[2])
        Vcm, Vcs, Vcr = int(V[0]), V[1] == 'true', int(V[2])
        c['TH0'] = (4 * tn * tn * (llo + c['LG0']) - 2 * tn * tn * o - tn * Q * (hp + rp) - 4 * o * Q * Q) // (4 * tn * Q)
        c['TH1'] = _cdiv(4 * tn * tn * (lhi + c['LG1']) + 4 * o * Q * Q - 2 * tn * tn * o - tn * Q * (hp - rp),
                         4 * tn * Q)
        Nm = Vcm if Vcs else -Vcm
        D = Ucm if Ucs else -Ucm
        rN, rD = Vcr, Ucr
        if rD < D:
            c['F0'] = min((Nm - rN) * o // (D - rD), (Nm - rN) * o // (D + rD))
            c['F1'] = max(_cdiv((Nm + rN) * o, D - rD), _cdiv((Nm + rN) * o, D + rD))
        elif D + rD < 0:
            c['F0'] = min((Nm + rN) * o // (D - rD), (Nm + rN) * o // (D + rD))
            c['F1'] = max(_cdiv((Nm - rN) * o, D - rD), _cdiv((Nm - rN) * o, D + rD))
        else:
            raise ValueError(f'cos(2 pi p) ball contains 0 at tn={tn}, tq={tq}')
        res.append([c[k] for k in FIELDS])
    return res


def cert(tn, tq):
    """Drop-in for the lost lane-B4 `emit.cert(tn, tq) -> (cert, info)` (one Lean run per call; prefer `certs`)."""
    c = certs([(tn, tq)])[0]
    return c, dict(generator='rs4_certgen', P=P)


def E_min(tn, tq):
    """The least margin numerator E with RS5.MarginOK: one^4 (2^tq)^3 <= E^4 tn^3, i.e. E >= 2^P t^(-3/4)."""
    t = mp.mpf(tn) / (1 << tq)
    with mp.workdps(40):
        E = max(1, int(mp.floor(o * t ** mp.mpf(-0.75))) - 2)
    while not (o ** 4 * (1 << tq) ** 3 <= E ** 4 * tn ** 3):
        E += 1
    return E
