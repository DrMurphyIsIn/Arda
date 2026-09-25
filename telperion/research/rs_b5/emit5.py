# UNTRUSTED emitter for lane B5 (RS5_) band certificates.  Every value is re-verified in the kernel.
#
# Stage 1 (select):  numpy Riemann-Siegel Z (main + C0) on a dyadic grid of step 2^-tq over [T0, T1];
#                    one sample per sign-constancy run = the grid point of max |Z| in the run (the
#                    endpoints T0 and T1 are forced samples).  Cross-check the change count against
#                    mpmath nzeros(T1) - nzeros(T0).
# Stage 2 (certs):   RS4 certificate per sample (lane B4 emitter, placeholder z box) and margin E.
# Stage 3 (boxes):   the EXACT assembled box (RS4.zBox) of every sample is obtained by `#reduce` in Lean
#                    (the evaluator is Nat.rec-based and cannot be #eval-compiled); zlo/zhi := box.
# Stage 4 (lean):    write the band file.
import sys, json, math, subprocess, os
import numpy as np
import mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'b4'))
import emit as b4

SCR = os.path.dirname(os.path.abspath(__file__))
ISL = '/Users/peterwmurphy/arda-rs-b5/telperion/examples/zeta_reflection/lean'
LOCK = '/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/leanlock.sh'
P = 64; o = 1 << P


def Z_np(t):
    t = np.asarray(t, dtype=np.float64)
    a = np.sqrt(t / (2 * np.pi))
    N = np.floor(a).astype(int)
    p = a - N
    th = t / 2 * np.log(t / (2 * np.pi)) - t / 2 - np.pi / 8 + 1 / (48 * t)
    Nmax = N.max()
    n = np.arange(1, Nmax + 1)
    mask = n[None, :] <= N[:, None]
    terms = np.cos(th[:, None] - t[:, None] * np.log(n)[None, :]) / np.sqrt(n)[None, :]
    S = 2 * np.sum(np.where(mask, terms, 0.0), axis=1)
    psi = np.cos(2 * np.pi * (p * p - p - 1 / 16)) / np.cos(2 * np.pi * p)
    return S + (-1.0) ** (N + 1) * a ** -0.5 * psi


def select(T0, T1, tq):
    q = 1 << tq
    ks = np.arange(T0 * q, T1 * q + 1)
    Z = np.concatenate([Z_np(ks[i:i + 4096] / q) for i in range(0, len(ks), 4096)])
    sg = Z > 0
    runs = []  # (start, end) index ranges of constant sign
    s = 0
    for i in range(1, len(ks)):
        if sg[i] != sg[i - 1]:
            runs.append((s, i - 1)); s = i
    runs.append((s, len(ks) - 1))
    samp = []
    for ri, (a, b) in enumerate(runs):
        j = a + int(np.argmax(np.abs(Z[a:b + 1])))
        samp.append(j)
    # force endpoints
    if samp[0] != 0:
        samp[0] = 0
    if samp[-1] != len(ks) - 1:
        samp[-1] = len(ks) - 1
    return [int(ks[j]) for j in samp], [float(Z[j]) for j in samp], len(runs) - 1


def margin_E(tn, tq):
    t = mp.mpf(tn) / (1 << tq)
    E = int(mp.ceil(o * t ** mp.mpf(-0.75))) + 1
    while not (o ** 4 * (1 << tq) ** 3 <= E ** 4 * tn ** 3):
        E += 1
    return E


def lean_cert(c):
    return '⟨' + ', '.join(str(x) for x in c) + '⟩'


def reduce_boxes(certs, tag):
    """certs: list of (tn, tq, cert list).  Returns list of (lo, hi) from Lean #reduce."""
    fn = os.path.join(SCR, f'reduce_{tag}.lean')
    with open(fn, 'w') as f:
        f.write('import RS5_Eval\nopen RS4\nset_option maxRecDepth 100000\nset_option format.width 100000\n')
        for (tn, tq, c) in certs:
            f.write(f'#reduce (proofs := true) (fun b : DIntvProd.DIntv => (b.lo, b.hi)) '
                    f'(zBox (ArbEcon.OrderK.cfg64 {tn} {tq}) ({lean_cert(c)} : Cert))\n')
    r = subprocess.run(['sh', LOCK, 'lake', 'env', 'lean', fn], cwd=ISL, capture_output=True, text=True)
    out = r.stdout + r.stderr
    res = []
    for line in out.splitlines():
        line = line.strip()
        if line.startswith('(Int.'):
            parts = line.strip('()').split(', ')
            vals = []
            for pp in parts:
                pp = pp.strip()
                if pp.startswith('Int.ofNat '):
                    vals.append(int(pp[len('Int.ofNat '):]))
                elif pp.startswith('Int.negSucc '):
                    vals.append(-int(pp[len('Int.negSucc '):]) - 1)
                else:
                    raise ValueError(pp)
            res.append(tuple(vals))
    if len(res) != len(certs):
        print(out[-3000:], file=sys.stderr)
        raise RuntimeError(f'got {len(res)} boxes for {len(certs)} certs')
    return res


def main():
    T0, T1, tq, tag = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    mp.mp.dps = 30
    tns, zs, K_grid = select(T0, T1, tq)
    Nd = int(mp.nzeros(T1)) - int(mp.nzeros(T0))
    print(f'band [{T0},{T1}] grid 2^-{tq}: samples {len(tns)}, grid changes {K_grid}, '
          f'mpmath N(T1)-N(T0) = {Nd}', file=sys.stderr)
    certs = []
    for tn in tns:
        c, info = b4.cert(tn, tq)
        certs.append((tn, tq, c))
    boxes = []
    B = 1500
    for bi in range(0, len(certs), B):
        boxes += reduce_boxes(certs[bi:bi + B], f'{tag}_{bi // B}')
    samples = []
    dropped = []
    for (tn, tq_, c), (lo, hi), zg in zip(certs, boxes, zs):
        c = list(c)
        c[17], c[18] = lo, hi
        E = margin_E(tn, tq_)
        pos = lo > 0
        ok = (13 * E * o < 5 * lo) if pos else (5 * hi < -(13 * E * o))
        t = tn / (1 << tq_)
        if not ok:
            dropped.append(dict(t=t, Z=zg, lo=lo / o / o, hi=hi / o / o, margin=13 / 5 * E / o))
            continue
        samples.append(dict(tn=tn, tq=tq_, E=E, cert=c, pos=pos, t=t, Z=zg,
                            hw=(hi - lo) / 2 / o / o, margin=13 / 5 * E / o))
    K = sum(1 for a, b in zip(samples, samples[1:]) if a['pos'] != b['pos'])
    first_ok = samples[0]['tn'] == T0 << tq
    last_ok = samples[-1]['tn'] == T1 << tq
    rep = dict(T0=T0, T1=T1, tq=tq, n_samples=len(samples), K=K, grid_changes=K_grid,
               mpmath_count=Nd, sharp=(K == Nd), dropped=dropped, endpoints_kept=(first_ok and last_ok),
               max_hw=max(s['hw'] for s in samples), min_absZ=min(abs(s['Z']) for s in samples))
    print(json.dumps({k: v for k, v in rep.items() if k != 'dropped'}), file=sys.stderr)
    if dropped:
        print('DROPPED', dropped, file=sys.stderr)
    json.dump(dict(report=rep, samples=samples), open(os.path.join(SCR, f'band_{tag}.json'), 'w'))


if __name__ == '__main__':
    main()
