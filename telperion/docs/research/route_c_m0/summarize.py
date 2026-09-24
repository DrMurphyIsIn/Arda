"""Aggregate results/*.json into results/summary.json and print the M0 tables (markdown).

Also computes the design-B curve: for each certified envelope row (c0, N_s), the barrier sits at
X ~ x_{N_s} and hypothesis (i) (Prop 3.3 form) follows from a zero-free region
    beta <= 1 - c / log|gamma|   (|gamma| >= 55/16)
as soon as  (1 + sqrt(2 c0))/2 > 1 - c/log(X/2),  i.e.  c > c_needed(c0) := (1 - sqrt(2 c0)) log(X/2) / 2.
The kernel-proved constant is c >= 9/1369088 (DlvpZetaRateEffective.lean); the best published explicit
constant checked here is c = 1/5.558691 (Mossinghoff-Trudgian-Yang, arXiv:2212.06867, |t| >= 2).
"""
import glob
import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')


def load(p):
    with open(p) as f:
        return json.load(f)


def main():
    rows = {}
    for p in sorted(glob.glob(os.path.join(RES, 'row_*.json'))):
        rows[os.path.basename(p)] = load(p)
    env = load(os.path.join(RES, 'envelope.json')) if os.path.exists(os.path.join(RES, 'envelope.json')) else []
    uni = load(os.path.join(RES, 'uniform_small_x.json')) if os.path.exists(os.path.join(RES, 'uniform_small_x.json')) else {}
    extra = {}
    for name in ('controls', 'coverage_check'):
        q = os.path.join(RES, name + '.json')
        if os.path.exists(q):
            extra[name] = load(q)
    extra['coverage_full'] = {os.path.basename(q): load(q) for q in sorted(glob.glob(os.path.join(RES, 'coverage_full_*.json')))}
    out = dict(rows=rows, envelope=env, uniform_small_x=uni, **extra)
    # design-B curve
    c_kernel = 9 / 1369088
    c_mty = 1 / 5.558691
    curve = []
    for r in env:
        if not r.get('ok'):
            continue
        Ns = r['N_s']
        X = 4 * math.pi * Ns * Ns
        cneed = (1 - math.sqrt(2 * r['c0'])) * math.log(X / 2) / 2
        curve.append(dict(c0=r['c0'], y0=r['y0'], t0=r['t0'], N_s=Ns, X_approx=X, c_needed=cneed,
                          ok_kernel_dvp=cneed < c_kernel, ok_MTY=cneed < c_mty))
    out['designB_curve'] = curve
    with open(os.path.join(RES, 'summary.json'), 'w') as f:
        json.dump(out, f, indent=1, default=float)
    # ---- print tables
    print('| row | design | c0 | t0 | y0 | X | (i) | N_s | N1 | strip boxes | strip evals | Dirichlet terms | CPU s | all certified |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for k, r in rows.items():
        st = r.get('strip', {})
        an = r.get('analytic', {})
        X = r.get('X')
        print(f"| {k} | {r['design']} | {r['c0']:.7g} | {r['t0']} | {r['y0']} | {X:.6g} | "
              f"{r.get('cond_i', {}).get('kind', '')[:30]} | {an.get('N_s')} | {an.get('N1')} | "
              f"{st.get('boxes', '-')} | {st.get('evals', '-')} | {st.get('terms', '-')} | "
              f"{st.get('cpu_sec', r.get('barrier', {}).get('cpu_sec', 0)):.0f} | {r.get('all_certified_here')} |")
    print()
    print('| c0 | y0 | t0 | N_s | x_s = 4 pi N_s^2 | N1 (crude) | min bottom-edge margin | max crude rho | ok |')
    print('|---|---|---|---|---|---|---|---|---|')
    for r in sorted(env, key=lambda r: (r['c0'], r['y0'])):
        print(f"| {r['c0']} | {r['y0']} | {r['t0']:.6f} | {r['N_s']} | {r.get('x_s', float('nan')):.3e} | {r.get('N1')} | "
              f"{r.get('min_bottom_margin', float('nan')):.2e} | {r.get('max_crude_rho', float('nan')):.3f} | {r['ok']} |")
    print()
    print('| c0 | N_s | X ~ x_{N_s} | dVP constant c needed | kernel c = 6.57e-6 enough? | MTY c = 0.1799 enough? |')
    print('|---|---|---|---|---|---|')
    for r in curve:
        print(f"| {r['c0']} | {r['N_s']} | {r['X_approx']:.3e} | {r['c_needed']:.3e} | {r['ok_kernel_dvp']} | {r['ok_MTY']} |")


if __name__ == '__main__':
    main()
