"""Negative and positive controls for the box certifiers (README section 4.5).

A certifier that accepts everything proves nothing.  Each certifier is run on a region that contains
a genuine zero of H_t (a real zero, found here by a sign change of H_t on the real axis, enclosed in
Arb) and must FAIL there; and on a nearby zero-free region at the canopy height, where it must PASS.

  C1  direct evaluator,   t = 0.4, around the first real zero of H_{0.4} (x ~ 28)
  C2  A+B-C evaluator,    t = 0.4, around a real zero of H_{0.4} near x = 1000
  C3  Phi-integral boxes, t = 0,   around the first zero of H_0 (x = 2 gamma_1 ~ 28.27)
Writes results/controls.json.
"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import arb, acb, ctx  # noqa: E402

import canopy_mesh as cm  # noqa: E402
import p15_arb as pa  # noqa: E402
import smallx  # noqa: E402


def real_zero_bracket(F, a, b, n=400):
    """Find [u, v] in [a, b] with Re F(u) Re F(v) < 0 certified (F real on the real axis)."""
    xs = [a + (b - a) * k / n for k in range(n + 1)]
    vals = [F(x) for x in xs]
    for (u, fu), (v, fv) in zip(zip(xs, vals), zip(xs[1:], vals[1:])):
        if float(fu.upper()) < 0 < float(fv.lower()) or float(fv.upper()) < 0 < float(fu.lower()):
            return u, v
    return None


if __name__ == '__main__':
    ctx.prec = 100
    out = {}
    t = arb('0.4')
    # C1: direct evaluator near x ~ 28 (H_t real on the real axis)
    br = real_zero_bracket(lambda x: pa.Ht_direct(acb(x, 0), t).real, 26.0, 30.0, n=80)
    out['C1_zero_bracket'] = br
    u, v = br
    neg = cm.cover_strip(u - 0.05, v + 0.05, -0.05, 0.05, t, 'direct', w0=0.2, wmin=1e-3)
    pos = cm.cover_strip(u - 0.05, v + 0.05, 0.4, 0.4472136, t, 'direct', w0=0.2, wmin=1e-3)
    out['C1_direct'] = dict(region_with_zero=[u - 0.05, v + 0.05, -0.05, 0.05], must_fail=not neg['ok'],
                            zero_free_region=[u - 0.05, v + 0.05, 0.4, 0.4472136], must_pass=pos['ok'])
    # C2: A+B-C evaluator near x ~ 1000
    N = 8
    C = pa.Coeffs(t, 20)

    def Fabc(x):
        Q = pa.ft_all(acb(x, 0), t, N, C, want_deriv=False, want_err=False, want_C=False)
        B = pa.log_Mt(t, (1 - acb(0, 1) * acb(x, 0)) / 2)
        # H/B ~ f; H real on the axis, so use Re(f * B/|B|) = Re(f e^{i arg B}) as the real proxy
        return (Q['f'] * (acb(0, 1) * B.imag).exp()).real
    br2 = real_zero_bracket(Fabc, 1000.0, 1004.0, n=200)
    out['C2_zero_bracket'] = br2
    u2, v2 = br2
    neg2 = cm.cover_strip(u2 - 0.05, v2 + 0.05, 0.0, 0.02, t, 'abc', C, w0=0.05, wmin=1e-4)
    pos2 = cm.cover_strip(u2 - 0.05, v2 + 0.05, 0.4, 0.4472136, t, 'abc', C, w0=0.05, wmin=1e-4)
    out['C2_abc'] = dict(region_with_zero=[u2 - 0.05, v2 + 0.05, 0.0, 0.02], must_fail=not neg2['ok'],
                         zero_free_region=[u2 - 0.05, v2 + 0.05, 0.4, 0.4472136], must_pass=pos2['ok'])
    # C3: Phi-integral boxes at t = 0 around 2*gamma_1
    x1 = 2 * 14.134725141734693
    neg3 = smallx.cover_2d_phi(x1 - 0.1, x1 + 0.1, -0.05, 0.05, 0.0, w=0.05, h=0.05, wmin=1e-3)
    pos3 = smallx.cover_2d_phi(x1 - 0.1, x1 + 0.1, 0.3, 0.6, 0.0, w=0.05, h=0.05, wmin=1e-3)
    out['C3_phi'] = dict(region_with_zero=[x1 - 0.1, x1 + 0.1, -0.05, 0.05], must_fail=not neg3['ok'],
                         zero_free_region=[x1 - 0.1, x1 + 0.1, 0.3, 0.6], must_pass=pos3['ok'])
    out['all_controls_behave'] = all(out[k]['must_fail'] and out[k]['must_pass'] for k in ('C1_direct', 'C2_abc', 'C3_phi'))
    here = os.path.dirname(os.path.abspath(__file__))
    json.dump(out, open(os.path.join(here, 'results', 'controls.json'), 'w'), indent=1, default=float)
    print(json.dumps(out, indent=1, default=float))
