"""(3) Polygon negative controls: feed the calibration fakes (EP5, EPQ2, DH) into the RH-type emitters'
certification layer (Layer 1, no Lean build) and record whether each REFUSES, ACCEPTS a statement that is
TRUE of the fake (non-discriminating, not unsound), or ACCEPTS a FALSE statement (soundness finding).
conjecture1_proved = False.
"""
import json, os
from fractions import Fraction as F
from flint import acb, acb_series, arb, ctx

from telperion.arb_fakes import (rigorous_winding, fake_eval, enclose_li_fake, fake_series, _frac_interval,
                                 _eval_point)
from telperion.emit_box_localization import box_localization_certificate, empty_band_certificate
from telperion.emit_li_positivity import li_rung_certificate
from telperion.emit_winding_box_zero import winding_box_zero_certificate
from telperion import emit_grid_modulus_nonvanishing as G
from telperion.emit_bagchi_recurrence import bagchi_grid_max

OUT = os.path.expanduser("~/rh-team/wall2/T/certs/negative_controls.json")
rows = []


def rec(emitter, obj, claim, truth_for_fake, outcome, detail):
    verdict = {"REFUSED": "OK (refused)",
               "ACCEPTED": "OK (true of the fake: non-discriminating)" if truth_for_fake else "SOUNDNESS FINDING"}[outcome]
    rows.append(dict(emitter=emitter, object=obj, claim=claim, claim_true_for_fake=truth_for_fake,
                     outcome=outcome, verdict=verdict, detail=str(detail)[:400]))
    print(f"[{verdict}] {emitter} / {obj}: {claim} -> {outcome}: {str(detail)[:160]}", flush=True)


def attempt(emitter, obj, claim, truth, fn):
    try:
        r = fn()
        rec(emitter, obj, claim, truth, "ACCEPTED", r)
    except (ValueError, RuntimeError) as e:
        rec(emitter, obj, claim, truth, "REFUSED", e)


# ---------------------------------------------------------------- Arb sign changes on the critical line
def lam_line(name, t, prec=96):
    """The real completed function on Re s = 1/2 (Lambda for EP5/EPQ2, xi for DH): returns an arb."""
    ctx.prec, ctx.cap = prec, 1
    s = acb_series([acb(arb("1/2"), arb(f"{F(t)}"))])
    one = acb_series([1])
    if name in ("EP5", "EPQ2"):
        v = s.gamma() * (s * (acb(20).sqrt() / (2 * acb.pi())).log()).exp() * fake_series(name, s)
    else:
        v = (-((one + s) / 2) * (acb.pi() / 5).log()).exp() * ((one + s) / 2).gamma() * fake_series("DH", s)
    v = v.coeffs()[0]
    assert abs(float(v.imag.mid())) <= 1e-6 * max(1e-30, abs(float(v.real.mid()))) + float(v.imag.rad()) + 1e-25
    return v.real


def online_lower_bound(name, t0, t1, step=F(1, 200)):
    """Rigorous LOWER bound on the number of zeros on Re = 1/2 with t0 < t < t1: sign changes of the real
    completed function at rational sample points whose Arb balls exclude 0 (IVT)."""
    n, last = 0, None
    t = F(t0) + step
    while t < t1:
        v = lam_line(name, t)
        sgn = 1 if v > 0 else (-1 if v < 0 else 0)
        if sgn != 0:
            if last is not None and sgn != last:
                n += 1
            last = sgn
        t += step
    return n


# ---------------------------------------------------------------- 1. box_localization ("all zeros in B on the line")
BOXES = {"EP5": ("1/20", "19/20", "15", "33/2"), "EPQ2": ("1/10", "9/10", "41", "42"), "DH": ("1/10", "9/10", "85", "86")}
loc_detail = {}
for name, (r0, r1, i0, i1) in BOXES.items():
    n_total = rigorous_winding(name, r0, r1, i0, i1, prec=96)
    n_line = online_lower_bound(name, F(i0), F(i1))
    loc_detail[name] = dict(box=(r0, r1, i0, i1), n_total_arb=n_total, n_line_lower_bound_arb=n_line)
    attempt("box_localization", name, f"every zero of {name} in [{r0},{r1}]x[{i0},{i1}] is on Re=1/2 "
            f"(n_line={n_line}, n_total={n_total})", False,
            lambda: box_localization_certificate(n_line, n_total, r0, r1, i0, i1))
    # the empty-band (zero-free) path with the honest count
    attempt("box_localization.empty_band", name, f"{name} zero-free on the box (n_total={n_total})", False,
            lambda: empty_band_certificate(r0, r1, i0, i1, n_total=n_total))

# ---------------------------------------------------------------- 2. winding_box_zero with a rigorous fake backend
from telperion.emit_winding_box_zero import register_winding_fn
for name in ("EP5", "EPQ2", "DH"):
    register_winding_fn(f"arb_fakes_{name}", lambda r0, r1, i0, i1, p, n, _nm=name:
                        rigorous_winding(_nm, r0, r1, i0, i1, prec=p, init_per_side=max(2, n // 3)))
ZB = {"EP5": ("923/1000", "943/1000", "7829/500", "7839/500"), "EPQ2": ("213/250", "109/125", "41757/1000", "41777/1000"),
      "DH": ("799/1000", "819/1000", "85689/1000", "85709/1000")}
for name, (r0, r1, i0, i1) in ZB.items():
    for claim_w, truth in ((0, False), (1, True), (2, False)):
        attempt("winding_box_zero[arb_fakes backend]", name, f"winding {claim_w} on the off-line zero box", truth,
                lambda: winding_box_zero_certificate(re0=r0, re1=r1, im0=i0, im1=i1, expected_winding=claim_w,
                                                     prec=96, n_per_side=24,
                                                     winding_fn=lambda *a, _nm=name: rigorous_winding(
                                                         _nm, *a[:4], prec=a[4])).to_json_dict())

# ---------------------------------------------------------------- 3. grid_modulus_nonvanishing (mpmath-numeric kind)
# f = f_base' convention: order k of the backend returns |f^{(k-1)}| for f = the fake.
def _fake_backend(name):
    def be(order, re, im, prec):
        ctx.prec, ctx.cap = max(64, 4 * int(prec)), order
        s = acb_series([acb(arb(f"{F(re)}"), arb(f"{F(im)}")), 1])
        c = fake_series(name, s).coeffs()
        k = order - 1
        import math
        return float(abs(c[k]).mid()) * math.factorial(k)
    return be


for name, (r0, r1, i0, i1) in ZB.items():
    G.register_backend(f"fake_{name}", _fake_backend(name))
    # adversarial: try many grids and take the most favourable claimed M, L (the sweep values themselves)
    accepted = None
    be = _fake_backend(name)
    R0, R1, I0, I1 = map(F, (r0, r1, i0, i1))
    for nrows in (1, 2, 3, 5, 8, 13):
        hh = (I1 - I0) / (2 * nrows)
        rows_ = [I0 + hh * (2 * k + 1) for k in range(nrows)]
        gre = (R0 + R1) / 2
        hw = (R1 - R0) / 2
        d = F(int(((hw * hw + hh * hh) ** 0.5) * 10**9) + 1, 10**9)
        M = F(G._sup_second_with_lipschitz(be, R0, R1, I0, I1, 40, 2, 2) * 1.0000001).limit_denominator(10**9) + F(1, 10**9)
        L = F(min(be(1, gre, t, 40) for t in rows_) * 0.9999999).limit_denominator(10**9)
        try:
            c = G.grid_modulus_nonvanishing_certificate(
                re0=r0, re1=r1, im0=i0, im1=i1, grid_re=gre, grid_im=rows_, half_width=hw, half_height=hh,
                delta=d, bound_M=M, bound_L=L, backend=f"fake_{name}", prec=40, sweep_nre=2, sweep_nim=2)
            accepted = (nrows, c.to_json_dict())
            break
        except ValueError as e:
            last = e
    if accepted:
        rec("grid_modulus_nonvanishing[fake backend]", name, "zero-free on the off-line zero box", False, "ACCEPTED", accepted)
    else:
        rec("grid_modulus_nonvanishing[fake backend]", name, "zero-free on the off-line zero box (6 adversarial grids)",
            False, "REFUSED", last)

# ---------------------------------------------------------------- 4. li_positivity: provenance of lo
li = {n: enclose_li_fake(n, 40, 512) for n in ("EP5", "EPQ2", "DH")}
for name in li:
    lo = li[name][9][0]
    attempt("li_positivity.li_rung_certificate", name,
            f"rung n=9 with lo = {name}'s lambda_10 lower bound {float(lo):.4f} (emitted as a riemannXi rung)", True,
            lambda: li_rung_certificate(9, lo))
from telperion.li_coeff import enclose_li_coeffs
attempt("li_coeff.enclose_li_coeffs", "zeta", "anchored zeta enclosures", True, lambda: enclose_li_coeffs(3)[0])

# ---------------------------------------------------------------- 5. bagchi_recurrence: same finite observation for EP5
SIG = [F(3, 5), F(13, 20), F(7, 10)]
TS = [F(10), F(11), F(12)]


def fake_dev(name, tau):
    M = F(0)
    for s in SIG:
        for t in TS:
            ctx.prec = 160
            a = _eval_point(name, s, t + tau, 160) - _eval_point(name, s, t, 160)
            M = max(M, _frac_interval(a.abs_upper())[1])
    return M


Mz = min(bagchi_grid_max(tau, SIG, TS, 120)[0] for tau in range(1, 61))
Me = min(fake_dev("EP5", tau) / 2 for tau in range(1, 61))
rec("bagchi_recurrence (finite grid)", "EP5/2 vs zeta",
    f"best grid deviation over tau in [1,60]: zeta {float(Mz):.4f}, EP5/2 {float(Me):.4f}", True, "ACCEPTED",
    "a finite recurrence observation is certifiable for the fake too; the instrument does not discriminate")

# ---------------------------------------------------------------- 6. dVP 3-4-1 positivity input (zero_free_region template)
def p341(name, a1, s, t):
    ctx.prec = 128
    vs = [_eval_point(name, F(s), F(x), 128) / a1 for x in (0, t, 2 * t)]
    return _frac_interval((abs(vs[0]) ** 3 * abs(vs[1]) ** 4 * abs(vs[2])))


hi = p341("DH", 1, F(51, 50), F(8571, 100))[1]
rec("zero_free_region (3-4-1 input)", "DH", f"|D(s)^3 D(s+it)^4 D(s+2it)| >= 1 at s=51/50, t=85.71: Arb upper {float(hi):.5f}",
    False, "REFUSED" if hi < 1 else "ACCEPTED", "the positivity hypothesis of the dVP template is Arb-certified FALSE for DH")

hi = p341("EP5", 2, F(5, 4), F(17015, 100))[1]
rec("zero_free_region (3-4-1 input)", "EP5", f"|F(s)^3 F(s+it)^4 F(s+2it)| >= 1, F = EP5/2, at s=5/4, t=170.15: Arb upper {float(hi):.10f}",
    False, "REFUSED" if hi < 1 else "ACCEPTED", "the positivity hypothesis of the dVP template is Arb-certified FALSE for EP5 (barely)")

json.dump({"rows": rows, "localization_detail": loc_detail, "conjecture1_proved": False}, open(OUT, "w"), indent=1)
