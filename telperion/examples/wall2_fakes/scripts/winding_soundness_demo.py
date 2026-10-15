"""Soundness finding: arb_dh.winding_number (node sampling) undercounts two zeros near an edge.
conjecture1_proved = False.

f(z) = (z - a)(z - b), with a and b both INSIDE the unit box and close to the bottom edge, between two
sampling nodes.  The true winding is 2.  We evaluate f in Arb balls and route it through the unmodified
arb_dh.winding_number by patching its module-level dh_eval, so the evaluations are exact balls; only the
node-sampling argument is under test.  Then we run winding_box_zero_certificate, which re-runs at doubled
precision and density, with expected_winding = 1.
"""
from fractions import Fraction as F
from flint import acb, acb_series, arb, ctx
import telperion.arb_dh as A
from telperion.emit_winding_box_zero import winding_box_zero_certificate
from telperion.arb_fakes import rigorous_winding

a = (F(51, 100), F(1, 10**4))       # x = 0.51 lies between nodes 12/24, 13/24 (and 24/48, 25/48)
b = (F(51, 100) + F(1, 10**5), F(2, 10**4))


def f_series(s):
    za = acb(arb(f"{a[0]}"), arb(f"{a[1]}"))
    zb = acb(arb(f"{b[0]}"), arb(f"{b[1]}"))
    return (s - za) * (s - zb)


def patched_eval(x, y, prec=128):
    ctx.prec = prec
    v = f_series(acb_series([acb(arb(f"{F(x)}"), arb(f"{F(y)}"))])).coeffs()[0]
    from telperion.arb_fakes import _frac_interval
    rl, rh = _frac_interval(v.real)
    il, ih = _frac_interval(v.imag)
    return rl, rh, il, ih


A.dh_eval = patched_eval
w_node = A.winding_number(0, 1, 0, 1, prec=128, n_per_side=24)
print("arb_dh.winding_number (node sampling), n_per_side=24:", w_node)
cert = winding_box_zero_certificate(re0=0, re1=1, im0=0, im1=1, expected_winding=1, prec=128, n_per_side=24,
                                    winding_fn=lambda r0, r1, i0, i1, p, n: A.winding_number(r0, r1, i0, i1, p, n))
print("winding_box_zero_certificate ACCEPTED expected_winding=1:", cert.to_json_dict())
print("TRUE number of zeros in the box: 2 (a, b both inside)")
print("arb_fakes.rigorous_winding:", rigorous_winding(f_series, 0, 1, 0, 1, prec=128))
