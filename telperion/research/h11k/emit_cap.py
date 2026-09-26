"""UNTRUSTED emitter (lane H11K): the capstone H11K_h11000.lean (values mirrored exactly in Python)."""
import sys, pickle
sys.path.insert(0, '/Users/peterwmurphy/arda-h11k/telperion/examples/zeta_reflection')
import Arb4_emit_seg as ES
import Arb4_emit as A
from fractions import Fraction as Fr
ISL = '/Users/peterwmurphy/arda-h11k/telperion/examples/zeta_reflection/lean'
d = pickle.load(open('encl.pkl', 'rb'))
L1, H1, L2, H2, L3, H3, L4, H4, L5, H5 = d['E']
G1 = d['G1']
n = 3541
t0, t1 = Fr(31851, 4), Fr(11004)
cim = (t0 + t1) / 2
q = (cim - t0) ** 2 + 4
d0, d1 = Fr(30989, 500000), Fr(3, 1000)
assert cim == Fr(75867, 8) and q == Fr(147987481, 64)
# mirror validBS / CapGeom.of_sqrt / hs1
assert 0 < t0 <= t1 and q > 0 and t0 <= cim <= t1 and Fr(9, 4) + (cim - t0) ** 2 < q and Fr(9, 4) + (t1 - cim) ** 2 < q
pl = 2 * L1 + L2 - H3 + L4 + L5; ph = 2 * H1 + H2 - L3 + H4 + H5
assert 2 * Fr(3141593, 10 ** 6) * (n - 1) < pl and ph < 2 * Fr(3141592, 10 ** 6) * (n + 1)
assert q <= cim ** 2 and q <= (cim - t0 + d0) ** 2 and q <= (t1 + d1 - cim) ** 2 and Fr(1, 4) + cim ** 2 >= q
ql = A.ql
src = open('cap_template.lean').read()
for k, v in dict(L4=ql(L4), H4=ql(H4), L5=ql(L5), H5=ql(H5)).items():
    src = src.replace('@' + k + '@', v)
src = src.replace('@G1@', ES.gam_def('G_T11004', G1))
open(ISL + '/H11K_h11000.lean', 'w').write(src)
print('pin slack lo %.4f hi %.4f' % (float(pl - 2 * Fr(3141593, 10 ** 6) * (n - 1)), float(2 * Fr(3141592, 10 ** 6) * (n + 1) - ph)))
print(ES.gam_def('G_T11004', G1), ql(L4), ql(H4), ql(L5), ql(H5))
