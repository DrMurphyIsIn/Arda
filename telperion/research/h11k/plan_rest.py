import sys, time, pickle
sys.path.insert(0, '/Users/peterwmurphy/arda-h11k/telperion/examples/zeta_reflection')
import Arb4_emit_seg as ES
from fractions import Fraction as Fr
T0 = Fr(31851, 4); T1 = Fr(11004); n = 3541
d1 = Fr(3, 1000)
t = time.time()
sd = ES.plan_slab_rowed("U11004", T1, T1 + d1)
print("slab rows", len(ES.slab_rows(sd)), "cells", ES.slab_ncells(sd), "N", sd["N"], "F", float(sd["F"]), round(time.time()-t,1), "s")
pickle.dump(sd, open("slab_U11004.pkl", "wb"))
e = pickle.load(open("edge_11004.pkl", "rb"))
G0, G1 = ES.gam_cert(T0), ES.gam_cert(T1)
print("G0", G0); print("G1", G1)
L4, H4, L5, H5 = ES.k6_encl(G0, G1)
L2, H2 = e["Lv"], e["Hv"]
L3, H3 = Fr(-17713, 200000), Fr(-31959, 500000)
L1, H1 = Fr(-249, 250), Fr(249, 250)
pl = 2*L1 + L2 - H3 + L4 + L5
ph = 2*H1 + H2 - L3 + H4 + H5
import math
print("L4..H5", float(L4), float(H4), float(L5), float(H5))
print("pl/2pi", float(pl)/2/math.pi, "ph/2pi", float(ph)/2/math.pi, "n", n)
lo = 2*Fr(3141593, 10**6)*(n-1); hi = 2*Fr(3141592,10**6)*(n+1)
print("sharp pin slack lo", float(pl-lo), "hi", float(hi-ph))
lo2 = 2*Fr(31416, 10000)*(n-1); hi2 = 2*Fr(314,100)*(n+1)
print("old pin slack lo", float(pl-lo2), "hi", float(hi2-ph))
pickle.dump(dict(G0=G0,G1=G1,E=(L1,H1,L2,H2,L3,H3,L4,H4,L5,H5)), open("encl.pkl","wb"))
