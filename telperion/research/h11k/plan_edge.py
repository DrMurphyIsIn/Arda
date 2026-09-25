import sys, time, pickle
sys.path.insert(0, '/Users/peterwmurphy/arda-h11k/telperion/examples/zeta_reflection')
import Arb4_emit_seg as ES
OFF = ES.OFF
from fractions import Fraction as Fr
T = Fr(sys.argv[1])
t0 = time.time()
e = OFF.edge_enclosure(OFF.plan_edge(T))
print("T", T, "N", e["N"], "pieces", len(e["pieces"]), "Lo", float(e["Lv"]), "Hi", float(e["Hv"]), "w", float(e["Hv"]-e["Lv"]), "s", round(time.time()-t0,1))
print([ (str(p["sig"]), str(p["r"])) for p in e["pieces"]])
pickle.dump(e, open("edge_%s.pkl" % sys.argv[1].replace("/","_"), "wb"))
