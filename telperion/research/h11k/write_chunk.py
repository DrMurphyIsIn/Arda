# UNTRUSTED writer (lane H11K): band_<tag>.json -> ONE chunk file RS5_Band_<Name>_C0.lean via lane B5's chunk_file.
import sys, json, os
sys.path.insert(0, '/Users/peterwmurphy/arda-h11k/telperion/research/rs_b5')
import write_band as W
W.ISL = '/Users/peterwmurphy/arda-h11k/telperion/examples/zeta_reflection/lean'
SCR = os.path.dirname(os.path.abspath(__file__))
tag, name = sys.argv[1], sys.argv[2]
d = json.load(open(os.path.join(SCR, f'band_{tag}.json')))
rep, S = d['report'], d['samples']
assert S[0]['tn'] == rep['tn0'] and S[-1]['tn'] == rep['tn1'] and not rep['dropped'] if 'dropped' in rep else True
mod, K, lo, hi = W.chunk_file(name, 0, S, rep)
p = os.path.join(W.ISL, mod + '.lean')
t = open(p).read()
t = t.replace(f'-- lane B5: chunk 0 of the band certificate {name}', f'-- lane H11K (RS5 format): the band certificate {name}')
t = t.replace('pipeline scratchpad/b5/emit5.py', 'pipeline scratchpad/h11k/emit5h.py (lane B5 emit5.py over a dyadic range)')
open(p, 'w').write(t)
print(mod, len(S), K, lo['tn'], hi['tn'], rep)
