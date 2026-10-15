# UNTRUSTED writer (lane H11K): band_<tag>.json -> ONE chunk file RS5_Band_<Name>_C0.lean via lane B5's chunk_file.
import sys, json, os
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[3] / 'telperion/research/rs_b5'))
import write_band as W
W.ISL = str(__import__('pathlib').Path(__file__).resolve().parents[3] / 'telperion/examples/zeta_reflection/lean')
SCR = os.path.dirname(os.path.abspath(__file__))
# usage: write_chunk.py <tag> <Name> [--json-dir DIR] [--out DIR]   (--out: write the chunk there instead of the island)
args = sys.argv[1:]
JSON_DIR = SCR
if '--json-dir' in args:
    i = args.index('--json-dir'); JSON_DIR = args[i + 1]; del args[i:i + 2]
if '--out' in args:
    i = args.index('--out'); W.ISL = os.path.abspath(args[i + 1]); del args[i:i + 2]
    os.makedirs(W.ISL, exist_ok=True)
tag, name = args[0], args[1]
d = json.load(open(os.path.join(JSON_DIR, f'band_{tag}.json')))
rep, S = d['report'], d['samples']
assert S[0]['tn'] == rep['tn0'] and S[-1]['tn'] == rep['tn1'] and not rep['dropped'] if 'dropped' in rep else True
# provenance phrase: emit5h.py lives in git since RSC0 Phase 3c (its certificates come from rs4_certgen.py)
PROV = ('pipeline telperion/research/h11k/emit5h.py (lane B5 emit5.py over a dyadic range; certificates rs4_certgen.py)'
        if rep.get('cert_generator') == 'rs4_certgen'
        else 'pipeline scratchpad/h11k/emit5h.py (lane B5 emit5.py over a dyadic range)')
mod, K, lo, hi = W.chunk_file(name, 0, S, rep, sharp=rep.get('sharp_margin', False), provenance=PROV)
p = os.path.join(W.ISL, mod + '.lean')
t = open(p).read()
t = t.replace(f'-- lane B5: chunk 0 of the band certificate {name}', f'-- lane H11K (RS5 format): the band certificate {name}')
open(p, 'w').write(t)
print(mod, len(S), K, lo['tn'], hi['tn'], rep)
