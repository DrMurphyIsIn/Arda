"""Extract (T0, T1, N) for every RHInBoxT band imported by AllZeros_h1000..h280000 and the distinct
edge heights; writes bands_h280000.json (input of extrapolate.py / edge_study.py).
usage: python3 extract_bands.py <zeta_zero_localization/lean dir> [out.json]
conjecture1_proved = False."""
import json, os, re, sys
from fractions import Fraction
src = sys.argv[1]
out = sys.argv[2] if len(sys.argv) > 2 else "bands_h280000.json"
bands = set()
for k in range(1, 281):
    f = os.path.join(src, "AllZeros_h%d.lean" % (1000 * k))
    for m in re.finditer(r"^import (RHInBoxT_\S+)", open(f).read(), re.M):
        bands.add(m.group(1))
def fr(s):
    s = s.strip().strip("()")
    if "/" in s:
        a, c = s.split("/"); return Fraction(int(a.strip()), int(c.strip()))
    return Fraction(int(s))
rows = []
for b in sorted(bands):
    head = open(os.path.join(src, b + ".lean")).read(600)
    m = re.search(r"x \[([0-9/() ]+),([0-9/() ]+)\]` with `N = (\d+)`", head)
    rows.append((float(fr(m.group(1))), float(fr(m.group(2))), int(m.group(3))))
rows.sort()
edges = sorted({r[0] for r in rows} | {r[1] for r in rows})
json.dump(dict(bands=rows, edges=edges), open(out, "w"))
print(len(rows), "bands,", sum(r[2] for r in rows), "zeros (with stretched-box overlaps),", len(edges), "edges")
