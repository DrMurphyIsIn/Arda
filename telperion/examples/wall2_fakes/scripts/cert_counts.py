"""(b) Arb-certified OFF-LINE zero counts on [sigma0, sigmaR] x [1/20, T], strips of height 10,
compared strip-by-strip with WALL-1 track C's non-rigorous zero lists.  conjecture1_proved = False.

usage: cert_counts.py NAME T
The right edge sigmaR is one where right_halfplane_nonvanishing certifies f != 0 for Re s >= sigmaR,
so the count is ALL zeros with Re s > sigma0 and 1/20 < Im s < T."""
import csv, json, os, sys, time
from fractions import Fraction as F
from telperion.arb_fakes import rigorous_winding, right_halfplane_nonvanishing

name, T = sys.argv[1], int(sys.argv[2])
SR = {"EP5": F(8, 5), "EPQ2": F(5, 2), "DH": F(8, 5)}[name]
SIG0 = [F(3, 5), F(7, 10), F(4, 5)]
OUT = os.path.expanduser(f"~/rh-team/wall2/T/certs/{name}_offline_counts_T{T}.cert.json")
dom = right_halfplane_nonvanishing(name, SR)
assert dom["certified"], dom
zl = [(float(r["sigma"]), float(r["t"])) for r in csv.DictReader(open(os.path.expanduser(
    f"~/rh-team/wall1/C/out/{name}_zeros_all.csv")))]
cuts = list(range(10, T, 10))
hs = [F(1, 20)] + [F(c) for c in cuts] + [F(T)]
res = {"kind": "offline_zero_count", "trust_class": "arb", "object": name, "sigma_right": str(SR),
       "right_edge_certificate": dom, "t0": "1/20", "T": T, "method": "arb_fakes.rigorous_winding (segment enclosure)",
       "counts": {}, "conjecture1_proved": False}
for s0 in SIG0:
    strips, tot, mism = [], 0, []
    t_start = time.time()
    for a, b in zip(hs, hs[1:]):
        st = {}
        w = rigorous_winding(name, s0, SR, a, b, prec=96, stats=st)
        exp = sum(1 for (x, y) in zl if x > float(s0) and float(a) < y < float(b))
        strips.append({"im0": str(a), "im1": str(b), "winding": w, "trackC": exp, "segments": st["segments"],
                       "min_segment": st["min_segment"]})
        tot += w
        if w != exp:
            mism.append((str(a), str(b), w, exp))
            print(f"  MISMATCH {name} s0={s0} [{a},{b}] arb={w} trackC={exp}", flush=True)
    res["counts"][str(s0)] = {"total": tot, "trackC_total": sum(s["trackC"] for s in strips), "mismatches": mism,
                              "strips": strips, "seconds": round(time.time() - t_start)}
    print(f"{name} sigma0={s0}: Arb-certified {tot} zeros in ({s0},{SR})x(1/20,{T}); trackC {res['counts'][str(s0)]['trackC_total']}; "
          f"{round(time.time() - t_start)} s", flush=True)
    json.dump(res, open(OUT, "w"), indent=1, sort_keys=True)
