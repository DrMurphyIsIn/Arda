"""(2) Li coefficients of the fakes, Arb.  usage: li_ramp.py N PREC.  conjecture1_proved = False."""
import json, os, sys, time
from telperion.arb_fakes import enclose_li_fake
N, P = int(sys.argv[1]), int(sys.argv[2])
OBJS = sys.argv[3].split(",") if len(sys.argv) > 3 else ["zeta", "EP5", "EPQ2", "DH"]
out = {"N": N, "prec_bits": P, "convention": "index n = taylorCoeff xi n = Li lambda_{n+1}", "trust_class": "arb",
       "conjecture1_proved": False, "objects": {}}
for name in OBJS:
    t0 = time.time()
    b = enclose_li_fake(name, N, P)
    neg = [n + 1 for n, (lo, hi) in enumerate(b) if hi < 0]
    undecided = [n + 1 for n, (lo, hi) in enumerate(b) if lo <= 0 <= hi]
    minpos = min(range(N), key=lambda n: b[n][0])
    out["objects"][name] = {"seconds": round(time.time() - t0, 1), "certified_negative_lambda": neg,
                            "undecided_lambda": undecided, "all_positive": not neg and not undecided,
                            "max_width": float(max(hi - lo for lo, hi in b)),
                            "lambda": [[str(lo), str(hi)] for lo, hi in b],
                            "lambda_float": [float((lo + hi) / 2) for lo, hi in b]}
    print(name, N, P, out["objects"][name]["seconds"], "s; negative:", neg[:10], "undecided:", undecided[:10],
          "max width", out["objects"][name]["max_width"], flush=True)
json.dump(out, open(os.path.expanduser(f"~/rh-team/wall2/T/certs/li_fakes_N{N}_{"_".join(OBJS)}.cert.json"), "w"))
