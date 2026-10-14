"""Compact summary of the Li enclosures (the full files are 50-110 MB).  conjecture1_proved = False."""
import json, os
from fractions import Fraction


def outward(iv, digits=40):
    """Round an exact [lo, hi] OUTWARD to a decimal grid (still a rigorous enclosure)."""
    lo, hi = Fraction(iv[0]), Fraction(iv[1])
    w = max(abs(lo), abs(hi), Fraction(1))
    k = digits - len(str(int(w)))
    q = 10 ** max(k, 0)
    return [str(Fraction((lo * q).__floor__(), q)), str(Fraction(-((-hi * q).__floor__()), q))]
C = os.path.expanduser("~/rh-team/wall2/T/certs/")
srcs = {"zeta": "li_fakes_N3000_zeta_EP5_EPQ2_DH.cert.json", "EPQ2": "li_fakes_N3000_zeta_EP5_EPQ2_DH.cert.json",
        "DH": "li_fakes_N3000_zeta_EP5_EPQ2_DH.cert.json", "EP5": "li_fakes_N9000_EP5.cert.json"}
out = {"convention": "lambda_n, n >= 1 (= taylorCoeff xi (n-1)); zeta lambda_1 = 0.0230957...", "trust_class": "arb",
       "generator": "telperion.arb_fakes.enclose_li_fake", "conjecture1_proved": False, "objects": {}}
cache = {}
for name, f in srcs.items():
    if f not in cache:
        cache[f] = json.load(open(C + f))
    d = cache[f]["objects"][name]
    neg = d["certified_negative_lambda"]
    runs = []
    for k in neg:
        if runs and runs[-1][1] == k - 1:
            runs[-1][1] = k
        else:
            runs.append([k, k])
    lam = [outward(iv) for iv in d["lambda"]]
    pick = sorted(set([1, 2, 3, 10, 100, 1000] + ([runs[0][0] - 1, runs[0][0]] if runs else []) + [len(lam)]))
    out["objects"][name] = {"N": cache[f]["N"], "prec_bits": cache[f]["prec_bits"], "seconds": d["seconds"],
                            "first_certified_negative": runs[0][0] if runs else None, "negative_runs": runs,
                            "n_negative": len(neg), "undecided": d["undecided_lambda"], "max_width": d["max_width"],
                            "lambda_1_to_200": lam[:200],
                            "selected": {str(n): lam[n - 1] for n in pick}}
json.dump(out, open(C + "li_fakes_summary.cert.json", "w"), indent=1)
for k, v in out["objects"].items():
    print(k, v["N"], v["first_certified_negative"], len(v["negative_runs"]), v["undecided"][:3])
