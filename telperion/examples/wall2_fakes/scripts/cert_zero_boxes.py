"""(a) Arb-certified winding boxes around the named off-line zeros of EP5, EPQ2, DH.  conjecture1_proved = False."""
import json, time, os
from fractions import Fraction as F
from telperion.arb_fakes import certify_zero_box
from telperion import arb_dh

ZEROS = [("EP5", "0.932969697485", "15.668249531278"), ("EP5", "0.93766690670", "29.98339523516"),
         ("EPQ2", "0.86238551488", "41.76697325913"), ("EPQ2", "0.83666006753", "56.18314506997"),
         ("DH", "0.808517", "85.699348")]
H = F(1, 100)
out = []
for name, x, y in ZEROS:
    cx, cy = F(round(F(x) * 1000), 1000), F(round(F(y) * 1000), 1000)
    t0 = time.time()
    c = certify_zero_box(name, cx - H, cx + H, cy - H, cy + H, expected=1, prec=96)
    c["named_zero"] = f"{x}+{y}i"
    c["seconds"] = round(time.time() - t0, 1)
    print(name, x, y, "-> winding", c["winding"], c["box"], c["segments"], "segs", c["seconds"], "s", flush=True)
    out.append(c)
# DH: is the old node-sampling certify_offline_zero also accepting this box? (record, not trusted)
try:
    d = arb_dh.certify_offline_zero(F(4, 5), F(41, 50), F(857, 10) - H, F(857, 10) + H)
    print("arb_dh.certify_offline_zero (node sampling, NOT rigorous) on the DH box:", d["winding"])
except Exception as e:
    print("arb_dh.certify_offline_zero:", e)
json.dump(out, open(os.path.expanduser("~/rh-team/wall2/T/certs/offline_zero_boxes.cert.json"), "w"), indent=2, sort_keys=True)
