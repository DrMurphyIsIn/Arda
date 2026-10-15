"""Track T: Arb zero box for EP5's zero at ~1.011049+1193.946405i (claimed by track P / wall1 C). conjecture1_proved=False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, time
from telperion.arb_fakes import certify_zero_box, fake_eval
t=time.time()
c = certify_zero_box("EP5", "1.006", "1.016", "1193.941", "1193.951", expected=1, prec=96)
c["note"] = "box strictly inside Re s > 1 (re0 = 1.006); arb_fakes, Arda main 2dfc6eeee (guarded); script on branch wall3/telperion-certs"
c["seconds"] = round(time.time()-t, 1)
v = fake_eval("EP5", "1.011049334044", "1193.946404528846", prec=128)
c["value_at_C_float_point"] = [float(x) for x in v]
json.dump(c, open(cert_path("P_EP5_zero_sigma_gt_1.cert.json"), "w"), indent=1)
print(json.dumps(c, indent=1))
