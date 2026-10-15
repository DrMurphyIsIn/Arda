"""EP5 knife edge: certify the zero near 0.79977772+61.14026i lies strictly LEFT of sigma = 0.8.
conjecture1_proved = False.  ARB (bb-reviewed)."""
import json, os
from telperion.arb_fakes import certify_zero_box
c = certify_zero_box("EP5", "7995/10000", "79995/100000", "611390/10000", "611415/10000", expected=1, prec=128)
c["named_zero"] = "0.79977772+61.14026i"
c["gap_to_sigma_0.8"] = "1/20000"
c["status"] = "ARB (bb-reviewed: ~/e9-research/review_wall2_T/REVIEW_wall2_T_2026-10-14.md; review covers through d75bf8a86)"
print(c)
json.dump(c, open(os.path.expanduser("~/rh-team/wall2/T/certs/EP5_knife_edge.cert.json"), "w"), indent=1, sort_keys=True)
