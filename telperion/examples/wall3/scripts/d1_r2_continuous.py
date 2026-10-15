"""Track T: wall5/D1/T_REQUEST.md R2 -- A, zeta_Pi(0), zeta_Pi'(rho0) (and a zero box) for the continuous planted
system at (beta0, u0) = (0.85, 103) and (0.70, 11), gamma0 = 14.134725.  Reuses the rigorous Ein/E1 machinery of
n8_continuous.py (same file, constants swapped).  ARB.  conjecture1_proved = False."""
import json
SRC = open("/Users/peterwmurphy/rh-team/wall3/T/scripts/n8_continuous.py").read().split("res = {")[0]
out = {"trust_class": "arb", "conjecture1_proved": False, "cases": []}
for b0, u0, fl in (("0.85", 103, {"A": 0.122010758984, "z0": -8.14032808e-14, "dz": [8.0879161, 0.2576544]}),
                   ("0.70", 11, {"A": 0.238588309151, "z0": -1.65919263e-3, "dz": [4.0490081, 0.2054351]})):
    src = SRC.replace('arb("0.85"), arb("14.134725")', f'arb("{b0}"), arb("14.134725")').replace("arb(103).log()", f"arb({u0}).log()")
    g = {}
    exec(src, g)
    acb, ctx, cert = g["acb"], g["ctx"], g["certify_zero_box"]
    RHO, RHOB, V0, EG, _ein, val = g["RHO"], g["RHOB"], g["V0"], g["EG"], g["_ein"], g["val"]
    ctx.prec = 192
    Eb1, _ = _ein((1 - RHO) * V0); Eb2, _ = _ein((1 - RHOB) * V0)
    A = EG * V0 * (1 - RHO) * (1 - RHOB) * (-Eb1 - Eb2).exp()
    Ea0, _ = _ein((RHO - 1) * V0); Ebb0, _ = _ein((RHO - RHOB) * V0)
    dz = EG * V0 * (RHO - RHOB) / (RHO - 1) * (Ea0 - Ebb0).exp()
    z0 = val("0", "0", prec=192)
    box = cert(g["zetaP"], float(b0) - 0.01, float(b0) + 0.01, 14.124725, 14.144725, expected=1, prec=128)
    row = {"beta0": b0, "u0": u0, "A": A.str(15), "zeta_Pi(0)": z0.str(12), "zeta_Pi'(rho0)": dz.str(15),
           "zero_box_winding": box["winding"], "D1_floats": fl}
    out["cases"].append(row)
    print(b0, u0, "A", A.str(12), "z(0)", z0.str(10), "z'(rho0)", dz.str(12), "box", box["winding"], flush=True)
json.dump(out, open("/Users/peterwmurphy/rh-team/wall3/T/certs/D1_R2_continuous.cert.json", "w"), indent=1)
