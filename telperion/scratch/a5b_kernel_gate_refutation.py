"""
A5b: kernel-gate the Case-B structural-rule refutation via the AXLE negative_control primitive.

a5 found the structural rule R_maxgap is NOT Aobj-monotone: at a specific miss tree it moves
Aobj 901/96 -> 1189/128 (DOWN).  Here we (1) re-verify those Aobj values against the EXACT cavity
engine, and (2) kernel-gate the FALSE monotonicity claim `Aobj_before <= Aobj_after`
(i.e. 901/96 <= 1189/128) via assert_kernel_rejects — confirming the Lean kernel rejects any
'proof' of the refuted rule's monotonicity.  This is the negative-control guard on a real Case-B rule.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pathlib import Path
from a3_derisk import Aobj_node

# telperion import
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.negative_control import assert_kernel_rejects
from telperion.verify import verify_lean

ENV_DIR = Path(__file__).resolve().parents[2] / "proof" / "formalization"

def main():
    inst = json.load(open(os.path.join(os.path.dirname(__file__), "a5_negctl_instance.json")))
    before = eval(inst["before"]); after = eval(inst["after"])
    ab, aa = Aobj_node(before), Aobj_node(after)
    print(f"rule refuted        : {inst['rule']}")
    print(f"Aobj(before) [engine]: {ab}   (json {inst['aobj_before']})")
    print(f"Aobj(after)  [engine]: {aa}   (json {inst['aobj_after']})")
    print(f"monotone claim Aobj_before <= Aobj_after : {ab <= aa}  (FALSE => rule refuted)")
    assert str(ab) == inst["aobj_before"] and str(aa) == inst["aobj_after"], "engine mismatch"

    # kernel-gate: the false monotonicity, as the exact rationals the cavity engine produces.
    ab_p, ab_q = ab.numerator, ab.denominator
    aa_p, aa_q = aa.numerator, aa.denominator
    claim = (f"theorem maxgap_mono_refuted : ({ab_p}:ℝ)/{ab_q} ≤ ({aa_p}:ℝ)/{aa_q} := by norm_num\n")
    print(f"\nkernel-gating FALSE claim: {ab_p}/{ab_q} ≤ {aa_p}/{aa_q}")
    rejected = assert_kernel_rejects("import Mathlib\n\n" + claim, "maxgap_mono_refuted", env_dir=ENV_DIR)
    print(f"assert_kernel_rejects (True = kernel REJECTS the false monotonicity): {rejected}")

    # positive control: the TRUE direction verifies clean (kernel accepts real inequality).
    good = (f"theorem maxgap_drop_real : ({aa_p}:ℝ)/{aa_q} < ({ab_p}:ℝ)/{ab_q} := by norm_num\n")
    r = verify_lean("import Mathlib\n\n" + good, env_dir=ENV_DIR, decls=["maxgap_drop_real"])
    print(f"positive control (real drop Aobj_after < Aobj_before verifies): okay={r.okay} axclean={r.axioms_clean}")
    print(f"\nRESULT: negative-control guard {'FIRED (rule refuted, kernel-gated)' if rejected and r.okay else 'INCONCLUSIVE'}")

if __name__ == "__main__":
    main()
