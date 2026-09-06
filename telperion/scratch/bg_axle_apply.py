"""
Apply the merged AXLE/Ono Telperion capabilities to the BG conjecture1 effort.
Executes, against the REAL built Lean project (proof/formalization) and real BG-shaped specs:

  #1 negative_control  — kernel-gated disprove of a FALSE BG log-combination (trust primitive).
  #2 emit_transcendental_enclosure — emit + verify a real BG compact-core cell enclosure atom.
  #3 gap_fill + verify — recognize a real BG log-enclosure goal, pick a route; extract sorry-gaps.
  #4 repair + cert_meta + bundle — metadata/index/dedup/name-conflict guard on BG atoms.

Run:  PYTHONPATH=src PATH=$HOME/.elan/bin:$PATH python3 scratch/bg_axle_apply.py
"""
import os, sys
from pathlib import Path

HERE = Path(__file__).resolve()
ENV_DIR = HERE.parents[2] / "proof" / "formalization"   # the built R3Cert lake project

from telperion.verify import verify_lean
from telperion.negative_control import log_combination_negative_control
from telperion import emit_transcendental_enclosure as TE
from telperion import gap_fill
from telperion import cert_meta, bundle, repair

def hdr(s): print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)

# ---------------------------------------------------------------- #1
def n1_negative_control():
    hdr("#1  negative_control — kernel-gated disprove of a FALSE BG log-combination")
    # FALSE BG-shaped claim: 1·log(3/2) − FSTAR ≤ 0.  (LHS = 0.405 − 0.207 = +0.198 > 0.)
    # monotone fold ⇒ emitted norm_num fact (3/2)^11 ≤ 621/64, i.e. 86.5 ≤ 9.7 — FALSE.
    res = log_combination_negative_control(
        terms=[(1, "3/2"), (-1, "621/64")], q="0", route="monotone", env_dir=ENV_DIR)
    print(f"  false instance: 1·log(3/2) − FSTAR ≤ 0")
    print(f"  Layer-1 self-check refused (untrusted): {res.selfcheck_refused}")
    print(f"  Layer-2 KERNEL rejects forged proof   : {res.kernel_rejects}")
    print(f"  okay (kernel-gated as FALSE)          : {res.okay}")
    # positive control: a TRUE instance must VERIFY clean (no false positive on truth).
    # 1·log(5/4) − FSTAR ≤ 1/5  (0.223−0.207=0.016 ≤ 0.2) — true, tangent route.
    try:
        from telperion.emit_log_combination import log_combination_certificate, LogCombinationEmitter
        cert = log_combination_certificate(terms=[(1,"5/4"),(-1,"621/64")], q="1/5", route="tangent")
        lean = LogCombinationEmitter()._emit_tangent(cert, "true_ctrl")
        content = ("import Mathlib\n\nnoncomputable def FSTAR : ℝ := Real.log (621/64) / 11\n\n" + lean)
        rc = verify_lean(content, env_dir=ENV_DIR, decls=["true_ctrl"])
        print(f"  control (TRUE claim VERIFIES clean)   : okay={rc.okay} axclean={rc.axioms_clean}")
    except Exception as e:
        print(f"  control skipped: {type(e).__name__}: {str(e)[:80]}")
    return res.okay

# ---------------------------------------------------------------- #2
def n2_emit_enclosure():
    hdr("#2  emit_transcendental_enclosure — real BG compact-core cell enclosure, verified green")
    # BG cell box: e_v = log(1 + x) − F*, x = S/d ∈ [1/6, 1/3] (a tail-cell message box).
    cert = TE.transcendental_enclosure_certificate(face="log", x0="1/6", x1="1/3", L="3/20", U="1/3")
    print(f"  cert self-checked: L={cert.L} ≤ log(1+x) ≤ U={cert.U} on [{cert.x0},{cert.x1}]")
    lean = TE.TranscendentalEnclosureEmitter()._emit_log(cert, "bg_cell_enc_16_13")
    r = verify_lean("import Mathlib\n\n" + lean, env_dir=ENV_DIR,
                    decls=["bg_cell_enc_16_13_enclosure"])
    print(f"  verify_lean: okay={r.okay}  axioms_clean={r.axioms_clean}  sorries={r.sorries}  ({r.elapsed_s:.1f}s)")
    if r.errors: print("  errors:", r.errors[:3])
    print(f"  axioms: {r.axioms}")
    return r.okay and r.axioms_clean

# ---------------------------------------------------------------- #3
def n3_gapfill():
    hdr("#3  gap_fill + verify — recognize a real BG log-enclosure goal, pick route; extract gaps")
    for stmt in ["Real.log (5/4) - FSTAR ≤ 1/5",
                 "Real.log (4/3) - FSTAR ≤ 1/3",
                 "Real.log (3/2) - FSTAR ≤ 0"]:
        spec = gap_fill.match_log_enclosure(stmt)
        if spec is None:
            print(f"  '{stmt}'  ->  not a single-log FSTAR enclosure")
            continue
        try:
            route = gap_fill.pick_route(spec)
            print(f"  '{stmt}'  ->  terms={spec.terms} q={spec.q}  ROUTE={route}")
        except ValueError as e:
            print(f"  '{stmt}'  ->  no route ({str(e)[:50]})")
    # extract_gaps on a synthetic BG file with a sorry-lemma (the assembly driver).
    synth = ("theorem bg_open_cell (x : ℝ) (hx : 0 ≤ x) : "
             "Real.log (1 + x) - FSTAR ≤ 1/3 := by sorry\n")
    gaps = gap_fill.extract_gaps(synth)
    print(f"  extract_gaps: {[(g.name, g.statement[:40]+'...') for g in gaps]}")
    return len(gaps) == 1

# ---------------------------------------------------------------- #4
def n4_repair_meta_bundle():
    hdr("#4  repair + cert_meta + bundle — metadata / index / dedup / name-conflict guard on BG atoms")
    atomA = ("theorem bg_a (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by\n"
             "  have hy : (0:ℝ) < 1 + x := by linarith\n"
             "  have h := Real.log_le_sub_one_of_pos hy\n  linarith\n")
    atomB = ("theorem bg_b : (2:ℝ) * 3 = 6 := by norm_num\n")
    # cert_meta: structured metadata (type hash, tactic counts)
    m = cert_meta.extract_cert_meta(atomA)
    print(f"  cert_meta bg_a: name={m.name} type_hash={m.type_hash[:12]} tactics={m.tactic_counts}")
    idx = cert_meta.CertIndex()
    idx.add(cert_meta.extract_cert_meta(atomA)); idx.add(cert_meta.extract_cert_meta(atomB))
    print(f"  CertIndex size={len(idx.metas)}  duplicates={idx.duplicates()}  (content-addressed)")
    # bundle: merge + dedup + name-conflict rejection
    stats = bundle.bundle_stats(bundle.merge_bundle([atomA, atomB, atomA]))  # atomA duplicated
    print(f"  merge_bundle([A,B,A]) stats: {stats}  (dedup of shared atom)")
    conflict_caught = False
    try:
        bundle.merge_bundle([atomA, "theorem bg_a : (1:ℝ) = 1 := rfl\n"])  # same name, diff stmt
    except ValueError as e:
        conflict_caught = True
        print(f"  name-conflict guard fired: {str(e)[:70]}")
    # repair: run the drift-repair pass (idempotent on clean input)
    repaired, applied = repair.repair_lean(atomA)
    print(f"  repair_lean ran: passes_applied={applied}  unchanged_on_clean={repaired.strip()==atomA.strip()}")
    return conflict_caught

if __name__ == "__main__":
    results = {}
    for fn in (n1_negative_control, n2_emit_enclosure, n3_gapfill, n4_repair_meta_bundle):
        try:
            results[fn.__name__] = fn()
        except Exception as e:
            import traceback; traceback.print_exc()
            results[fn.__name__] = f"ERROR: {type(e).__name__}: {e}"
    hdr("SUMMARY")
    for k, v in results.items():
        print(f"  {k}: {v}")
