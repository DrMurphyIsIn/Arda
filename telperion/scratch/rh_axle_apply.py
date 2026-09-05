"""
Apply the merged AXLE/Ono Telperion capabilities to the Riemann-Hypothesis effort
(the zero-free-region rate-upgrade thread: zeta_log_bound + ZeroFreePolylog).

Mirrors scratch/bg_axle_apply.py, but pointed at the RH `zero_free_bridge` Lean
example and RH-shaped specs.  FOUR capabilities exercised:

  #1 negative_control  — kernel-gated disprove of a FALSE RH log-tangent bound
                         (the trust primitive; generic `assert_kernel_rejects`).
  #2 emit_transcendental_enclosure — emit the log-face atom whose `_upper` theorem
                         `log(1+x) ≤ x` IS the tangent bound underlying the RH
                         harmonic bound (harmonic_le_one_add_log → norm_partial_sum_le
                         → zeta_log_bound).
  #3 gap_fill          — extract_gaps on an RH sorry-skeleton (the REAL RH workflow:
                         a parallel session filled zeta_partial_sum_repr/zeta_trunc/
                         zeta_log_bound from exactly such a skeleton).
  #4 cert_meta+bundle  — metadata / content-addressed index / dedup / name-conflict
                         guard on the growing RH atom family.

TWO-TIER by design (per AXLE third tour):
  * PYTHON/SYMPY tier (always runs) — exact-arithmetic self-checks, Layer-1 negative
    control, gap extraction, cert metadata.  Zero Lean.  Proves the math.
  * KERNEL tier (gated behind RH_AXLE_RUN_LEAN=1) — verify_lean / assert_kernel_rejects.
    OFF by default: the RH `zero_free_bridge` example has NO .lake build, so a local
    verify_lean would trigger a full Mathlib compile == the SoC-watchdog hazard.
    Run the kernel tier in CI (the rh-research-artifacts jobs), or set the flag only
    on a machine cleared for local Lean.

Run (Python tier only):   PYTHONPATH=src python3 scratch/rh_axle_apply.py
Run (full, CI/cleared):   RH_AXLE_RUN_LEAN=1 PYTHONPATH=src PATH=$HOME/.elan/bin:$PATH \
                          python3 scratch/rh_axle_apply.py
"""
import os
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve()
# the RH zero-free-bridge lake project (built in CI; unbuilt locally).
ENV_DIR = HERE.parents[1] / "examples" / "zero_free_bridge" / "lean"

RUN_LEAN = os.environ.get("RH_AXLE_RUN_LEAN") == "1"

from telperion import emit_transcendental_enclosure as TE
from telperion import gap_fill, cert_meta, bundle


def hdr(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)


# ---------------------------------------------------------------- #1
def n1_negative_control():
    hdr("#1  negative_control — kernel-gated disprove of a FALSE RH log-tangent bound")
    x = sp.Symbol("x", nonnegative=True)
    # FALSE RH-shaped claim: log(1+x) ≤ x − 1/10 for x ≥ 0.  FALSE at x=0
    # (log 1 = 0 ≤ −1/10 is false).  The tangent bound log(1+x) ≤ x is TIGHT at
    # x=0, so no downward shift survives.  The forged Lean proof reuses the true
    # atom's tactic (log_le_sub_one_of_pos + linarith) — linarith CANNOT close the
    # shifted goal, so the kernel rejects.
    false_stmt = "Real.log (1 + x) ≤ x - 1/10"
    true_stmt = "Real.log (1 + x) ≤ x"
    # ---- Layer 1 (untrusted, sympy, local): witness the falsity at x=0. --------
    val0 = sp.log(1 + sp.Integer(0)) - (sp.Integer(0) - sp.Rational(1, 10))  # log1 - (-1/10)
    layer1_refuses = bool(sp.N(val0, 30) > 0)  # LHS-RHS = 1/10 > 0 ⇒ claim false at x=0
    print(f"  false claim : {false_stmt}   (x ≥ 0)")
    print(f"  Layer-1 self-check refuses (witness x=0, LHS-RHS=+1/10>0): {layer1_refuses}")
    # ---- Layer 2 (trusted, kernel, gated): forge a proof, confirm kernel rejects.
    forged = (
        f"theorem rh_negctrl_forged (x : ℝ) (hx : 0 ≤ x) : {false_stmt} := by\n"
        f"  have hy : (0 : ℝ) < 1 + x := by linarith\n"
        f"  have h := Real.log_le_sub_one_of_pos hy\n"
        f"  linarith\n"
    )
    true_ctrl = (
        f"theorem rh_true_tangent (x : ℝ) (hx : 0 ≤ x) : {true_stmt} := by\n"
        f"  have hy : (0 : ℝ) < 1 + x := by linarith\n"
        f"  have h := Real.log_le_sub_one_of_pos hy\n"
        f"  linarith\n"
    )
    if RUN_LEAN:
        from telperion.negative_control import assert_kernel_rejects
        from telperion.verify import verify_lean
        rej = assert_kernel_rejects(
            "import Mathlib\n\n" + forged, "rh_negctrl_forged", env_dir=ENV_DIR)
        rc = verify_lean("import Mathlib\n\n" + true_ctrl, env_dir=ENV_DIR,
                         decls=["rh_true_tangent"])
        print(f"  Layer-2 KERNEL rejects forged proof   : {rej}")
        print(f"  control (TRUE tangent VERIFIES clean) : okay={rc.okay} axclean={rc.axioms_clean}")
        return layer1_refuses and rej and rc.okay
    print("  Layer-2 KERNEL tier GATED OFF (RH_AXLE_RUN_LEAN != 1; no local .lake).")
    print("  forged proof staged for CI:")
    for ln in forged.splitlines():
        print("    | " + ln)
    return layer1_refuses


# ---------------------------------------------------------------- #2
def n2_emit_enclosure():
    hdr("#2  emit_transcendental_enclosure — RH tangent atom log(1+x) ≤ x (harmonic-bound leg)")
    # The `_upper` theorem below is precisely the tangent bound the RH harmonic
    # bound rests on (norm_partial_sum_le : ‖Σ n^{-s}‖ ≤ 1 + log N, via
    # harmonic_le_one_add_log).  We instantiate on a concrete box to also ship the
    # rational floor; the RH-load-bearing sub-theorem is `_upper` (all x ≥ 0).
    cert = TE.transcendental_enclosure_certificate(face="log", x0="1/6", x1="1/3", L="3/20", U="1/3")
    print(f"  cert self-checked (exact sympy): L={cert.L} ≤ log(1+x) ≤ U={cert.U} on [{cert.x0},{cert.x1}]")
    lean = TE.TranscendentalEnclosureEmitter()._emit_log(cert, "rh_tangent_enc")
    upper = [ln for ln in lean.splitlines()
             if ln.startswith("theorem rh_tangent_enc_upper") or ln.strip().startswith("have")]
    print("  emitted `_upper` (the RH harmonic-bound tangent leg):")
    for ln in lean.splitlines():
        if "rh_tangent_enc_upper" in ln or ("_upper" in ln and "theorem" in ln):
            print("    | " + ln)
    if RUN_LEAN:
        from telperion.verify import verify_lean
        r = verify_lean("import Mathlib\n\n" + lean, env_dir=ENV_DIR,
                        decls=["rh_tangent_enc_upper", "rh_tangent_enc_enclosure"])
        print(f"  verify_lean: okay={r.okay} axioms_clean={r.axioms_clean} "
              f"sorries={r.sorries} ({r.elapsed_s:.1f}s)")
        if r.errors:
            print("  errors:", r.errors[:3])
        return r.okay and r.axioms_clean
    print("  KERNEL tier GATED OFF — Lean generated + math self-checked, verify staged for CI.")
    return True


# ---------------------------------------------------------------- #3
def n3_gapfill():
    hdr("#3  gap_fill — extract_gaps on an RH sorry-skeleton (the real RH fill workflow)")
    # This is the ACTUAL RH pattern: the zeta-log-bound thread was a sorry-skeleton
    # filled lemma-by-lemma (zeta_partial_sum_repr, zeta_trunc, zeta_log_bound).
    # extract_gaps recovers each `:= by sorry` lemma as a standalone goal to attack.
    skeleton = (
        "theorem norm_partial_sum_le {s : ℂ} (hs : 1 ≤ s.re) {N : ℕ} (hN : 1 ≤ N) : "
        "‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ 1 + Real.log N := by sorry\n\n"
        "theorem zeta_log_bound {σ t : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 2 ≤ |t|) : "
        "‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ 6 * (1 + Real.log |t|) := by sorry\n"
    )
    gaps = gap_fill.extract_gaps(skeleton)
    print(f"  extract_gaps recovered {len(gaps)} RH goal(s):")
    for g in gaps:
        print(f"    - {g.name}: {g.statement[:64]}...")
    # HONEST: the BG route-matcher (match_log_enclosure) is FSTAR-shaped; RH log
    # goals carry no FSTAR term, so it declines — the RH-relevant half of gap_fill
    # is the generic goal extraction, not the BG log-combination router.
    rh_goal = "Real.log (1 + x) ≤ x"
    spec = gap_fill.match_log_enclosure(rh_goal)
    print(f"  match_log_enclosure('{rh_goal}') -> {spec}  (correctly declines: no FSTAR term)")
    return len(gaps) == 2


# ---------------------------------------------------------------- #4
def n4_meta_bundle():
    hdr("#4  cert_meta + bundle — metadata / content-addressed index / dedup on RH atoms")
    # Real RH atoms: the tangent bound (log-face _upper) and a rational fact.
    tangent = (
        "theorem rh_tangent (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by\n"
        "  have hy : (0:ℝ) < 1 + x := by linarith\n"
        "  have h := Real.log_le_sub_one_of_pos hy\n  linarith\n"
    )
    const_c = "theorem rh_c_pos : (0:ℝ) < 6 := by norm_num\n"
    m = cert_meta.extract_cert_meta(tangent)
    print(f"  cert_meta rh_tangent: name={m.name} type_hash={m.type_hash[:12]} tactics={m.tactic_counts}")
    idx = cert_meta.CertIndex()
    idx.add(cert_meta.extract_cert_meta(tangent))
    idx.add(cert_meta.extract_cert_meta(const_c))
    print(f"  CertIndex size={len(idx.metas)} duplicates={idx.duplicates()} (content-addressed)")
    stats = bundle.bundle_stats(bundle.merge_bundle([tangent, const_c, tangent]))  # tangent duped
    print(f"  merge_bundle([tangent,c,tangent]) stats: {stats}  (dedup shared atom)")
    conflict = False
    try:
        bundle.merge_bundle([tangent, "theorem rh_tangent : (1:ℝ)=1 := rfl\n"])  # same name diff stmt
    except ValueError as e:
        conflict = True
        print(f"  name-conflict guard fired: {str(e)[:70]}")
    return conflict


# ---------------------------------------------------------------- #5
def n5_signature_gate():
    hdr("#5  signature_gate — assert the emitted RH atom states the INTENDED claim")
    # The positive half of the trust boundary (AXLE verify_proof signature match):
    # negative_control kills a FALSE claim; this kills a WEAKER/DIFFERENT true claim
    # that still compiles. The RH thread hit this by hand — an ∃C restatement of
    # zeta_log_bound gives NO region constant vs the intended explicit C.
    from telperion.signature_gate import check_signatures, forall_type
    content = (
        "import Mathlib\n\n"
        "theorem rh_tangent (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by\n"
        "  have hy : (0:ℝ) < 1 + x := by linarith\n"
        "  have h := Real.log_le_sub_one_of_pos hy\n  linarith\n"
    )
    binders = "(x : ℝ) (hx : 0 ≤ x)"
    correct = forall_type(binders, "Real.log (1 + x) ≤ x")
    weaker = forall_type(binders, "Real.log (1 + x) ≤ x + 1")   # silent restatement
    exists_c = "∃ C : ℝ, ∀ (x : ℝ), 0 ≤ x → Real.log (1 + x) ≤ C * x"  # ∃C vs explicit
    if not RUN_LEAN:
        print("  KERNEL tier GATED OFF — guard block staged for CI:")
        from telperion.signature_gate import build_sig_guards
        for ln in build_sig_guards({"rh_tangent": correct}).splitlines():
            print("    | " + ln)
        return True
    ok_correct = check_signatures(content, env_dir=ENV_DIR, expected={"rh_tangent": correct})
    ko_weaker = check_signatures(content, env_dir=ENV_DIR, expected={"rh_tangent": weaker})
    ko_exists = check_signatures(content, env_dir=ENV_DIR, expected={"rh_tangent": exists_c})
    print(f"  CORRECT  (≤ x)     : okay={ok_correct.okay} all_match={ok_correct.all_match}  (want MATCH)")
    print(f"  WEAKER   (≤ x+1)   : okay={ko_weaker.okay} all_match={ko_weaker.all_match}  (want MISMATCH)")
    print(f"  EXISTS-C (∃C form) : okay={ko_exists.okay} all_match={ko_exists.all_match}  (want MISMATCH)")
    # gate is correct iff it ACCEPTS the intended and REJECTS both restatements.
    return ok_correct.all_match and (not ko_weaker.all_match) and (not ko_exists.all_match)


if __name__ == "__main__":
    print(f"ENV_DIR = {ENV_DIR}")
    print(f"RUN_LEAN = {RUN_LEAN}  (kernel tier {'ON' if RUN_LEAN else 'OFF — Python/sympy tier only'})")
    results = {}
    for fn in (n1_negative_control, n2_emit_enclosure, n3_gapfill, n4_meta_bundle,
               n5_signature_gate):
        try:
            results[fn.__name__] = fn()
        except Exception as e:
            import traceback
            traceback.print_exc()
            results[fn.__name__] = f"ERROR: {type(e).__name__}: {e}"
    hdr("SUMMARY")
    for k, v in results.items():
        print(f"  {k}: {v}")
    print("\nconjecture1_proved = False.")
    # Exit non-zero if any capability did not hold — so the CI kernel tier fails
    # loudly (forged proof NOT rejected, or a true control NOT clean).
    import sys
    ok = all(v is True for v in results.values())
    sys.exit(0 if ok else 1)
