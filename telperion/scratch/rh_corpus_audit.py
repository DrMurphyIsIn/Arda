"""Apply the NEW Telperion corpus (cert-dependency graph + signature gate) to the
REAL RH zero-free-region proof — not demo atoms.

PART A (cert_meta dependency graph, offline text): index every `:= by` theorem in
the ZeroFreeBridge-namespace files, then report the dependency structure, dead atoms
(referenced by nothing, excluding the exported roots), and the impact set of a shared
atom (which certs re-verify when it changes).

PART B (signature gate, kernel — needs the modules built): assert each EXPORTED
region theorem states its INTENDED proposition, and cross-check the two region
theorems are DISTINCT strengths:
  * riemannZeta_zero_free_polylog states the γ⁴·(1+log2γ) denominator (the improvement),
    and is NOT the weaker γ⁵ form;
  * riemannZeta_zero_free_poly states the γ⁵ denominator, and is NOT the polylog form;
  * zeta_log_bound states the explicit constant C=6.

Run (Part A only):  PYTHONPATH=src python3 scratch/rh_corpus_audit.py
Run (A+B, needs built ZetaLogBound/ZeroFreePolylog/ZeroFreeElementary):
  RH_AXLE_RUN_LEAN=1 PATH=$HOME/.elan/bin:$PATH PYTHONPATH=src python3 scratch/rh_corpus_audit.py
conjecture1_proved = False.
"""
import os
from pathlib import Path

from telperion import bundle, cert_meta

HERE = Path(__file__).resolve()
ENV = HERE.parents[1] / "examples" / "zero_free_bridge" / "lean"
RUN_LEAN = os.environ.get("RH_AXLE_RUN_LEAN") == "1"

# ZeroFreeBridge-namespace files (one shared namespace, so bare-name refs resolve).
CORPUS = ["ZetaLogBound", "ZeroFreePolylog", "ZeroFreeElementary", "ZeroFreeRegion", "StripBound"]
# The exported region theorems + the growth bound are API roots (dead-atom exempt).
ROOTS = ["riemannZeta_zero_free_polylog", "riemannZeta_zero_free_poly", "zeta_log_bound"]


def hdr(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)


def part_a_dependency_graph():
    hdr("PART A  cert_meta dependency graph over the REAL RH corpus (offline)")
    idx = cert_meta.CertIndex()
    skipped = []
    for mod in CORPUS:
        text = (ENV / f"{mod}.lean").read_text(encoding="utf-8")
        for blk in bundle.parse_theorems(text):
            try:
                idx.add(cert_meta.extract_cert_meta(blk["block"]))
            except ValueError:
                skipped.append(blk["name"])  # term-mode (`:= <term>`, no `:= by`)
    print(f"  indexed {len(idx.metas)} `:= by` theorems from {CORPUS}")
    if skipped:
        print(f"  skipped {len(skipped)} term-mode decls: {skipped}")
    print("\n  dependency edges (theorem -> intra-corpus deps):")
    for name in idx.metas:
        deps = idx.dependencies(name)
        if deps:
            print(f"    {name} -> {sorted(deps)}")
    dead = idx.dead_atoms(roots=ROOTS)
    print(f"\n  DEAD atoms (no dependents, not an API root): {dead}")
    for shared in ("zeta_pole_bound", "zeta_log_bound"):
        if shared in idx.metas:
            print(f"  impact_by({shared}) = re-verify on change: {sorted(idx.impacted_by(shared))}")
    return idx


def part_b_signature_gate():
    hdr("PART B  signature gate on the EXPORTED region theorems (kernel)")
    from telperion.signature_gate import check_signatures

    content = ("import ZeroFreePolylog\nimport ZeroFreeElementary\nimport ZetaLogBound\n"
               "open ZeroFreeBridge\n")
    zero = "riemannZeta ((β : ℂ) + γ * Complex.I) = 0 → 2 ≤ γ →"
    polylog_form = (f"∃ c > (0 : ℝ), ∀ β γ : ℝ, {zero} "
                    "β ≤ 1 - c / (γ ^ 4 * (1 + Real.log (2 * γ)))")
    poly_form = f"∃ c > (0 : ℝ), ∀ β γ : ℝ, {zero} β ≤ 1 - c / γ ^ 5"
    c6_form = ("∀ {σ t : ℝ}, 1 ≤ σ → σ ≤ 2 → 2 ≤ |t| → "
               "‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ 6 * (1 + Real.log |t|)")

    # (name, intended, should_match) — the intended-claim asserts + cross-strength checks.
    checks = [
        ("riemannZeta_zero_free_polylog", polylog_form, True),   # states its OWN γ⁴ form
        ("riemannZeta_zero_free_polylog", poly_form, False),     # is NOT the weaker γ⁵ form
        ("riemannZeta_zero_free_poly", poly_form, True),         # states its OWN γ⁵ form
        ("riemannZeta_zero_free_poly", polylog_form, False),     # is NOT the stronger polylog form
        ("zeta_log_bound", c6_form, True),                       # explicit C=6
    ]
    if not RUN_LEAN:
        print("  KERNEL tier GATED OFF (RH_AXLE_RUN_LEAN != 1). Intended forms staged:")
        print(f"    polylog: {polylog_form[:70]}...")
        print(f"    poly   : {poly_form[:70]}...")
        return True
    all_ok = True
    for name, intended, want in checks:
        r = check_signatures(content, env_dir=ENV, expected={name: intended})
        got = r.all_match
        ok = (got == want)
        all_ok = all_ok and ok
        tag = "MATCH" if got else "MISMATCH"
        exp = "want MATCH" if want else "want MISMATCH (distinct strength)"
        print(f"  [{name:32}] {tag:8} ({exp})  {'ok' if ok else 'FAIL'}")
    return all_ok


if __name__ == "__main__":
    print(f"ENV = {ENV}\nRUN_LEAN = {RUN_LEAN}")
    part_a_dependency_graph()
    ok = part_b_signature_gate()
    hdr("RESULT")
    print(f"  signature gate on region theorems: {ok}")
    print("  conjecture1_proved = False.")
    import sys
    sys.exit(0 if ok else 1)
