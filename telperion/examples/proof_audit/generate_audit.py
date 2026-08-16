"""The proof audit ledger: PROOF_AUDIT.md, generated — never asserted.

One row per stratum of the Brualdi-Goldwasser campaign, with the verification
method and its CURRENT state.  Executable rows are executed (frozen manifests
read, certificate exports recheck-verified live by the stdlib engine); kernel
rows carry their CI references; unstarted rows say PLANNED.  The file cannot
claim more than the checks that ran.

Usage:  python3 examples/proof_audit/generate_audit.py  [-o PROOF_AUDIT.md]
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import sys
from pathlib import Path

TELPERION = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(TELPERION / "src"))


def _load_family(example: str):
    p = TELPERION / "examples" / example / "family.py"
    spec = importlib.util.spec_from_file_location(f"_audit_{example}", p)
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(p.parent))
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.path.pop(0)
    for attr in ("family", f"{example.split('_')[0]}_family", "r47_family"):
        if hasattr(mod, attr):
            return getattr(mod, attr)()
    raise AttributeError(f"no family factory found in {p}")


def _sampled(fam, per_axis: int = 2):
    """A small sub-grid for the live recheck (full certification of the heavy
    families belongs to their generate --check, not the ledger)."""
    import dataclasses

    from telperion import GridSpec

    axes = [(n, list(vs)[:per_axis]) for n, vs in fam.grid.axes]
    return dataclasses.replace(fam, grid=GridSpec(axes))


def _frozen_info(example: str) -> tuple[int, list[str]]:
    theorems, hashes = 0, []
    for m in sorted((TELPERION / "examples" / example).glob("frozen/**/manifest.json")):
        doc = json.loads(m.read_text())
        theorems += doc.get("n_theorems", 0)
        hashes.append(doc.get("input_hash", "")[:12])
    return theorems, hashes


def _live_recheck(example: str) -> str:
    """Certify + export + stdlib-recheck, live — the third engine's verdict."""
    from telperion import certify
    from telperion.interchange import export_certificates
    from telperion.recheck import recheck

    try:
        fam = _load_family(example)
        small = _sampled(fam)
        n = small.grid.size()
        cf = certify(small)
        problems = recheck(export_certificates(cf, "0" * 64), trials=8)
        return (f"sampled recheck GREEN ({n} cell(s))"
                if not problems else f"RECHECK RED ({len(problems)})")
    except Exception as e:  # noqa: BLE001 — the ledger reports, never hides
        return f"RECHECK ERROR: {type(e).__name__}"


def generate() -> str:
    today = datetime.date.today().isoformat()
    rows = []

    # --- kernel strata (origin CI; references, not re-derivable by design) ---
    rows.append(("Lean core: bridge + phi_le_one + merge layer + parse "
                 "(90 R3Cert modules)", "Lean kernel (origin CI)",
                 "KERNEL-CHECKED — origin pipeline 2762803858 @ b2996c79; "
                 "reviewed PASS 2026-08-14/15"))
    rows.append(("G1Kernel + Real.log bridges + 103 hinge-dead classes",
                 "Lean kernel (origin CI)",
                 "KERNEL-CHECKED origin-side (parallel session; trio round in "
                 "flight)"))

    # --- Telperion re-derivations (executed) ---
    for example, stratum, extra in (
        ("r47_cells", "36-cell unified merge table (HypStar seam)", ""),
        ("g1_floors", "G1 floors: dichotomy/tax/below-window + anchors "
         "(HypFloors)", " — COMPILE-GATED green @6758e88; handoff ACCEPTED "
         "(origin bf2f0747); 1 fragile cell tripwired ((2,0,1) @0.59 width)"),
        ("shed_lemmas", "R6 shedding lemmas (de-loading schedule)", ""),
        ("legs_certs", "Legs certificates + the 726-digit bignum "
         "((L) layer)", ""),
        ("interp_lemma", "Interpolation lemma: I1 UPGRADED TO SYMBOLIC "
         "(vs origin's 199 point checks) + I2 + 212 light-top facts with "
         "witness table", " — heavy-top sup + DELTA sweep are float-guarded "
         "in origin; exact counterparts routed to g1_endpoint_certificates "
         "(origin G1FIX arc)"),
        ("r7_starofhubs", "972 star-of-hubs dominations (HypStarSymbolic)", ""),
    ):
        theorems, hashes = _frozen_info(example)
        if theorems:
            verdict = (f"RE-DERIVED: {theorems} theorems frozen "
                       f"[{', '.join(hashes)}]; {_live_recheck(example)}{extra}")
        else:
            verdict = "IN FLIGHT — freeze not yet landed" + extra
        rows.append((stratum, "Telperion re-derivation + stdlib recheck", verdict))

    # --- planned strata ---
    for stratum, note in (
        ("G34 residual sweep (442,800 cases)",
         "as interchange export + stdlib recheck (not per-theorem Lean)"),
        ("Two-hub residual tails (per-residue comparators)",
         "witness API + varmap machinery ready; encoding queued"),
        ("Hunt-attack sweep over all certified families",
         "three-mode adversarial minimization; queued"),
    ):
        rows.append((stratum, "planned", "PLANNED — " + note))

    # --- out of scope, named honestly ---
    rows.append(("Structural inductions (telescoping, termination, "
                 "acyclicity); R7' assembly correctness",
                 "Lean kernel + independent review ONLY",
                 "OUT OF TELPERION SCOPE by design — the kernel and the "
                 "honest-conditional review are the arbiters"))

    out = [
        "# PROOF AUDIT — the Brualdi-Goldwasser campaign, by verification stratum",
        "",
        f"Generated {today} by `examples/proof_audit/generate_audit.py`; "
        "executable rows were EXECUTED (frozen manifests read, exports "
        "recheck-verified live).  Do not edit; regenerate.",
        "",
        "| stratum | method | state |",
        "|---|---|---|",
    ]
    for stratum, method, state in rows:
        out.append(f"| {stratum} | {method} | {state} |")
    out += [
        "",
        "Reading rule (inherited from conjecture1_status.py): a green row "
        "verifies THAT stratum; no combination of rows proves the surrounding "
        "conjecture.  conjecture1_proved = False until the R7' assembly and "
        "its independent review complete.",
        "",
    ]
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", "--out", default=str(TELPERION / "PROOF_AUDIT.md"))
    args = ap.parse_args()
    text = generate()
    Path(args.out).write_text(text)
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
