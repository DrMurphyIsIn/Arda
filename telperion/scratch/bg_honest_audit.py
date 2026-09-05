"""BG honest-state audit: what is ACTUALLY proved on the conjecture1 spine.

Two layers, the first AUTHORITATIVE:
  (A) KERNEL truth — `#print axioms` (via verify_lean against the BUILT
      proof/formalization env) on the capstone assembly + the lemmas its proof uses.
      A clean axiom set (⊆ {propext, Quot.sound, Classical.choice}, NO sorryAx) proves
      the assembly is a genuine conditional, sorry-free.  Cannot be fooled by comments.
  (B) TEXTUAL map — COMMENT-STRIPPED scan of the corpus for real proof-body `sorry`
      (the prototype miscounted docstrings like "no `sorry`"), plus the exact open
      obligations (Hnorm / Hdom) the capstone is conditional on.

Run:  PATH=$HOME/.elan/bin:$PATH PYTHONPATH=src python3 scratch/bg_honest_audit.py
conjecture1_proved = False (this AUDITS honesty; it does not prove BG).
"""
import re
from pathlib import Path

from telperion import bundle
from telperion.lean_server import LeanServer
from telperion.verify import verify_lean

HERE = Path(__file__).resolve()
ROOT = HERE.parents[2] / "proof" / "formalization"      # built BG lake project
R3 = ROOT / "R3Cert"

# The assembly + the lemmas its two capstone proofs actually invoke.
CAPSTONE_IMPORTS = ("import R3Cert.R47TopCapstone\nimport R3Cert.R47TopCapstoneFixedN\n"
                    "import R3Cert.CavityTree\n")
# The two capstones are the AUTHORITATIVE signal: a clean axiom set on them
# transitively certifies their ENTIRE proof-dependency closure is sorry-free
# (sorryAx propagates through `#print axioms`).
CAPSTONES = [
    "R3Cert.Step3.conjecture1_of_layers",
    "R3Cert.Step3.conjecture1_of_layers_fixedN",
]
# Illustrative on-path lemmas (already transitively certified by the capstones).
USED_LEMMAS = [
    "R3Cert.Step3.chain_to_normalForm",
    "R3Cert.Step3.Balanced.chain",
    "R3Cert.Step3.Capped.chain",
    "R3Cert.Step3.chain_stateSize_eq",
    "R3Cert.RTree.Matched_factor",     # the prototype's false-positive "on-spine sorry"
]
KERNEL_DECLS = CAPSTONES + USED_LEMMAS

_BLOCK_C = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_C = re.compile(r"--[^\n]*")


def _strip_comments(s: str) -> str:
    return _LINE_C.sub("", _BLOCK_C.sub("", s))


def hdr(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)


def kernel_truth():
    hdr("(A) KERNEL TRUTH — #print axioms on the conjecture1 assembly (authoritative)")
    srv = LeanServer(ROOT)
    if not srv.probe(timeout=240):
        print("  [warm server unavailable; using cold verify]")
        srv = None
    r = verify_lean(CAPSTONE_IMPORTS, env_dir=ROOT, decls=KERNEL_DECLS,
                    server=srv, timeout=300)

    def verdict(d):
        axs = r.axioms.get(d)
        if axs is None:
            return None, "(no axiom report — name/import)"
        dirty = [a for a in axs if a == "sorryAx" or a.startswith("sorry")]
        return (not dirty), (f"axioms={axs}  -> " + ("CLEAN" if not dirty else f"DIRTY {dirty}"))

    print("  CAPSTONES (authoritative — clean ⟹ whole dependency closure sorry-free):")
    caps_clean = True
    for d in CAPSTONES:
        c, msg = verdict(d)
        print(f"    {d}:\n      {msg}")
        caps_clean = caps_clean and (c is True)
    print("  on-path lemmas (illustrative; already implied by the capstones):")
    for d in USED_LEMMAS:
        _, msg = verdict(d)
        print(f"    {d}: {msg}")
    if srv:
        srv.close()
    print(f"\n  ASSEMBLY kernel-clean conditional (both capstones sorry-free): {caps_clean}")
    return caps_clean


def textual_map():
    hdr("(B) TEXTUAL MAP — comment-stripped real sorries + the open obligations")
    files = list(R3.glob("*.lean")) + list((ROOT / "R7Hyps").rglob("*.lean"))
    real_sorry = {}
    total_thms = 0
    for f in files:
        try:
            txt = f.read_text(encoding="utf-8")
        except Exception:
            continue
        for b in bundle.parse_theorems(txt):
            total_thms += 1
            body = _strip_comments(b["block"])
            # count sorry only AFTER `:= by` / `:=` (the proof), not in the signature.
            m = re.search(r":=", body)
            proof = body[m.end():] if m else body
            if re.search(r"\bsorry\b", proof):
                real_sorry.setdefault(f.name, []).append(b["name"])
    n_real = sum(len(v) for v in real_sorry.values())
    print(f"  corpus: {total_thms} theorems/lemmas across {len(files)} files")
    print(f"  REAL proof-body `sorry` (comment-stripped): {n_real} "
          f"in {len(real_sorry)} file(s)")
    for f, names in sorted(real_sorry.items())[:20]:
        print(f"    - {f}: {names}")
    return real_sorry


def open_obligations():
    hdr("(C) THE OPEN FRONTIER — what conjecture1 is conditional on")
    print("  conjecture1_of_layers_fixedN (the WELL-POSED capstone) proves")
    print("      ∀ t, Aobj t ≤ Aobj (tie (usize t))")
    print("  FROM two undischarged hypotheses:")
    print("    Hnorm (size-preserving normalization): ∀ t, ∃ s, Balanced s ∧ Capped s ∧")
    print("           stateSize s = usize t ∧ Aobj t ≤ Aobj (backboneU s)")
    print("    Hdom  (normal-form domination): ∀ s, Balanced s → Capped s →")
    print("           (∀ u, ¬OrderedStep s u) → Aobj (backboneU s) ≤ Aobj (tie (stateSize s))")
    print("  It is NEVER instantiated with discharged Hnorm/Hdom (grep: only comments).")
    print("  ⇒ the ENTIRE remaining BG frontier = discharge Hnorm + Hdom.")
    print()
    print("  STATEMENT-IDENTITY caveat: Aobj t := Ztot (dtRealize t) (R47Tree.lean).")
    print("  Whether this equals CLASSICAL BG per(L)/∏deg or the rooted-branch Φ¹¹ variant")
    print("  (81/8 ≠ 621/64 at the tie) is the mislabeling risk to pin with the signature")
    print("  gate before any 'BG resolved' claim — a distinct, high-value follow-on.")


if __name__ == "__main__":
    print(f"BG env: {ROOT}")
    clean = kernel_truth()
    sor = textual_map()
    open_obligations()
    hdr("VERDICT")
    print(f"  assembly kernel-clean conditional: {clean}")
    print(f"  real open sorries in corpus: {sum(len(v) for v in sor.values())}")
    print("  remaining frontier: discharge Hnorm (size-preserving) + Hdom")
    print("  conjecture1_proved = False.")
