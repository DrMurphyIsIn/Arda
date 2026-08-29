"""The per-n extremality PARITY LAW, kernel-gated (exact extremal Phi^11 values, n<=14).

Audit finding (2026-08-29, corrects PROOF_STATUS #4): the per-n Phi^11 maximizer over ALL
trees follows a parity law -- the near-star N(0,(n-1)/2) wins at every ODD n (it only exists
at odd n = 2s+1), and a multi-hub wins at every EVEN n.  No max exceeds 1; equality (the tie)
occurs only at n=11, where the maximizer is the near-star N(0,5).  This is the structural
reason Track-B's tree->hub reduction has no clean shortcut: the extremal template oscillates
with parity, so no single hub family dominates all trees.

SCOPE (honest).  Maximality is exhaustive over all non-isomorphic trees on n vertices, verified
in Python (`multi_hub_extremality.phi_maximizer`, via networkx enumeration) -- the same
exhaustive-small-n status PROOF_STATUS already assigns to spider extremality.  The KERNEL gates
the exact rational Phi^11 of each per-n extremal tree and its BG bound: `< 1` for every
n in [4,14] except `= 1` at n=11 (the tie).  So this is the exhaustive small-n base case of BG
(all trees, n<=14), with the extremal values kernel-recorded and the parity structure exhibited.
Not a proof of BG; conjecture1_proved = False.

    python3 examples/bg_parity_law/generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.multi_hub_extremality import phi_maximizer, is_near_star  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGParityLaw.lean"
NS = range(4, 15)  # n = 4..14 (phi_maximizer sweep ~2.7s; fully exhibits the parity alternation)


def _facts():
    out = []
    for n in NS:
        phi, edges = phi_maximizer(n)
        ns = is_near_star(n, edges)
        assert phi <= 1 and (phi == 1) == (n == 11), (n, phi)
        assert ns == (n % 2 == 1), (n, ns)  # near-star wins iff n odd
        out.append((n, phi, ns))
    return out


def build() -> str:
    lines = []
    for n, phi, ns in _facts():
        struct = "near-star N(0,%d)" % ((n - 1) // 2) if ns else "multi-hub"
        P, Q = phi.numerator, phi.denominator
        if n == 11:
            thm = f"theorem bg_extremum_n{n} : (({P} : ℚ) / {Q}) = 1 := by norm_num"
            tag = f"-- n={n} [odd, {struct}]: THE TIE -- Phi^11 = 1 exactly"
        else:
            rel = "odd" if n % 2 else "even"
            thm = f"theorem bg_extremum_n{n} : (({P} : ℚ) / {Q}) < 1 := by norm_num"
            tag = f"-- n={n} [{rel}, {struct}]: max Phi^11 < 1 (strictly below the tie)"
        lines.append(f"{tag}\n{thm}")
    body = "\n\n".join(lines)
    header = (
        "/- The per-n extremality PARITY LAW, kernel-gated (exact extremal Phi^11, n<=14).\n"
        "   Near-star wins at every ODD n (exists only at n=2s+1), multi-hub at every EVEN n;\n"
        "   max Phi^11 < 1 for all n in [4,14] except = 1 at n=11 (the tie N(0,5)).  Maximality\n"
        "   is exhaustive-Python (all trees on n vertices); the kernel gates each extremal value\n"
        "   + its BG bound -- the exhaustive small-n base case, exhibiting the parity structure.\n"
        "   Not a proof of BG; conjecture1_proved = False. -/\n"
        "import Mathlib\n\nnamespace BGParityLaw\n\n"
    )
    return header + body + "\n\nend BGParityLaw\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        if not OUT.exists():
            print(f"MISSING: {OUT}")
            return 1
        if OUT.read_text() != src:
            print(f"DRIFT: {OUT} differs from freshly generated output")
            return 1
        print(f"OK: {OUT} matches")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(src)
    print(f"WROTE: {OUT} ({len(NS)} per-n extremal Phi^11 facts, n=4..14)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
