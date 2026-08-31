"""Generate the BG star-of-cherry-brooms c=5 optimum certificate (route-b retarget, kernel-gated).

    python examples/bg_broom_optimum/generate.py           # write lean/BGBroomOptimum.lean
    python examples/bg_broom_optimum/generate.py --check    # drift check (no write)

The star-of-cherry-brooms `S(k,c)` (one central hub joined to `k` branch-hubs, each of degree `c+1` carrying `c`
length-2 cherries) has asymptotic per-vertex free-energy density `F(c) = log(total(c))/(2c+1)` for the Laplacian
ratio `pi = per(L)/prod(deg)`, where `total(c) = (3/2)^(c-1)(4c+3)/(2(c+1))` (exact; `total(5) = 621/64`).  Its
STAR core beats Pant 2026's path-core caterpillars: `F(5) = 0.206586 > 0.205098` (caterpillar sup).

This example kernel-gates the DISCRETE optimum `c* = 5`: `F(5) > F(c)` for the competitors `c in {2,3,4,6,7,8}`.
The `(2c+1)`-th roots in `rate(c) = total(c)^(1/(2c+1))` are cleared by CROSS-EXPONENTIATION --

    rate(5) > rate(c)   <=>   total(5)^(2c+1) > total(c)^(2*5+1) = total(c)^11

both sides exact rationals -- so each atom is a `norm_num`-checkable rational inequality.  The `total(c)` values
ARE the exact branch weights (`spider_Z` closed form == `matching_free_energy.rho`, checked in
`tests/test_spider_broom.py`).  This certifies only the `c`-argmax among brooms; the family-vs-caterpillar
dominance and the global-maximizer question (still OPEN) are separate.  NOT a proof of Brualdi-Goldwasser.
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.spider_broom import BroomOptimumCertificate  # noqa: E402

_CERT = BroomOptimumCertificate()
NAMESPACE = "BGBroomOptimum"
_OUT = Path(__file__).resolve().parent / "lean" / "BGBroomOptimum.lean"


def build() -> str:
    assert _CERT.check(), "broom c=5 optimum certificate does not hold"
    head = (
        "/- BG star-of-cherry-brooms c=5 optimum (route-b retarget, kernel-gated).\n"
        "   S(k,c): central hub + k branch-hubs (deg c+1), each with c length-2 cherries. Asymptotic density\n"
        "   F(c)=log(total(c))/(2c+1), total(c)=(3/2)^(c-1)(4c+3)/(2(c+1)), total(5)=621/64. Its star core beats\n"
        "   Pant 2026's path-core caterpillars: F(5)=0.206586 > 0.205098. Atoms: the discrete optimum c*=5 via\n"
        "   cross-exponentiation rate(5)>rate(c) <=> total(5)^(2c+1) > total(c)^11 (clears the roots -> exact\n"
        "   rationals). Certifies only the c-argmax among brooms; family-vs-caterpillar dominance and the global\n"
        "   maximizer (OPEN) are separate. NOT a proof of Brualdi-Goldwasser. conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module(NAMESPACE)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        if cur != src:
            print(f"DRIFT: {_OUT.relative_to(ROOT)} is stale -- re-run generate.py"); return 1
        print(f"ok: {_OUT.relative_to(ROOT)} matches"); return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
