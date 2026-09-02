"""Generate the BG leaf-exchange certificate (extremality assembly leg #5, kernel-gated).

    python examples/bg_leaf_exchange/generate.py [--check]

A bare leaf child never occurs in the M_d argmax: for hub degree d=3..6, replacing a leaf child by a cherry
strictly raises ell (ell(B(d-1)) - ell((d-2)cherries+leaf) = log(3/2) - F* + log((4d-1)/(4d+1)) > 0), which
clears (x11, 11 F*=log(621/64)) to the PURE RATIONAL (3(4d-1)/(2(4d+1)))^11 > 621/64. So the single-child
induction excludes leaf children. See docs/BG_EXTREMALITY_ASSEMBLY_20260902.md. conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))
from telperion.tie_regime import LeafExchangeCertificate  # noqa: E402

_CERT = LeafExchangeCertificate()
_OUT = Path(__file__).resolve().parent / "lean" / "BGLeafExchange.lean"


def build() -> str:
    assert _CERT.check(), "leaf-exchange certificate does not hold"
    head = (
        "/- BG extremality assembly leg #5: leaf-exchange (bare leaves excluded from the M_d argmax).\n"
        "   For hub degree d=3..6, leaf->cherry strictly raises ell; cleared (x11) to the pure rational\n"
        "   (3(4d-1)/(2(4d+1)))^11 > 621/64. conjecture1_proved = False. -/\n"
    )
    return head + _CERT.lean_module("BGLeafExchange")


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true"); a = ap.parse_args()
    src = build()
    if a.check:
        cur = _OUT.read_text() if _OUT.exists() else ""
        print("ok: matches" if cur == src else "DRIFT: re-run generate.py")
        return 0 if cur == src else 1
    _OUT.parent.mkdir(parents=True, exist_ok=True); _OUT.write_text(src)
    print(f"wrote {_OUT.relative_to(ROOT)}"); return 0


if __name__ == "__main__":
    sys.exit(main())
