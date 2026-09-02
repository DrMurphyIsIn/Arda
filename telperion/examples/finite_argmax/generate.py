"""Generate the finite-argmax example: certify -> emit -> write.

    python examples/finite_argmax/generate.py           # write lean/FiniteArgmax.lean
    python examples/finite_argmax/generate.py --check    # drift check (no write)

Finite extremality with a strict cross-multiplied margin — a designated winner
rational strictly beats every competitor in a finite list (each fact is the
integer inequality p_i*q_w < p_w*q_i, closed by norm_num).  Models the PROVEN
examples/bg_extremality `bgext_n*_beats_runnerup` / `bgext_n*_value_le1` pattern.

Three instances:
  - nearstar_n5:  BG near-star N(0,2), winner Phi^11 = 73039787676416/92354487127101
                  (< 1; value-load on) beats runner-up 3123330500020692224/16360320331104560847
  - nearstar_n11: BG near-star N(0,5), winner Phi^11 = 1/1 (the TIE; value-load off)
                  beats runner-up 25804264053054077850709/46523913960640966796875
  - small_multi:  a small illustrative argmax, winner 3/4 (< 1) beats 1/2, 2/3, 5/7

NOTE: the `finite_argmax` kind is not yet registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it is, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (not the re-exported certify() function) — its dispatch
from telperion.emit_finite_argmax import (  # noqa: E402
    FiniteArgmaxMarginEmitter,
    finite_argmax_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> {"winner": (p,q), "competitors": [(p,q), ...], "lt_one": bool}
_SPECS = {
    0: {
        "winner": (73039787676416, 92354487127101),
        "competitors": [(3123330500020692224, 16360320331104560847)],
        "lt_one": True,
    },
    1: {
        "winner": (1, 1),
        "competitors": [(25804264053054077850709, 46523913960640966796875)],
        "lt_one": False,
    },
    2: {
        "winner": (3, 4),
        "competitors": [(1, 2), (2, 3), (5, 7)],
        "lt_one": True,
    },
}
_NAMES = {0: "fa_nearstar_n5", 1: "fa_nearstar_n11", 2: "fa_small_multi"}
_OUT = Path(__file__).resolve().parent / "lean" / "FiniteArgmax.lean"


def build() -> str:
    fam = finite_argmax_family(
        "FiniteArgmax",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("FiniteArgmax",)),
        [FiniteArgmaxMarginEmitter()],
        ValidationReport(checks=(("finite_argmax", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: FiniteArgmax.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
