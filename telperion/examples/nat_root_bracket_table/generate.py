"""Generate the nat-root-bracket-table example: certify -> emit -> write.

    python examples/nat_root_bracket_table/generate.py           # write lean/NatRootBracket.lean + lean/NatRootBracketTable.lean
    python examples/nat_root_bracket_table/generate.py --check   # drift check (no write)

Four instances, every emitted ℕ fact decided by ``decide +kernel`` and lifted to ℝ by the
once-proved ``NatRootBracket`` prelude:

  * ``sum_neg34_400``   -- ∑_{i<400} (i+1)^(-3/4) at scale 10^10 in two blocks of 200 (the CN-1
                           ZetaTables shape for sigma = 3/4, cut to M = 400);
  * ``sum_neg78_400``   -- the same for sigma = 7/8;
  * ``pow_1001_pos14``  -- 1001^(1/4) at scale 10^12 (a positive exponent; the CN-1
                           ``n1001_quarter`` single bracket);
  * ``rat_64003_8_neg58`` -- (64003/8)^(-5/8) at scale 10^12 (a rational base; the CN-1
                           GammaRatio ``g_hA`` factor (8000 + 3/8)^(3/8 - 1)).

The prelude ``NatRootBracket.lean`` is emitted from the SAME module
(:func:`telperion.nat_root_bracket_prelude_lean`), so the drift check covers it too.

conjecture1_proved = False -- finite arithmetic facts about rational powers and their partial
sums; nothing here concerns zeta or class numbers.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    NatRootBracketTableEmitter, ValidationReport, certify, emit,
    nat_root_bracket_certificate, nat_root_bracket_prelude_lean,
    nat_root_bracket_table_certificate, nat_root_bracket_table_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
_PRELUDE_OUT = _LEAN / "NatRootBracket.lean"
_OUT = _LEAN / "NatRootBracketTable.lean"

_SPECS = {
    0: ("sum_neg34_400", dict(p=3, q=4, terms=400, scale=10 ** 10, block=200)),
    1: ("sum_neg78_400", dict(p=7, q=8, terms=400, scale=10 ** 10, block=200)),
    2: ("pow_1001_pos14", dict(base=1001, p=1, q=4, scale=10 ** 12, sign=+1)),
    3: ("rat_64003_8_neg58", dict(base=(64003, 8), p=5, q=8, scale=10 ** 12, sign=-1)),
}


def build() -> str:
    fam = nat_root_bracket_table_family(
        "NatRootBracketTable",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _SPECS[pt["case"]][0],
        spec=lambda pt: dict(_SPECS[pt["case"]][1]),
    )
    checks = []
    for case in sorted(_SPECS):
        name, spec = _SPECS[case]
        spec = dict(spec)
        if "terms" in spec:
            cert = nat_root_bracket_table_certificate(spec.pop("p"), spec.pop("q"), spec.pop("terms"),
                                                      **spec)
            checks.append((f"totals_ordered_{name}", cert.lo_total <= cert.hi_total))
            checks.append((f"one_ulp_per_term_{name}",
                           cert.hi_total - cert.lo_total <= cert.terms))
        else:
            cert = nat_root_bracket_certificate(spec.pop("base"), spec.pop("p"), spec.pop("q"), **spec)
            checks.append((f"bracket_ordered_{name}", cert.lo <= cert.hi <= cert.lo + 1))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("NatRootBracketTable",), imports=("NatRootBracket",)),
        [NatRootBracketTableEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    prelude = nat_root_bracket_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("NatRootBracket.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("NatRootBracketTable.lean")
        if bad:
            print(f"DRIFT: {', '.join(bad)} do(es) not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _LEAN.mkdir(exist_ok=True)
    _PRELUDE_OUT.write_text(prelude, encoding="utf-8")
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_PRELUDE_OUT} ({len(prelude)} bytes) and {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
