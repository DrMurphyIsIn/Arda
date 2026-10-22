"""Generate the quadratic-order-root-table example: certify -> emit -> write.

    python examples/quadratic_order_root_table/generate.py           # write lean/QuadraticOrderRoot.lean + lean/QuadraticOrderRootTable.lean
    python examples/quadratic_order_root_table/generate.py --check   # drift check (no write)

Five monogenic quadratic orders ``X^2 - t X + c`` (the rings of integers of ``Q(sqrt -m)`` for
``m = 2, 5, 14, 31, 163``), each with a short list of primes.  Per prime the kernel decides ONE
face -- RAMIFIED ``p | 4c - t^2``, SPLIT ``IsRootMod t c p y``, INERT
``forall z : ZMod p, z^2 - t z + c != 0`` -- and the ``QuadraticOrderRoot`` prelude turns it into
the Kummer-Dedekind statement about ``primesOver (p) (O_K)`` under the ``QuadInt`` hypothesis:

  * ``d8``   (t = 0, c = 2;  d = 8,   h(-8) = 1):   primes 2, 3, 5, 7, 199.  The CONTROL case: p = 2 = c
    is ramified (its root y = 0 is NOT a class-number witness, by the ``p != c`` conjunct);
    3 splits but 4 * 3 > 8; 5, 7, 199 are inert.  No witness, so no ``classNumber K != 1`` theorem.
  * ``d20``  (t = 0, c = 5;  d = 20,  h(-20) = 2):  primes 2, 3, 7.  p = 3 splits with y = 1 and
    IS a witness (12 <= 20, 3 != 5): ``d20_classNumber_ne_one``.  p = 7 splits (y = 3) but 28 > 20.
  * ``d56``  (t = 0, c = 14; d = 56,  h(-56) = 4):  primes 2, 3, 5, 7.  2 and 7 ramify; 3 (y = 1) and
    5 (y = 1) split and are witnesses.
  * ``d31``  (t = 1, c = 8;  d = 31,  h(-31) = 3):  primes 2, 5, 7.  All three split (y = 0, 2, 3) and
    all three are witnesses (8, 20, 28 <= 31).
  * ``d163`` (t = 1, c = 41; d = 163, h(-163) = 1): primes 2, 3, 5, 7, 41, 163, 193.  2, 3, 5, 7 are
    inert (the no-root table of CN-1's Minkowski converse for m = 163); 41 splits with y = 0 but
    4 * 41 = 164 > 163, so it is NOT a witness; 163 ramifies; 193 is inert (the kernel-cost probe
    for ``decide`` over ``ZMod 193``).

The prelude ``QuadraticOrderRoot.lean`` is emitted from the SAME module
(:func:`telperion.quadratic_order_root_prelude_lean`), so the drift check covers it too.

conjecture1_proved = False -- splitting facts about five explicit quadratic orders; nothing here
concerns zeta.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    QuadraticOrderRootTableEmitter, ValidationReport, certify, emit,
    quadratic_order_root_prelude_lean, quadratic_order_root_table_certificate,
    quadratic_order_root_table_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
_PRELUDE_OUT = _LEAN / "QuadraticOrderRoot.lean"
_OUT = _LEAN / "QuadraticOrderRootTable.lean"

_SPECS = {
    0: ("d8", dict(t=0, c=2, primes=[2, 3, 5, 7, 199])),
    1: ("d20", dict(t=0, c=5, primes=[2, 3, 7])),
    2: ("d56", dict(t=0, c=14, primes=[2, 3, 5, 7])),
    3: ("d31", dict(t=1, c=8, primes=[2, 5, 7])),
    4: ("d163", dict(t=1, c=41, primes=[2, 3, 5, 7, 41, 163, 193])),
}


def build() -> str:
    fam = quadratic_order_root_table_family(
        "QuadraticOrderRootTable",
        GridSpec([("case", sorted(_SPECS))]),
        lambda pt: _SPECS[pt["case"]][0],
        spec=lambda pt: dict(_SPECS[pt["case"]][1]),
    )
    checks = []
    for case in sorted(_SPECS):
        name, spec = _SPECS[case]
        cert = quadratic_order_root_table_certificate(spec["t"], spec["c"], spec["primes"])
        checks.append((f"faces_cover_primes_{name}",
                       [f.p for f in cert.faces] == list(spec["primes"])))
        checks.append((f"witness_iff_split_small_{name}",
                       all(f.witness == (f.face == "split" and 4 * f.p <= cert.d and f.p != cert.c)
                           for f in cert.faces)))
    # The control case must have NO witness: h(-8) = 1, and p = 2 = c is refused by p != c.
    d8 = quadratic_order_root_table_certificate(0, 2, [2, 3, 5, 7, 199])
    checks.append(("d8_has_no_witness", d8.witnesses == ()))
    checks.append(("d8_two_is_ramified_not_split", d8.faces[0].face == "ramified"))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("QuadraticOrderRootTable",), imports=("QuadraticOrderRoot",)),
        [QuadraticOrderRootTableEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    prelude = quadratic_order_root_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("QuadraticOrderRoot.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("QuadraticOrderRootTable.lean")
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
