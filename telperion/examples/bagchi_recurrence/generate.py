"""Generate Bagchi-recurrence observations — Face 4 (recurrence) of the RH obstruction.

    python examples/bagchi_recurrence/generate.py           # write lean/BagchiRecurrence.lean
    python examples/bagchi_recurrence/generate.py --check    # drift check (no write)

Bagchi (1981): RH ⟺ ζ is strongly recurrent in the strip 1/2 < Re s < 1.  For a
few shifts τ over a compact rational box K (a σ×t grid inside the strip, right of
the critical line to stay zero-free), the emitter certifies
``sup_{grid} |ζ(s+iτ) − ζ(s)| ≤ ε`` — each per-point deviation a rigorous
flint/Arb ``acb.zeta`` upper bound, the grid-max ``M`` carried as hypothesis
``hdev`` and ``ε`` a readable rounded-up cap (``ε > M``, so the theorem is
substantive).  Also carries ``bagchi_recurrence_refutes``, the falsifiability face.

HONEST SCOPE: the certified statement is the sup over the finite GRID; a continuous
sup over K needs a modulus-of-continuity argument (documented, not claimed).  At
accessible heights ζ does not nearly repeat, so ε is O(1), not small — this is the
finite recurrence INSTRUMENT, not a strong-recurrence claim.  conjecture1_proved
= False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_bagchi_recurrence import (  # noqa: E402
    BagchiRecurrenceEmitter,
    bagchi_grid_max,
    bagchi_recurrence_family,
    bagchi_refutation_atom_lean,
    scan_best_shift,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# Box K: σ ∈ [3/5, 7/10] (inside the strip, right of Re=1/2), t ∈ [10, 12].
SIGMAS = [Fraction(3, 5), Fraction(13, 20), Fraction(7, 10)]
TS = [Fraction(10), Fraction(11), Fraction(12)]
PREC_BITS = 160
_OUT = Path(__file__).resolve().parent / "lean" / "BagchiRecurrence.lean"


def _round_up_6sig(x: Fraction) -> Fraction:
    """Smallest 6-significant-decimal fraction ≥ x (x > 0), STRICTLY above x when x
    is not already 6-sig — a readable ε with M ≤ ε and (for a non-degenerate M) a
    substantive M ≤ ε."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**5:
        exp += 1
    num = -((-x.numerator * 10**exp) // x.denominator)  # ceil
    up = Fraction(num, 10**exp)
    if up == x:  # already representable: bump one ulp so ε > M (substantive)
        up = Fraction(num + 1, 10**exp)
    return up


def build() -> str:
    # a few shifts: the best in [1,60] plus two more distinct integer shifts
    best_tau, _ = scan_best_shift(SIGMAS, TS, 1, 60, prec_bits=120)
    taus = sorted({best_tau, best_tau + 7, best_tau + 23})
    specs = {}
    for tau in taus:
        M, _ = bagchi_grid_max(tau, SIGMAS, TS, PREC_BITS)
        eps = _round_up_6sig(M)
        assert eps >= M and eps > M  # substantive + valid
        specs[tau] = {"tau": tau, "sigmas": SIGMAS, "ts": TS, "eps": eps,
                      "prec_bits": PREC_BITS}

    fam = bagchi_recurrence_family(
        "BagchiRecurrence",
        GridSpec([("tau", taus)]),
        lambda pt: f"bagchi_tau{pt['tau']}",
        spec=lambda pt: specs[pt["tau"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("BagchiRecurrence",),
            prelude=bagchi_refutation_atom_lean(),
        ),
        [BagchiRecurrenceEmitter()],
        ValidationReport(checks=(("bagchi_recurrence", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BagchiRecurrence.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} (recurrence observations + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
