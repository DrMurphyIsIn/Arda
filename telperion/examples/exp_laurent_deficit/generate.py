"""Generate the exp-Laurent deficit certificate -- the Face 4 <-> Face 1 dictionary row.

    python examples/exp_laurent_deficit/generate.py           # write the zzl-island Lean
    python examples/exp_laurent_deficit/generate.py --check   # drift check (no write)

QC_RECURRENCE section 2 row (a) models an off-line pair at displacement `d` by two
one-sided clearances -- the outer mirror factor `e^d - 1` and the inner
transported-zero factor `1 - e^(-d)` -- and identifies their PRODUCT, the
recurrence deficit, with the Bragg amplification excess `e^d + e^(-d) - 2`.  Both
rows emitted here are that identity and its Weil-energy square:

    expLaurent_recurrence_deficit      (e^d - 1) * (1 - e^(-d))      = e^d + e^(-d) - 2
    expLaurent_recurrence_deficit_sq   (e^d - 1)^2 * (1 - e^(-d))^2  = (e^d + e^(-d) - 2)^2

Each is certified (kind `exp_laurent_identity`) as an EXACT reduction of
`lhs - rhs` modulo the single relation `e^d * e^(-d) = 1` in Q[y, z]; the quotient
-- the cofactor -- is the load-bearing certificate the emitted `linear_combination`
consumes.  Corrupt it and the Lean kernel rejects the theorem
(`negctrl_adapters/adapter_exp_laurent_identity.py`).

NEGATIVE CONTROL (always runs, before anything is written): the mistake
QC_RECURRENCE section 6 caught in ITSELF -- the SUM of the clearances,
`(e^d - 1) + (1 - e^(-d)) = 2d + O(d^3)`, is NOT the excess; only the product is.
The certifier must REFUSE the sum form with a nonzero remainder.  A second control
refuses a plain ring identity, where the relation would not be load-bearing.

OUTPUT LOCATION.  The emitted file is written into the zeta_zero_localization
island (`examples/zeta_zero_localization/lean/ExpLaurentDeficit.lean`), where its
consumer lives: `RecurrenceDeficit.lean` specializes the first row at d = 1/10 to
prove the MIRRORMERE node `MM_recurrence_deficit_eq_excess` against the island's
own `BraggDefect.excess`.  Same toolchain pin (v4.32.0), same lakefile (zzl_aux).

HONEST SCOPE: a dictionary row between two finite instruments, unconditional and
zeta-free.  Certifying one recurrence instance is not progress toward RH; the
UNIFORM Bagchi recurrence IS RH and is untouched here.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_exp_laurent_identity import (  # noqa: E402
    Y,
    Z,
    ExpLaurentIdentityEmitter,
    exp_laurent_certificate,
    exp_laurent_identity_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = (Path(__file__).resolve().parents[1]
        / "zeta_zero_localization" / "lean" / "ExpLaurentDeficit.lean")

# The two clearances of QC_RECURRENCE row (a), in the exp generators.
_G_PLUS = Y - 1        # outer mirror factor   e^d - 1
_G_MINUS = 1 - Z       # inner factor          1 - e^(-d)
_EXCESS = Y + Z - 2    # Bragg amplification excess

# Row index -> (Lean theorem name, lhs, rhs).  The grid axis is the integer index
# (GridSpec axes are integer-valued); the displacement binder is the Lean name `d`.
_ROWS = (
    ("expLaurent_recurrence_deficit", _G_PLUS * _G_MINUS, _EXCESS),
    ("expLaurent_recurrence_deficit_sq", (_G_PLUS * _G_MINUS) ** 2, _EXCESS ** 2),
)
_VAR = "d"

_PRELUDE = """-- THE EXP-LAURENT DEFICIT ROWS (QC_RECURRENCE section 2 row (a), section 4 item 2).
--
-- For an off-line pair at displacement d, the two one-sided clearances are the outer mirror
-- factor e^d - 1 and the inner transported-zero factor 1 - e^(-d).  Their PRODUCT -- the
-- two-sided clearance a recurrence shift must bridge -- is the RECURRENCE DEFICIT, and it
-- equals the Bragg amplification EXCESS e^d + e^(-d) - 2.  The square is the Weil-energy
-- (quadratic-form) reading of the same row.
--
-- Certificate: an exact reduction of lhs - rhs modulo the single relation e^d * e^(-d) = 1,
-- with the quotient (cofactor) carried into `linear_combination`.  Corrupt the cofactor or
-- either side and the kernel rejects the theorem.
--
-- HONEST SCOPE: unconditional, zeta-free bookkeeping between two finite instruments.  It is
-- a dictionary row, not an analytic theorem, and NOT a step toward RH (the uniform Bagchi
-- recurrence IS RH and is untouched).  conjecture1_proved = False."""


def _negative_controls() -> None:
    """Layer-1 refusals that must fire before anything is emitted.

    (1) The memo's own corrected mistake: the SUM of the clearances is not the
        excess (remainder 2 - 2*e^(-d) != 0).
    (2) A plain ring identity, where the relation e^d * e^(-d) = 1 carries no
        information (cofactor 0) -- that shape belongs to IdentityEmitter.
    """
    controls = (
        ("sum_not_product", _G_PLUS + _G_MINUS, _EXCESS,
         "the SUM of the two clearances (QC_RECURRENCE section 6's corrected mistake)"),
        ("relation_not_load_bearing", (Y - 1) * (Y + 1), Y ** 2 - 1,
         "a plain ring identity (cofactor 0)"),
    )
    for name, lhs, rhs, why in controls:
        try:
            exp_laurent_certificate(lhs, rhs, name=name)
        except ValueError:
            continue
        raise AssertionError(
            f"exp_laurent_identity negative control FAILED: accepted {why}")
    print("exp_laurent_identity: OK (product row accepted; the SUM form and the "
          "cofactor-0 ring identity are refused)")


def build() -> str:
    fam = exp_laurent_identity_family(
        "ExpLaurentDeficit",
        GridSpec([("row", range(len(_ROWS)))]),
        lambda pt: _ROWS[pt["row"]][0],
        spec=lambda pt: (_ROWS[pt["row"]][1], _ROWS[pt["row"]][2], _VAR),
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("ExpLaurentDeficit",), prelude=_PRELUDE),
        [ExpLaurentIdentityEmitter()],
        ValidationReport(checks=(("exp_laurent_identity", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    _negative_controls()
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: ExpLaurentDeficit.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(parents=True, exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="Emit the exp-Laurent recurrence-deficit rows onto the "
                    "zeta_zero_localization island.")
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
