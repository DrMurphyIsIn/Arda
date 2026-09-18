"""Generate the Weil-form-enclosure example: certify -> emit -> write.

    python examples/weil_form_enclosure/generate.py            # write lean/WeilFormEnclosure.lean
    python examples/weil_form_enclosure/generate.py --check    # drift check (no write)

WHAT THIS IS.  The finite value certificate that the MIRRORMERE W3c membership goal
(`MM_zeta_comb_membership`, design memo
telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md) reads back: a rigorous
two-sided rational enclosure of

    W(g) = Re (WeilExplicit.weilForm (WeilExplicit.autocorr g))
         = Re (archSide (g * g~) - primeSide (g * g~))

at explicit Gaussian test functions, produced by the Arb backend `telperion.weil_gauss`
(closed forms anchored against the DEFINING integrals of `autocorr` / `weilKernel`, prime side
truncated with an elementary tail bound, archimedean integral by rigorous acb_calc quadrature
with an explicit Gaussian tail bound).

WHAT IT IS NOT.  It is not progress on RH and not an instance of the goal's quantifier.  The
goal quantifies over the whole test class and is RH-EQUIVALENT (Weil 1952; Bombieri 2000); no
finite family of test functions approaches that quantifier (RH_ROUTES_ROADMAP section 1).  The
Gaussians used here are in the Guinand class, not in `IsWeilTest` (they are not compactly
supported); they are used because every term is closed-form, so the certificate tests the
NORMALISATION of the registry vocabulary rather than a quadrature.

THE PARAMETERS.  `g(u) = exp(-(u-c)^2/(2a^2)) e^{i omega u}`; the autocorrelation's transform on
the critical line is `h_f(r) = 2 pi a^2 exp(-a^2 (r + omega)^2) = |h_g(r)|^2`, a bump centred at
`r = -omega`, so `-omega` selects which part of the zero comb the Weil form weighs:

  * `omega = -14.1347` centres it on the first zeta ordinate: W ~ 1.5708 ~ 2 pi a^2 -- the
    instrument is literally reading the first Bragg peak of the zero comb;
  * `omega = -21.02` centres it on the second;
  * `omega = -0.3` (off the comb) gives W ~ 0 to 1e-13 -- the enclosure then STRADDLES zero and
    `weil_form_certificate` REFUSES it.  That refusal is recorded here, not hidden: it is the
    honest statement that the sign is undecided at this precision, and it is itself the
    strongest evidence that the certificate is measuring the zeros and not an artefact.

conjecture1_proved = False.
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec, LeanProfile, ValidationReport, WeilFormEnclosureEmitter, certify, emit,
    weil_form_family, weil_form_membership_face_lean, weil_form_neg_refutes_rh_lean,
)
from telperion.emit_weil_form_enclosure import WeilFormData  # noqa: E402

_HERE = Path(__file__).resolve().parent
_OUT = _HERE / "lean" / "WeilFormEnclosure.lean"

# (lean name, label, a, omega, rounded enclosure lo/hi, zero-side reading lo/hi, note)
# The enclosures are the OUTWARD-rounded output of
#   telperion.weil_gauss.enclose_weil_gauss(WeilGaussParams(a, omega, c=1/5, cutoff=2000))
# and the zero-side readings are the independent sum over the first 40 zero pairs (mpmath,
# 25 digits) of 2 pi a^2 (e^{-a^2 (gamma+omega)^2} + e^{-a^2 (-gamma+omega)^2}).  Regenerating
# them is the job of `refresh.py`-style reruns; they are frozen here so `--check` is a pure
# drift gate (no flint required to run the check).
_INSTANCES = [
    ("weil_form_zero1",
     "gaussian a=1/2, omega=-14.1347 (centred on the first zeta ordinate)",
     Fraction(1, 2), Fraction(-141347, 10000),
     Fraction("1.5708074408"), Fraction("1.5708074409"),
     Fraction("1.5708074408"), Fraction("1.5708074409"),
     "zero-side sum over the first 40 zero pairs = 1.5708074408343442739"),
    ("weil_form_zero2",
     "gaussian a=1/2, omega=-21.02 (centred on the second zeta ordinate)",
     Fraction(1, 2), Fraction(-1051, 50),
     Fraction("1.6001063093"), Fraction("1.6001063094"),
     Fraction("1.6001063093"), Fraction("1.6001063094"),
     "zero-side sum over the first 40 zero pairs = 1.6001063093683198989"),
]

# The refused instance, kept as documentation of the honest refusal (see the module docstring).
_REFUSED = [
    ("gaussian a=1/2, omega=-3/10 (off the zero comb)",
     Fraction("-5.1e-13"), Fraction("5.1e-13"),
     "enclosure straddles zero: sign of the Weil form UNDECIDED at this precision -- refused"),
]


def build() -> str:
    data = {
        i: WeilFormData(label=lbl, lo=lo, hi=hi, zero_side_lo=zlo, zero_side_hi=zhi, note=note)
        for i, (_nm, lbl, _a, _om, lo, hi, zlo, zhi, note) in enumerate(_INSTANCES)
    }
    names = {i: nm for i, (nm, *_rest) in enumerate(_INSTANCES)}
    fam = weil_form_family(
        "WeilFormEnclosure",
        GridSpec([("case", sorted(data))]),
        lambda pt: names[pt["case"]],
        spec=lambda pt: data[pt["case"]],
    )
    refused = "".join(
        f"--   REFUSED: {lbl} -- enclosure [{lo}, {hi}]: {why}\n"
        for lbl, lo, hi, why in _REFUSED
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("WeilFormEnclosure",),
            prelude=(
                "-- Instances the certificate REFUSED (recorded, not hidden):\n"
                + refused
                + "\n"
                + weil_form_neg_refutes_rh_lean()
                + "\n"
                + weil_form_membership_face_lean()
            ),
        ),
        [WeilFormEnclosureEmitter()],
        ValidationReport(checks=(("weil_form_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: WeilFormEnclosure.lean does not match regeneration")
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
