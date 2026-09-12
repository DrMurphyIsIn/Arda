"""Generate the Route-P Bragg-floor diffraction ladder: enclose -> certify -> emit -> write.

    python examples/li_positivity/generate_bragg_floor.py           # write lean/BraggFloor.lean
    python examples/li_positivity/generate_bragg_floor.py --check    # drift check (no write)

Route P Brick D3 part 2 (the Dyson-quasicrystal diffraction certificate).  Per order `n` the emitter
proves the FINITE rational inequality

    floor(n)  ≤  braggLo − tailHi,

i.e. the truncated log-prime (von Mangoldt / Bragg) amplitude at base point `s0 > 1`, over prime
powers `p^k ≤ CUTOFF`, net of a certified tail, clears the explicit archimedean floor
`-(1 + Re taylorCoeff Γℝ n)` (the polygamma-at-½ capstone).  The three literals are Arb ball
enclosures (`telperion.bragg_coeff`), self-checked against the archimedean trend and the small-prime
von Mangoldt anchors before any box is emitted.  The file also carries
`bragg_below_floor_refutes_rh`, the falsifiability face, which fires `companion_below_floor_refutes_rh`
THROUGH the conditional `taylorCoeff_companion_bragg_of_exhaustion_limits` seam (an explicit,
undischarged, RH-hard hypothesis).

HONEST SCOPE.  The rungs are a FINITE necessary-condition check (category-b); the passage to the
companion coefficient at the Li base point is RH-hard and is NOT crossed.  Because the amplitude is
taken at a fixed `s0` (the order-0 datum), only the `n` whose floor it clears are emitted — the
fixed-`s0` truncation does not dominate the mid-range floors `n ∈ {1,…,5}`, for which
`bragg_floor_certificate` honestly refuses.  The emitted orders are n = 0 and n = 6..19.  The Arb
enclosures are the documented trust seam.  conjecture1_proved = False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.bragg_coeff import (  # noqa: E402
    BASE_S0,
    BraggFloorData,
    enclose_arch_floors,
    enclose_bragg_truncation,
)
from telperion.emit_bragg_floor import (  # noqa: E402
    BraggFloorEmitter,
    bragg_below_floor_refutes_rh_lean,
    bragg_floor_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

N_RUNGS = 20                 # orders 0..19 (the Li-ladder span); refused mid-range orders are skipped
CUTOFF = 5000                # prime-power truncation of the Bragg comb
PREC_BITS = 192
_SIG = 12                    # decimal significant figures for the emitted literals
_OUT = Path(__file__).resolve().parent / "lean" / "BraggFloor.lean"


def _round_sig(x: Fraction, *, down: bool) -> Fraction:
    """Nearest `_SIG`-significant-figure fraction on the given side of `x` (down => ≤ x, up => ≥ x).
    A directed round keeps the emitted literal short while preserving the inequality: rounding
    `braggLo` DOWN and `tailHi`/`floorHi` UP only ever makes `floorHi ≤ braggLo − tailHi` harder, so
    a survivor is still rigorous."""
    if x == 0:
        return Fraction(0)
    neg = x < 0
    ax = -x if neg else x
    exp = 0
    while ax * 10**exp < 10**(_SIG - 1):
        exp += 1
    scaled = ax * 10**exp
    # floor of the positive magnitude
    fl = Fraction(scaled.numerator // scaled.denominator, 1)
    base = fl / 10**exp
    # magnitude rounds toward +inf or -inf; compose with the sign to honor `down`.
    if neg:
        # x = -ax; rounding x DOWN means magnitude UP; x UP means magnitude DOWN.
        mag = base if not down else (base + Fraction(1, 10**exp) if base != ax else base)
        return -mag
    mag = base if down else (base + Fraction(1, 10**exp) if base != ax else base)
    return mag


def build() -> str:
    floors = enclose_arch_floors(N_RUNGS, prec_bits=PREC_BITS)          # self-checked inside
    bragg_lo, _bragg_hi, tail_hi = enclose_bragg_truncation(            # self-checked inside
        CUTOFF, prec_bits=PREC_BITS, s0=BASE_S0)

    # Directed rounding: braggLo down, tailHi up, floorHi up — each preserves the certified inequality.
    blo = _round_sig(bragg_lo, down=True)
    thi = _round_sig(tail_hi, down=False)

    emit_ns: list[int] = []
    data_by_n: dict[int, BraggFloorData] = {}
    for n in range(N_RUNGS):
        _flo_lo, flo_hi = floors[n]
        flo = _round_sig(flo_hi, down=False)
        # keep only orders whose rounded inequality genuinely holds (honest refusal otherwise)
        if flo <= blo - thi:
            emit_ns.append(n)
            data_by_n[n] = BraggFloorData(
                n=n, s0=BASE_S0, cutoff=CUTOFF,
                bragg_lo=blo, tail_hi=thi, floor_hi=flo,
            )
    if not emit_ns:
        raise RuntimeError("no Bragg rung cleared its floor after rounding — raise CUTOFF/PREC_BITS")

    fam = bragg_floor_family(
        "BraggFloor",
        GridSpec([("n", emit_ns)]),
        lambda pt: f"bragg_rung_{pt['n']}",
        spec=lambda pt: data_by_n[pt["n"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("BraggFloor",),
            imports=("RvMRoutePFalsify", "RvMCompanionPrime", "RvMCompanionBraggLimit"),
            prelude=(
                "open Complex\n\n"
                "open RvMWeierstrass in\n"
                + bragg_below_floor_refutes_rh_lean()
            ),
        ),
        [BraggFloorEmitter()],
        ValidationReport(checks=(("bragg_floor", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BraggFloor.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} (Bragg rungs + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
