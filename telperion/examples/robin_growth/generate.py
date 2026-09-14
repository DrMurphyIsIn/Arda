"""Generate the Robin-growth ladder — Face 2 (temperedness) of the RH obstruction.

    python examples/robin_growth/generate.py           # write lean/RobinGrowth.lean
    python examples/robin_growth/generate.py --check    # drift check (no write)

Robin's theorem (1984): RH ⟺  σ(n) < e^γ · n · log log n  for every integer
n > 5040.  Per rung n the emitter proves ``(σ(n) : ℝ) < R`` where R is the
transcendental Robin RHS carried as the hypothesis ``hR : Llo ≤ R``; ``Llo`` is
a rigorous rational lower bound from flint/Arb ball arithmetic
(``robin_rhs_lower_bound``), self-checked to lie strictly above the exact
divisor sum σ(n) before any box is handed out.  The file also carries
``robin_neg_refutes``, the falsifiability face.

Rungs chosen at colossally-abundant / superabundant n just above 5040, where the
Robin margin is thin — the honest place to certify.  Lower bounds are rounded
DOWN to 12 significant decimals (still rigorous, and still above σ(n)) so the
Lean literals stay readable.

HONEST SCOPE: each rung is a finite NECESSARY-condition check; the uniform
"∀ n > 5040" IS RH and nothing here approaches it.  The enclosure hypotheses
``hR`` are the documented Arb trust seam.  conjecture1_proved = False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_robin_growth import (  # noqa: E402
    RobinGrowthEmitter,
    robin_growth_family,
    robin_refutation_atom_lean,
    robin_rhs_lower_bound,
    sigma_exact,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# Colossally/superabundant n just above the Robin threshold 5040 (thin margin).
RUNGS = [5041, 5042, 5044, 5045, 10080, 15120, 25200, 55440]
PREC_BITS = 256
_OUT = Path(__file__).resolve().parent / "lean" / "RobinGrowth.lean"


def _round_down_12sig(x: Fraction) -> Fraction:
    """Largest 12-significant-decimal fraction <= x (x > 0). Still a rigorous
    lower bound; keeps the emitted literal short."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**11:
        exp += 1
    num = (x.numerator * 10**exp) // x.denominator  # floor
    return Fraction(num, 10**exp)


def build() -> str:
    specs = {}
    for n in RUNGS:
        lo_full = robin_rhs_lower_bound(n, prec_bits=PREC_BITS)  # rigorous Arb lower bound
        lo = _round_down_12sig(lo_full)
        sig = sigma_exact(n)
        assert Fraction(sig) < lo, (
            f"rung {n}: rounded lower bound {float(lo)} not above σ({n})={sig}")
        specs[n] = {"n": n, "Llo": lo}

    fam = robin_growth_family(
        "RobinGrowth",
        GridSpec([("n", RUNGS)]),
        lambda pt: f"robin_n{pt['n']}",
        spec=lambda pt: specs[pt["n"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("RobinGrowth",),
            prelude=robin_refutation_atom_lean(),
        ),
        [RobinGrowthEmitter()],
        ValidationReport(checks=(("robin_growth", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: RobinGrowth.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(RUNGS)} rungs + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
