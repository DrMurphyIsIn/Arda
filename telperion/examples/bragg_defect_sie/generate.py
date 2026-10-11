"""Discharge the BraggDefect Arb seam ``hexp`` with the scaled_interval_eval emitter.

    python examples/bragg_defect_sie/generate.py           # write the two island files
    python examples/bragg_defect_sie/generate.py --check   # drift check (no write)

Emits INTO the zeta_zero_localization island (``lean/``), the way ``exp_enclosure`` and
``exp_laurent_deficit`` do:

  * ``ScaledInterval.lean`` -- a COPY of the scaled_interval_eval prelude.  The single source
    of truth is the Python string :func:`telperion.scaled_interval_prelude_lean`; this script
    and ``examples/scaled_interval_eval/generate.py`` both write it from that string and both
    ``--check`` it byte-for-byte, so neither copy can drift.  (A copy rather than a
    ``[[require]]``: the island is sharded into path packages that share one deps dir in CI,
    and the RHLinalg prelude is reused the same way, as a byte-identical copy.)
  * ``BraggDefectSIE.lean`` -- two emitted instances at scale ``S = 10^40``:

      - ``sie_defect_offline`` -- ``L <= -(exp(1/10) + exp(-1/10) - 2)^2 <= U`` where ``L`` and
        ``U`` are the off-line bracket of ``BraggDefect.defect_witness_offline``, READ VERBATIM
        out of BraggDefect.lean at generation time (so driver drift breaks ``--check`` here);
      - ``sie_exp_tenth`` -- ``expLo <= exp(1/10) <= expHi`` with BraggDefect's own literals,
        read the same way.

``BraggDefect.lean`` (driver ``examples/zeta_zero_localization/bragg_defect.py``) imports
``BraggDefectSIE`` and states the hypothesis-free theorems ``defect_witness_offline_sie``,
``bragg_defect_witness_sie``, ``defect_leakage_gap_sie`` and ``hexp_sie`` next to the
``hexp``-taking originals.  ``--check`` also re-runs that driver's own drift check.

Every box is recomputed by the kernel (``decide +kernel``); nothing numeric is trusted from
Python.  conjecture1_proved = False -- one synthetic off-line pair's defect bracket; nothing
about RH.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import (  # noqa: E402
    ScaledIntervalEvalEmitter, ValidationReport, certify, emit,
    scaled_interval_eval_certificate, scaled_interval_eval_family,
    scaled_interval_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_ZZL = Path(__file__).resolve().parents[1] / "zeta_zero_localization"
_ISLAND = _ZZL / "lean"
_PRELUDE_OUT = _ISLAND / "ScaledInterval.lean"
_OUT = _ISLAND / "BraggDefectSIE.lean"
_BRAGG_DEFECT = _ISLAND / "BraggDefect.lean"
_DRIVER = _ZZL / "bragg_defect.py"

SCALE = 10 ** 40
_R = sp.Rational


def _theorem_statement(src: str, name: str) -> str:
    """The statement text of ``theorem <name>`` (from its name to the first ``:= by``)."""
    start = src.index(f"theorem {name}\n")
    return src[start:src.index(":= by", start)]


def island_offline_bracket() -> tuple[sp.Rational, sp.Rational]:
    """``(L, U)`` of ``BraggDefect.defect_witness_offline``, read verbatim from the island."""
    stmt = _theorem_statement(_BRAGG_DEFECT.read_text(encoding="utf-8"), "defect_witness_offline")
    hits = re.findall(r"\(-(\d+) / (\d+) : ℝ\)", stmt)
    if len(hits) != 2:
        raise SystemExit(f"DRIFT: defect_witness_offline no longer carries exactly two negative "
                         f"rational literals (found {len(hits)})")
    lo, hi = (-_R(int(p), int(q)) for p, q in hits)
    if not lo < hi < 0:
        raise SystemExit(f"DRIFT: off-line bracket is not L < U < 0: {lo}, {hi}")
    return lo, hi


def island_exp_bracket() -> tuple[sp.Rational, sp.Rational]:
    """``(expLo, expHi)`` of BraggDefect, read verbatim from their ``def`` lines."""
    src = _BRAGG_DEFECT.read_text(encoding="utf-8")
    out = []
    for name in ("expLo", "expHi"):
        hits = re.findall(rf"noncomputable def {name} : ℝ := \((\d+) / (\d+) : ℝ\)", src)
        if len(hits) != 1:
            raise SystemExit(f"DRIFT: expected exactly one `def {name}` literal, found {len(hits)}")
        out.append(_R(int(hits[0][0]), int(hits[0][1])))
    return out[0], out[1]


def specs() -> dict:
    off_lo, off_hi = island_offline_bracket()
    exp_lo, exp_hi = island_exp_bracket()
    t = _R(1, 10)
    return {
        0: ("sie_defect_offline",
            dict(expr=-(sp.exp(t) + sp.exp(-t) - 2) ** 2, lo=off_lo, hi=off_hi, scale=SCALE)),
        1: ("sie_exp_tenth", dict(expr=sp.exp(t), lo=exp_lo, hi=exp_hi, scale=SCALE)),
    }


def build() -> str:
    sp_ = specs()
    fam = scaled_interval_eval_family(
        "BraggDefectSIE",
        GridSpec([("case", sorted(sp_))]),
        lambda pt: sp_[pt["case"]][0],
        spec=lambda pt: dict(sp_[pt["case"]][1]),
    )
    checks = []
    for case in sorted(sp_):
        name, spec = sp_[case]
        spec = dict(spec)
        cert = scaled_interval_eval_certificate(spec.pop("expr"), **spec)
        lo, hi = cert.nodes[cert.root].box
        checks.append((f"root_box_ordered_{name}", lo <= hi))
        checks.append((f"claim_contains_box_{name}",
                       cert.claim_lo * cert.scale <= lo and hi <= cert.claim_hi * cert.scale))
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BraggDefectSIE",), imports=("ScaledInterval",)),
        [ScaledIntervalEvalEmitter()],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def _driver():
    spec = importlib.util.spec_from_file_location("zzl_bragg_defect", _DRIVER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main(*, check: bool = False) -> int:
    text = build()
    prelude = scaled_interval_prelude_lean()
    if check:
        bad = []
        if not _PRELUDE_OUT.exists() or _PRELUDE_OUT.read_text(encoding="utf-8") != prelude:
            bad.append("ScaledInterval.lean")
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            bad.append("BraggDefectSIE.lean")
        if _driver().render() != _BRAGG_DEFECT.read_text(encoding="utf-8"):
            bad.append("BraggDefect.lean (driver bragg_defect.py)")
        if bad:
            print(f"DRIFT: {', '.join(bad)} do(es) not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _PRELUDE_OUT.write_text(prelude, encoding="utf-8")
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_PRELUDE_OUT} ({len(prelude)} bytes) and {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
