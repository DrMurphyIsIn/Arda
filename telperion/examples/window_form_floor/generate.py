"""Generate the window-form-floor example: certify -> emit -> write INTO the Weil island.

    python examples/window_form_floor/generate.py           # write the island lib
    python examples/window_form_floor/generate.py --check    # drift check (no write)

Zhu, arXiv:2608.24827 Theorem 1.1 (the one-stroke window reduction) and Theorem 1.2 (its certified
execution at `L = 0.8`, support `1.6`).  The emitted Lean is stated in the `WindowFloor` predicate
over the registry's E8 vocabulary (`WeilExplicit` / `WeilForm`), which lives in `WeilFormDefs.lean`
inside the `weil_form_enclosure` island.  Rather than a fragile cross-package `require`, we follow
the recipe's honest fallback used by `bragg_amplitude`: the emitted instances are written as a NEW
lib inside that island (`WindowFormFloorInstances.lean`, registered in its lakefile), and the
`window-form-floor-compiles` CI job builds that lib in the island, which already carries the
Mathlib v4.32.0 olean cache.

Two instances, which are Zhu's own certified run and its independent cross-check (Section 5.5a):

  * `zhu_window_floor_L08_T200` -- `T# = 200`, `beta* = 0.5134667`, `lam0 = 9e-18`,
    `eps_D = eps_B = 1e-100`, `N = 200`.  Published floor `8.9e-18`, i.e. Theorem 1.2.
  * `zhu_window_floor_L08_T150` -- the independent second certification at `T# = 200 -> 150`,
    `beta* = 0.2241180`, `lam0 = 1.2e-18`.  Published floor `1.1e-18`, rounded DOWN from the raw
    `1.2e-18 - 1e-100` -- the emitter refuses `1.2e-18` itself, since that is not below the raw
    floor.  Zhu's Section 5.5(b) monotonicity check is visible here as the two published floors
    ordering with `T#`.

Every finite constant is RE-DERIVED by the emitter and refused if it disagrees (the retraction
guard).  `lam0`, `eps_D`, `eps_B` are the paper's multiprecision outputs and are the documented
NON-KERNEL trust seam; the kernel proves only that the published rounding is sound.

No RH progress.  PRE-WALL.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_window_form_floor import (  # noqa: E402
    WindowFormFloorData,
    WindowFormFloorEmitter,
    window_form_floor_family,
    window_form_floor_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_L08 = sp.Rational(4, 5)
_A_L08 = sp.Rational("2.9419735")        # Zhu Section 5.1; re-derived by the emitter

_SPECS = {
    200: dict(
        t_sharp=sp.Integer(200),
        beta_star=sp.Rational("0.5134667"),
        lam0=sp.Rational("9e-18"),
        published_floor=sp.Rational("8.9e-18"),
        label="zhu_thm12_L08_T200",
    ),
    150: dict(
        t_sharp=sp.Integer(150),
        beta_star=sp.Rational("0.2241180"),
        lam0=sp.Rational("1.2e-18"),
        published_floor=sp.Rational("1.1e-18"),
        label="zhu_sec55a_L08_T150",
    ),
}
_NAMES = {200: "zhu_window_floor_L08_T200", 150: "zhu_window_floor_L08_T150"}

_ISLAND = Path(__file__).resolve().parents[1] / "weil_form_enclosure" / "lean"
_OUT = _ISLAND / "WindowFormFloorInstances.lean"


def _spec(pt):
    s = _SPECS[pt["tsharp"]]
    return WindowFormFloorData(
        L=_L08,
        comb_mass=_A_L08,
        eps_d=sp.Rational("1e-100"),
        eps_b=sp.Rational("1e-100"),
        n_modes=200,
        **s,
    )


def build() -> str:
    fam = window_form_floor_family(
        "WindowFormFloorInstances",
        GridSpec([("tsharp", [150, 200])]),
        lambda pt: _NAMES[pt["tsharp"]],
        spec=_spec,
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("WindowFormFloorInstances",),
            imports=("WeilFormDefs",),
            prelude=window_form_floor_prelude_lean(),
        ),
        [WindowFormFloorEmitter()],
        ValidationReport(checks=(("window_form_floor", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: WindowFormFloorInstances.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
