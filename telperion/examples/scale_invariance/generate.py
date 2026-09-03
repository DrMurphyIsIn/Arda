"""Scale-invariance / objective-degeneracy certificates, compile-gated.

A homogeneity / parameter-cancellation certificate: a rational objective is
INVARIANT under scaling a parameter, or a parameter cancels entirely.

MOTIVATING STRUCTURE — the Arda trading system's leverage↔position_size
degeneracy in the Sharpe objective, read off the live formula in
``src/arda/acceleration/rust_core.py`` (~L1250–1318,
``trade_returns = trades / (initial_capital * position_size * leverage)``;
``sharpe = mean/std * sqrt(...)``) and its Rust twin
``arda_rust/src/backtesting.rs`` (``compute_weighted_sharpe``, ~L317–330).
Per-trade ``pnl = Δprice·direction·pos_size`` with ``pos_size = capital·s·L/price``
and fees ``∝ notional = capital·s·L``, so ``trade_return = (pnl−fee)/(capital·s·L)``.

Two shipped demonstrations:
  (i)  CANCELLATION — the trade return is INDEPENDENT of position_size ``s``
       (``s`` sits in both the pnl/fee numerator and the denominator).
  (ii) HOMOGENEITY — the squared Sharpe ``mean²·n/variance`` (n = 3 trades) is
       degree-0 homogeneous, hence INVARIANT under scaling the returns by the
       leverage factor ``lam`` (scaling ``L`` scales every ``trade_return`` by
       ``1/L``; the Sharpe numerator and denominator scale identically).

This is the algebraic root of CLAUDE.md's rule that ``leverage`` must NOT be an
evolvable gene: it is mathematically degenerate with ``position_size`` in the
Sharpe objective.

NEGATIVE CONTROLS: an objective that genuinely DEPENDS on the parameter is
refused (cancellation); an objective that is not degree-0 homogeneous is refused.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_scale_invariance import (  # noqa: E402
    ScaleInvarianceEmitter,
    scale_invariance_certificate,
    scale_invariance_family,
)

HERE = Path(__file__).resolve().parent

# --- symbols --------------------------------------------------------------- #
capital, s, s2, L, dprice, direction, fee, price = sp.symbols(
    "capital s s2 L dprice direction fee price", positive=True
)
r1, r2, r3, lam = sp.symbols("r1 r2 r3 lam", real=True)


def _cancellation_spec():
    """trade_return is independent of position_size s (fact 1)."""
    pos_size = capital * s * L / price
    pnl = dprice * direction * pos_size
    fee_amt = capital * s * L * fee
    trade_return = (pnl - fee_amt) / (capital * s * L)
    return {
        "objective": trade_return,
        "mode": "cancellation",
        "scale": s,
        "second": s2,
    }


def _homogeneity_spec():
    """Squared Sharpe (n=3) is degree-0 homogeneous under scaling returns (fact 2)."""
    n = 3
    mean = (r1 + r2 + r3) / n
    variance = ((r1 - mean) ** 2 + (r2 - mean) ** 2 + (r3 - mean) ** 2) / n
    sharpe_sq = mean ** 2 * n / variance
    return {
        "objective": sharpe_sq,
        "mode": "homogeneity",
        "scale": lam,
        "args": [r1, r2, r3],
    }


_SPECS = {0: _cancellation_spec, 1: _homogeneity_spec}
_NAMES = {
    0: "si_return_indep_position_size",
    1: "si_sharpe_sq_leverage_invariant",
}


def _family():
    return scale_invariance_family(
        "ScaleInvariance",
        (),
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]](),
    )


def _validation() -> ValidationReport:
    def genuine_dependence_refused():
        a, b, p = sp.symbols("a b p", real=True)
        try:
            scale_invariance_certificate(a * p + b, mode="cancellation", scale=p)
            raise AssertionError("parameter-dependent objective not refused")
        except ValueError:
            pass

    def non_homogeneous_refused():
        try:
            scale_invariance_certificate(
                r1 + r2, mode="homogeneity", scale=lam, args=[r1, r2]
            )
            raise AssertionError("degree-1 objective not refused")
        except ValueError:
            pass

    return ValidationReport.from_asserts([
        ("cancellation_discriminates", genuine_dependence_refused),
        ("homogeneity_discriminates", non_homogeneous_refused),
    ])


def build():
    return emit(
        certify(_family()),
        LeanProfile(
            namespace=("ScaleInvariance",),
            # `field_simp` alone closes these particular instances, leaving the
            # `all_goals ring` fallback unexecuted; the ≠-0 side conditions
            # document the objective's domain even when field_simp does not need
            # every one.  Silence the resulting cosmetic linters (build is green).
            options=(
                "set_option linter.unreachableTactic false",
                "set_option linter.unusedTactic false",
                "set_option linter.unusedVariables false",
            ),
        ),
        [ScaleInvarianceEmitter()],
        _validation(),
        file_name="ScaleInvariance.lean",
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    a = ap.parse_args()
    res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"ScaleInvariance: {res.n_theorems} certs, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
