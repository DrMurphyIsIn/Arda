"""Negative-control adapter for WeilFormEnclosureEmitter (MIRRORMERE W3c value certificate).

The emitted theorem is the rational implication `lo <= W -> W <= hi -> 0 < W and W <= hi`; its
load-bearing content is the single literal comparison `0 < lo`, discharged by `norm_num`.  If the
certificate's own bookkeeping is corrupted so that the sign claim is FALSE for the emitted
literals, `norm_num` fails and the TRUSTED Lean kernel rejects the proof.

FALSE forgery: a `sign = "pos"` cert whose lower bound is NEGATIVE (`lo = -1/2`, `hi = 2`).  Layer 1
(`weil_form_certificate`) refuses that enclosure outright -- it straddles zero, so the sign is
undecided -- so the adapter mints the frozen dataclass BY HAND to bypass the guard and let the
kernel be the arbiter: `norm_num : (0 : R) < -1/2` fails and the theorem is rejected.

TRUE twin: the real certified instance of this family -- the Gaussian test function of width
a = 1/2 modulated to the first zeta ordinate (omega = -14.1347), whose Weil form is enclosed in
[1.5708074408, 1.5708074409] and independently matches the zero-side sum over the first 40 zero
pairs to 18 digits.  Both twins are pure `(. : R)` rational implications, so the control
elaborates against plain Mathlib with no registry vocabulary.

conjecture1_proved = False.
"""
from __future__ import annotations

import sympy as sp

from telperion.emit_weil_form_enclosure import WeilFormCert, WeilFormEnclosureEmitter
from telperion.negative_control_harness import (
    NegativeControlAdapter,
    emit_via_single_instance_family,
    register,
)


def make_false_cert():
    """Hand-forged FALSE cert: sign 'pos' with a NEGATIVE lower bound (weil_form_certificate
    would refuse this enclosure as straddling zero)."""
    return WeilFormCert(
        label="forged: straddling enclosure labelled positive",
        lo=sp.Rational(-1, 2), hi=sp.Rational(2, 1), sign="pos",
    )


def make_true_cert():
    """Paired TRUE twin: the certified Gaussian instance at the first zeta ordinate."""
    return WeilFormCert(
        label="gaussian a=1/2 omega=-14.1347 (first zeta ordinate)",
        lo=sp.Rational("1.5708074408"), hi=sp.Rational("1.5708074409"), sign="pos",
        note="matches the independent zero-side sum to 18 digits",
    )


def _emit(cert, name: str) -> str:
    return emit_via_single_instance_family(
        WeilFormEnclosureEmitter(),
        lean_name=name,
        instance_kwargs={"payload": cert},
    )


register(
    NegativeControlAdapter(
        emitter_name="WeilFormEnclosureEmitter",
        make_false_cert=make_false_cert,
        make_true_cert=make_true_cert,
        emit_call=_emit,
        prelude="",
        allow_axioms=(),
        label=(
            "forged Weil-form cert labelled positive with lo = -1/2: the norm_num side goal "
            "0 < -1/2 is false, kernel rejects; true twin (the a=1/2 Gaussian at the first zeta "
            "ordinate, W in [1.5708074408, 1.5708074409]) compiles"
        ),
        imports_line="import Mathlib",
    )
)
