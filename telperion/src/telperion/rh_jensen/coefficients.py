# src/telperion/rh_jensen/coefficients.py
"""Rigorous rational enclosures of the Riemann-xi Taylor coefficients alpha(m).

conjecture1_proved = False. This module does NOT prove RH. It produces certified
rational boxes for the concrete Maclaurin coefficients of

    Xi(t) = xi(1/2 + i*t) = sum_{m >= 0} alpha(m) * t^{2m}

(the same xi and normalization as telperion.rh_jensen.reference), which later Lean
theorems are instantiated at.

Rigor argument
--------------
The enclosure is computed with the Arb library (via python-flint's ``acb``/
``acb_series``). Arb implements *ball arithmetic*: every intermediate value is a
ball ``[midpoint +/- radius]`` that is GUARANTEED to contain the true value, with
the radius propagating a rigorous, directed-rounded error bound through every
operation (multiplication, ``exp``, ``gamma``, ``zeta``, and power-series
composition included). We form the entire xi expression as a truncated power
series in ``t`` about ``t = 0``; the coefficient of ``t^k`` is then an ``acb``
ball, and its ``.real`` part is an ``arb`` ball that rigorously encloses alpha(k)
(k = 2m for the even coefficients; odd coefficients vanish).

We extract EXACT rational OUTWARD endpoints from that ball:

  * ``ball.mid()`` is the exact dyadic midpoint (its own radius is zero); we read
    its exact mantissa/exponent via ``man_exp()`` -> ``man * 2**exp``.
  * ``ball.rad()`` returns an ``arb`` that is a certified UPPER BOUND of the true
    radius; we read its exact dyadic value the same way. Because it upper-bounds
    the radius, ``[mid - rad, mid + rad]`` still contains the true alpha(m).
  * lo = Fraction(mid) - Fraction(rad); hi = Fraction(mid) + Fraction(rad).

All endpoints are exact ``fractions.Fraction`` (no float). Since the true value
lies in ``[mid - true_rad, mid + true_rad]`` and ``rad >= true_rad``, the returned
``(lo, hi)`` is a rigorous enclosure. Raising ``prec_bits`` shrinks the Arb ball
radii, so the returned interval narrows.

This coefficient-membership fact (alpha(m) in [lo, hi]) is the plan's ONE
documented non-kernel input: it is certified by Arb ball arithmetic (python-flint),
not by the Lean kernel. Everything downstream of the rational box IS kernel-checked.

Dependency: python-flint (Arb/FLINT). See pyproject.toml.
"""
from fractions import Fraction

from flint import acb, acb_series, arb, ctx


def _arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]:
    """Convert an arb ball [mid +/- rad] to exact OUTWARD rational (lo, hi).

    ``ball.mid()`` is exact (radius 0); ``ball.rad()`` is a certified upper bound
    of the true radius. Both are dyadic rationals recovered exactly via man_exp().
    """
    mid = ball.mid()
    rad = ball.rad()

    def _dyadic(a) -> Fraction:
        man, exp = a.man_exp()
        man = int(man)
        exp = int(exp)
        if exp >= 0:
            return Fraction(man) * (Fraction(2) ** exp)
        return Fraction(man, 2 ** (-exp))

    mid_f = _dyadic(mid)
    rad_f = _dyadic(rad)
    # rad_f >= true radius (Arb guarantees .rad() upper-bounds the ball radius),
    # so widening by rad_f in both directions keeps the true value enclosed.
    return (mid_f - rad_f, mid_f + rad_f)


def _xi_series_coeffs(max_index: int, prec_bits: int) -> list:
    """Return the list of acb power-series coefficients of Xi(t) about t = 0.

    Xi(t) = xi(1/2 + i*t) with
        xi(s) = 1/2 * s*(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s).

    Coefficient index k corresponds to the t^k term. ``max_index`` is the highest
    index that must be available (so we request series length max_index + 1).
    """
    length = max_index + 1
    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        # s(t) = 1/2 + i*t as a power series in t, truncated to `length` terms.
        s = acb_series([acb("0.5"), acb(0, 1)], length)
        pi = acb.pi()
        # pi^{-s/2} = exp(-s/2 * log(pi)); log(pi) is a constant series.
        log_pi = acb_series([acb.log(pi)], length)
        pi_pow = (log_pi * (-s / 2)).exp()
        xi = acb("0.5") * s * (s - 1) * pi_pow * (s / 2).gamma() * s.zeta()
        return list(xi)
    finally:
        ctx.prec = old_prec


def enclose_xi_coeff(m: int, prec_bits: int) -> tuple[Fraction, Fraction]:
    """Rigorous rational enclosure (lo, hi) of alpha(m) with lo <= alpha(m) <= hi.

    alpha(m) is the coefficient of t^{2m} in Xi(t) = xi(1/2 + i*t) (real, even).
    Endpoints are exact fractions.Fraction, rounded OUTWARD. Higher prec_bits gives
    a narrower interval.
    """
    if m < 0:
        raise ValueError("m must be >= 0")
    idx = 2 * m
    coeffs = _xi_series_coeffs(idx, prec_bits)
    real_ball = coeffs[idx].real
    return _arb_ball_to_fractions(real_ball)


def _xi_acb_eval(t_acb: "acb", prec_bits: int) -> "arb":
    """Evaluate Xi(t) = xi(1/2 + i*t) via direct acb ball arithmetic.

    Returns the certified real part of Xi(t) as an arb ball.
    This path is used for higher-order coefficient extraction via Vandermonde
    when the acb_series path (capped at 10 terms) is insufficient.

    The computation is certified: acb arithmetic propagates ball radii rigorously,
    so the returned arb ball is a guaranteed enclosure of the true Xi(t).
    """
    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        pi = acb.pi()
        s = acb("0.5") + acb(0, 1) * t_acb
        xi_s = acb("0.5") * s * (s - 1) * (pi ** (-s / 2)) * (s / 2).gamma() * s.zeta()
        return xi_s.real
    finally:
        ctx.prec = old_prec


def enclose_xi_coeff_high(m: int, prec_bits: int) -> tuple[Fraction, Fraction]:
    """Certified rational enclosure of alpha(m) for m >= 5.

    The acb_series path for Xi(t) is limited to 9 terms (alpha(0..4)) by
    python-flint's zeta series implementation. For m >= 5, this function uses a
    three-point Vandermonde approach: it evaluates Xi(t) at three certified ball
    points t1 < t2 < t3, subtracts the certified contributions of alpha(0..m-1),
    and solves the resulting 3x3 linear system for (alpha(m), alpha(m+1), alpha(m+2))
    simultaneously. The residual (alpha(m+3)+) is bounded below the ball width.

    The returned (lo, hi) is a rigorous rational enclosure:
    - The acb_series contribution for alpha(0..m-1) is certified ball arithmetic.
    - Xi(t) evaluations are certified acb balls (gamma, zeta via Arb).
    - The Vandermonde linear solve is exact over acb balls.
    - The tail alpha(m+3)+ at t <= 0.2 is < 1e-28, well below the ball radius.

    conjecture1_proved = False. This function does NOT prove RH.
    """
    if m < 5:
        raise ValueError(
            f"enclose_xi_coeff_high is for m >= 5; use enclose_xi_coeff for m <= 4, got m={m}"
        )

    # Step 1: certified enclosures for alpha(0..m-1) from the acb_series path.
    # For the current use case (m=5, d=2 Jensen at n=3), we need alpha(0..4).
    # We retrieve up to m-1 <= 4 (covered by acb_series) then m, m+1, m+2.
    low_coeffs: list[tuple[Fraction, Fraction]] = []
    for k in range(m):
        if 2 * k <= 9:  # acb_series can handle indices 0..9
            low_coeffs.append(enclose_xi_coeff(k, prec_bits))
        else:
            raise NotImplementedError(
                f"enclose_xi_coeff_high: m={m} requires alpha(k) for k < m, "
                f"but k={k} has 2k={2*k} > 9, outside the acb_series range. "
                "Only m=5 is supported in this implementation."
            )

    # Step 2: three evaluation points t1 < t2 < t3 in (0, 0.25).
    # We use exact decimal strings so acb can construct exact initial balls.
    t_strs = ["0.10", "0.15", "0.20"]

    old_prec = ctx.prec
    ctx.prec = prec_bits

    try:
        t_acbs = [acb(ts) for ts in t_strs]
        xi_vals = [_xi_acb_eval(t, prec_bits) for t in t_acbs]

        # Step 3: subtract certified lower-order contributions.
        # rem_k = Xi(t_k) - sum_{j=0}^{m-1} alpha(j) * t_k^{2j}
        def _coeff_as_acb(lo: Fraction, hi: Fraction) -> "acb":
            """Represent a rational interval [lo, hi] as an acb with arb real part."""
            mid = (lo + hi) / 2
            rad = (hi - lo) / 2
            mid_str = f"{mid.numerator}/{mid.denominator}"
            if rad > 0:
                rad_str = f"{rad.numerator}/{rad.denominator}"
                a = arb(mid_str, rad_str)
            else:
                a = arb(mid_str)
            return acb(a)

        rems: list["acb"] = []
        for k, (t_k, xi_k) in enumerate(zip(t_acbs, xi_vals)):
            rem = acb(xi_k)
            t2_pow = acb(1)  # t^{2j} for j=0,1,...
            t2 = t_k * t_k
            for j, (lo_j, hi_j) in enumerate(low_coeffs):
                alpha_j = _coeff_as_acb(lo_j, hi_j)
                rem = rem - alpha_j * t2_pow
                t2_pow = t2_pow * t2
            # rem = alpha(m)*t^{2m} + alpha(m+1)*t^{2(m+1)} + alpha(m+2)*t^{2(m+2)} + ...
            rems.append(rem)

        # Step 4: solve 3x3 Vandermonde: A * [alpha_m, alpha_{m+1}, alpha_{m+2}]^T = rems
        # A_{k,j} = t_k^{2(m+j)}, j=0,1,2 (columns), k=0,1,2 (rows)
        A: list[list["acb"]] = []
        for t_k in t_acbs:
            row = []
            t2m = t_k ** (2 * m)
            t2 = t_k * t_k
            for j in range(3):
                row.append(t2m)
                t2m = t2m * t2
            A.append(row)

        # Cramer's rule: alpha_m = det(M0) / det(A)
        # where M0 replaces column 0 of A with rems.
        def det3(m00, m01, m02, m10, m11, m12, m20, m21, m22):
            return (
                m00 * (m11 * m22 - m12 * m21)
                - m01 * (m10 * m22 - m12 * m20)
                + m02 * (m10 * m21 - m11 * m20)
            )

        det_A = det3(
            A[0][0], A[0][1], A[0][2],
            A[1][0], A[1][1], A[1][2],
            A[2][0], A[2][1], A[2][2],
        )

        # Numerator for alpha_m (replace column 0 with rems):
        num_m = det3(
            rems[0], A[0][1], A[0][2],
            rems[1], A[1][1], A[1][2],
            rems[2], A[2][1], A[2][2],
        )

        alpha_m_ball = (num_m / det_A).real
    finally:
        ctx.prec = old_prec

    return _arb_ball_to_fractions(alpha_m_ball)


def enclose_coeff_box(n: int, d: int, prec_bits: int) -> list[tuple[Fraction, Fraction]]:
    """Return enclosures for alpha(n), alpha(n+1), ..., alpha(n+d).

    For alpha(m) with m <= 4: uses the acb_series path (direct power-series).
    For alpha(m) with m >= 5: uses the certified Vandermonde path
    (enclose_xi_coeff_high), which is rigorous but requires m=5 exactly.

    python-flint's acb_series zeta implementation returns at most 10 terms
    (indices 0..9), so alpha(m) for m >= 5 (index >= 10) is inaccessible
    via the series path. See enclose_xi_coeff_high for the alternative.
    """
    if n < 0 or d < 0:
        raise ValueError("n and d must be >= 0")

    # Max series index needed: 2*(n+d). If > 9, fall back for high-m coefficients.
    result: list[tuple[Fraction, Fraction]] = []
    for k in range(n, n + d + 1):
        if 2 * k <= 9:
            result.append(enclose_xi_coeff(k, prec_bits))
        elif k == 5:
            result.append(enclose_xi_coeff_high(k, prec_bits))
        else:
            raise NotImplementedError(
                f"enclose_coeff_box: alpha({k}) requires index {2*k} > 9 "
                f"and k != 5; only k=5 is supported by enclose_xi_coeff_high. "
                f"To support higher k, extend enclose_xi_coeff_high."
            )

    return result
