"""Weil explicit-formula quadratic-form probe -- a validated numerical tool (2026-08-30).

WHAT IS ESTABLISHED (robust):
  * The Weil quadratic-form Gram kernel on a Gaussian-bump basis is implemented and VALIDATED to ~40
    digits: LHS (sum over the actual Riemann zeros, Sum_gamma |ghat(gamma)|^2) == RHS (poles + archimedean
    Gamma'/Gamma integral - prime sum -2 Sum Lambda(n)/sqrt(n) g(log n)).  See validate().
  * Diagonal dominance of the (pole-reduced) Weil Gram matrix FAILS and DIVERGES as the test cone grows
    (D ~ 1.8 -> 14.5 over cone L 1 -> 8): no finite diagonal-dominance certificate can capture Weil
    positivity -- the direct, measured analog of "the BG strong-spatial-mixing mechanism does not transfer
    to RH."  See diag_dominance().

WHAT WAS RETRACTED (honest record -- do not resurrect):
  * The pole-reduced smallest eigenvalue lam_min collapses super-exponentially as the cone grows, BUT this
    is a RESOLUTION ARTIFACT, not an RH-specific "tie": the collapse rate is entirely controlled by the bump
    width s (lam_min@N=16 swings 9e-8 .. 5e-20 .. 4e-49 for s = .08 .. .15 .. .25), and the reduced
    eigenvalues are just the zero-weights 4 pi s^2 exp(-s^2 t_k^2) in +-pairs (the Gaussian weight suppresses
    all but the lowest few zeros -> effectively low-rank Gram).  NOT an RH knife-edge.
  * An earlier reading that "the archimedean block dominates and the primes threaten positivity" is BACKWARDS
    in this finite discretization: the pole-reduced archimedean block alone is O(1) NEGATIVE and the PRIMES
    are load-bearing for positivity.  (This crude finite split also does NOT reproduce the Connes-Consani
    functional archimedean-positivity theorem; only the FULL, validated form is unambiguous here.)

Context: telperion/docs/RH_BARRIER_CRACK_2026-08-30.md, RH_ZERO_RIGIDITY_TARGET_2026-08-30.md.
NOT a proof of RH.  conjecture1_proved = False.

Requires: mpmath, sympy, and a list of Riemann-zero ordinates t_k (mpmath.zetazero).
"""
import mpmath as mp
import sympy


def _zeros(N=200):
    return [mp.im(mp.zetazero(k)) for k in range(1, N + 1)]


def _vonmangoldt_terms(s, cut=9.0):
    """(log n, Lambda(n)/sqrt(n)) for prime powers n with (log n) within the Gaussian window."""
    out = []
    n = 2
    while n < int(mp.exp(cut)) + 2:
        f = sympy.factorint(n)
        if len(f) == 1:
            out.append((mp.log(mp.mpf(n)),
                        mp.log(mp.mpf(list(f.keys())[0])) / mp.sqrt(mp.mpf(n))))
        n += 1
    return out


def validate(s, tk):
    """Return (LHS_over_zeros, RHS_arithmetic) for the diagonal Weil value W(phi*phitilde); they must agree."""
    s = mp.mpf(s); pi = mp.pi; sp = mp.sqrt(pi)
    LHS = 2 * mp.fsum([2 * pi * s**2 * mp.exp(-s**2 * t**2) for t in tk])
    poles = 2 * (2 * pi * s**2 * mp.exp(s**2 / 4))
    logpi = -s * sp * mp.log(pi)
    arch = s**2 * 2 * mp.quad(
        lambda r: mp.exp(-s**2 * r**2) * mp.re(mp.digamma(mp.mpf(1)/4 + mp.mpf(1)/2 * 1j * r)), [0, mp.inf])
    prime = -2 * s * sp * mp.fsum([wt * mp.exp(-(ln**2) / (4 * s**2)) for ln, wt in _vonmangoldt_terms(s)])
    return LHS, poles + logpi + arch + prime


def kernel(D, s, tk):
    """Weil Gram Toeplitz entry M(Delta) via the (validated) sum over zeros."""
    s = mp.mpf(s); D = mp.mpf(D)
    return 4 * pi_(s) * s**2 * mp.fsum([mp.exp(-s**2 * t**2) * mp.cos(t * D) for t in tk])


def pi_(s):
    return mp.pi


def diag_dominance(s, delta, Ns, tk):
    """Max row diagonal-dominance ratio D of the Weil Gram matrix on N bumps spaced delta (D>1 => no dominance)."""
    delta = mp.mpf(delta)
    K = [kernel(i * delta, s, tk) for i in range(max(Ns))]
    out = []
    for N in Ns:
        M = [[K[abs(i - j)] for j in range(N)] for i in range(N)]
        D = max(mp.fsum([abs(M[i][j]) for j in range(N) if j != i]) / abs(M[i][i]) for i in range(N))
        out.append((N, float((N - 1) * delta), float(D)))
    return out


if __name__ == "__main__":
    mp.mp.dps = 40
    tk = _zeros(200)
    for s in ("0.12", "0.15", "0.20"):
        L, R = validate(s, tk)
        print(f"validate s={s}: |LHS-RHS|/|LHS| = {mp.nstr(abs(L - R) / abs(L), 4)}  (should be ~1e-38)")
    print("\ndiagonal-dominance D vs cone (D>1 and growing => dominance mechanism fails):")
    for N, L, D in diag_dominance("0.15", "0.35", [4, 8, 12, 16, 20], tk):
        print(f"  N={N:>3} coneL={L:>5.2f}  D={D:>7.3f}")
