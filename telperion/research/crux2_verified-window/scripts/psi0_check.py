# Checks on the archimedean symbol Psi_0(t) = Re psi(1/4 + i t/2) - log pi used in Theorem 2.
# (i) global minimum at t = 0 (Re psi(x+iy) - psi(x) = sum_k y^2/((x+k)((x+k)^2+y^2)) >= 0, increasing in |y|)
# (ii) Zhu Lemma 3.1: Psi_0(t) >= log(t/2pi) - 1/t for t >= 15/4 (spot checks)
# (iii) the margin in R: with R = 2 pi e^{A+}(1+eta) the crude bound needs eta >= ~1/R; 1e-6 is too small at A+ ~ 11
import mpmath as mp
mp.mp.dps = 40
def psi0(t):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * mp.mpf(t) / 2)) - mp.log(mp.pi)
print("Psi_0(0) =", mp.nstr(psi0(0), 12), " (psi(1/4) - log pi)")
vals = [psi0(t) for t in [0, 0.1, 0.5, 1, 2, 5, 10]]
print("Psi_0 at 0,0.1,0.5,1,2,5,10:", [mp.nstr(v, 8) for v in vals], " monotone:", all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1)))
worst = None
for t in [mp.mpf(15) / 4, 4, 5, 7, 10, 20, 50, 100, 1000, 1e4, 1e5, 4.4e5]:
    d = psi0(t) - (mp.log(t / (2 * mp.pi)) - 1 / t)
    worst = d if worst is None or d < worst else worst
    print(f"t={mp.nstr(t, 6):>10}: Psi_0 - (log(t/2pi) - 1/t) = {mp.nstr(d, 6)};  Psi_0 - log(t/2pi) = {mp.nstr(psi0(t) - mp.log(t / (2 * mp.pi)), 6)}")
print("min margin over spot checks:", mp.nstr(worst, 6))
for A in ["4.2449", "8.4612", "10.5269", "11.084", "11.161373010"]:
    A = mp.mpf(A); R6 = 2 * mp.pi * mp.e ** A * (1 + mp.mpf(10) ** -6)
    lhs = mp.log(R6 / (2 * mp.pi)) - 1 / R6
    print(f"A+={mp.nstr(A, 10)}: at R=2pi e^A (1+1e-6)={mp.nstr(R6, 8)}: log(R/2pi)-1/R - A+ = {mp.nstr(lhs - A, 4)}"
          f"  (Lemma 3.1 alone {'suffices' if lhs >= A else 'does NOT suffice'}); true Psi_0(R) - A+ = {mp.nstr(psi0(R6) - A, 4)}")
