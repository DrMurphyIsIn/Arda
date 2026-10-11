"""Residual constant rho for ArchS9_CertRes (completeness): sup_[0,1] |T psi_n - theta_n psi_n| <= rho,
rho = gamma * sum_m |theta_m| Psi1_m + zeta1 (1 + gamma), Psi1_m = sum_k |B_mk|.  Reuses gen_s9.py.
Prints the Lean literal.  conjecture1_proved = False."""
import sys
sys.argv = ["gen_s9.py", "/dev/null"]
exec(open("gen_s9.py").read())
Psi1 = [sum(abs(x) for x in B[m]) for m in range(J)]
rho = up(gamQ * sum(abs(th[m]) * Psi1[m] for m in range(J)) + z1 * (1 + gamQ), 3)
for n in range(NC + 1):
    assert rho ** 2 < win[n]["w0"] ** 2 * (1 - gamQ)
print("rhoQ", q(rho), float(rho), file=sys.stderr)
print(q(rho))
