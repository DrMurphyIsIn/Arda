"""HEURISTIC: stage3_search.model with every constant that section 15/20 of the 7/8 paper derive from
sixth-power rows / sextic symbols (zeta_F^S(6 z0) -> h/6 in C(sigma0); Gram count K_R^{1/6} -> b/12;
h(z0 - 1/6) in E; plain capacity 1/(6 kappa)) replaced by the analogue for k-th power rows, with the
cube exponent (3) and the row-energy cap 6 ell <= 1 (which come from the mean square and the cubes,
not from the symbol order) left as they are.  Everything else in the model is kept verbatim, including
constants (17/50, 2/3, 76/75, 7/37, ...) whose dependence on k was not traced.  So: a screen for whether
the HIGH side could tolerate the LOW side's law sigma0 >= 1 - (1 + 3 ell)/(2k), nothing more."""
from fractions import Fraction as Fr
import sys
sys.path.insert(0, "/Users/peterwmurphy/arda-e9-audit/telperion/research/qrh_stage3")

def model_k(k, sigma0, beta_in, lx, b, ell, z0=Fr(17, 50), dmin=Fr(1, 100), zeta=Fr(1, 100000), floor_a=Fr(51, 100)):
    ly = lx + b; h = 1 - lx + ell
    alpha = 2 * beta_in - 1
    kappa0 = 2 * sigma0 - 1
    cP = 1 / (k * kappa0)
    def E(d, a, q, R):
        delta = 2 * a - 1
        return a - sigma0 + h * (z0 - Fr(1, k)) - a * ly - ell / 2 + q * ell + d * (R + delta / 2 - z0)
    def Dx(x): return (1 - x) + (2 - 4 * x * cP)
    def Px(x): return (1 - x) * (2 - 4 * x * cP)
    def R_star(delta, x):
        Jv = (alpha - delta) * Dx(x) + delta * Px(x)
        t = 1 + delta * Px(x) / (2 * Jv)
        return 1 - delta + (alpha - delta) * (t - 1)
    worst = []
    deltas = [Fr(1, 50) + (alpha - Fr(1, 50)) * Fr(j, 40) for j in range(0, 41)]
    xs = [Fr(j, 40) for j in range(0, 21)]
    ds = [dmin + (h + zeta - dmin) * Fr(j, 40) for j in range(0, 41)]
    for delta in deltas:
        a = (1 + delta) / 2
        for x in xs:
            q = x * delta; Rs = R_star(delta, x); R1 = 1 - delta
            for d in ds:
                if d <= Fr(1, 2):
                    R = Fr(76, 75) - Fr(2, 3) * delta
                else:
                    R = min(Rs, R1) if delta < alpha else R1
                worst.append((E(d, a, q, R), f"delta={float(delta):.3f} x={float(x):.2f} d={float(d):.3f}"))
    delta0 = 2 * floor_a - 1
    for d in ds:
        worst.append((E(d, floor_a, delta0 / 2, 1), f"floor d={float(d):.3f}"))
    Emax, lab = max(worst)
    small = h * (z0 - Fr(1, k)) - ly / 2 + 2 * dmin
    supply = ell / (h + zeta) - Fr(7, 37)
    Csig = sigma0 + lx / 2 - 1 + h / k
    low_ok = Csig - (lx / 2 + b / (2 * k))
    cap_ok = 6 * ell <= 1
    return dict(Emax=Emax, where=lab, small=small, supply=supply, low_ok=low_ok, cap_ok=cap_ok, h=h)

print("sanity k=6 at the paper's point:")
r = model_k(6, Fr(7, 8), Fr(11, 12), Fr(17, 48), Fr(1, 8), Fr(1, 6)); print("  Emax", r['Emax'], "small", r['small'], "supply", r['supply'], "C-low", r['low_ok'])
print()
print("low-side law sigma0_low(k) = 1 - (1 + 3 ell)/(2k) at ell = 1/6 (the cap):")
for k in (6, 5, 4, 3, 2):
    print(f"  k={k}: sigma0_low = {1 - Fr(3, 2)/(2*k)} = {float(1 - Fr(3, 2)/(2*k)):.4f}   -> Lambda <= 2(theta-1/2)^2 = {float(2*(1 - Fr(3,2)/(2*k) - Fr(1,2))**2):.4f}")
print()
print("HIGH side screen at sigma0 = sigma0_low(k), ell = 1/6, Stage-III-style input beta_in = previous stage; best b over a grid:")
for k in (6, 5, 4, 3):
    s = 1 - Fr(3, 2) / (2 * k)
    for beta_in in (Fr(11, 12), Fr(7, 8), s + Fr(1, 100)):
        best = None
        for bn in range(1, 40):
            b = Fr(bn, 128); lx = (1 - b - Fr(1, 6)) / 2
            if lx <= 0: continue
            r = model_k(k, s, beta_in, lx, b, Fr(1, 6))
            key = (r['Emax'] < 0 and r['small'] < 0 and r['supply'] > 0, -r['Emax'])
            if best is None or key > best[0]: best = (key, b, r)
        key, b, r = best
        print(f"  k={k} sigma0={float(s):.4f} beta_in={float(beta_in):.4f}: high {'ok  ' if key[0] else 'FAIL'} best b={b} Emax={float(r['Emax']):+.4f} @{r['where']} small={float(r['small']):+.4f} supply={float(r['supply']):+.4f} C-low={float(r['low_ok']):+.4f}")
print()
print("How far does the high side descend for k=4 (what sigma0 does it tolerate at ell=1/6, beta_in=13/16+0.01)?")
k = 4
for s in [Fr(13, 16) + Fr(j, 100) for j in range(0, 12)]:
    best = None
    for bn in range(1, 40):
        b = Fr(bn, 128); lx = (1 - b - Fr(1, 6)) / 2
        if lx <= 0: continue
        r = model_k(k, s, s + Fr(1, 100), lx, b, Fr(1, 6))
        key = (r['Emax'] < 0 and r['small'] < 0 and r['supply'] > 0, -r['Emax'])
        if best is None or key > best[0]: best = (key, b, r)
    key, b, r = best
    print(f"  sigma0={float(s):.4f}: high {'ok  ' if key[0] else 'FAIL'} Emax={float(r['Emax']):+.4f} small={float(r['small']):+.4f} (b={b})")
