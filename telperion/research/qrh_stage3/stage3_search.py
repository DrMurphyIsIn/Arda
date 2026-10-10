"""Stage III feasibility search over the §19-§20 row-exponent system (Part B).

Generalizes stage2_model.py: boundary sigma0, previous-stage bound beta_in (alpha = 2*beta_in - 1),
baseline capacity constant c_P = 1/(6*kappa0) with kappa0 = 2*sigma0 - 1 (Lemma 18.1 / eq. 19.2 at
Delta = 0), geometry (lx, b, ell) with ly = lx + b, h = 1 - lx + ell, lx + ly + ell = 1, contour z0.

What this file checks: that every IDEAL row exponent E(d; a, q, R) of eq. (10.15) is strictly negative
over the retained bins, with R from Prop. 19.2 (balanced selection, the two no-slot cases, and the
d <= 1/2 common exponent), plus the small-row saving (20.6) and the prime-supply condition.
What it does NOT check (not yet extracted): the low estimate (Prop 15.3) that bounds the probe
directly by Z^{C(sigma0)+omega}; the validity ranges of Lemmas 8.1-8.3, 10.4 (stated for
sigma0 >= 7/8), 17.1, 18.1; the principal-term normalization. So a 'feasible' answer here is a
necessary-condition screen, not a proof. conjecture1_proved = False.
"""
from fractions import Fraction as Fr
import itertools, sys

def model(sigma0, beta_in, lx, b, ell, z0=Fr(17, 50), dmin=Fr(1, 100), zeta=Fr(1, 100000), floor_a=Fr(51, 100)):
    ly = lx + b; h = 1 - lx + ell
    assert lx + ly + ell == 1
    alpha = 2 * beta_in - 1                     # bin ceiling: delta <= kappa <= alpha
    kappa0 = 2 * sigma0 - 1                     # baseline kappa at Delta = 0
    cP = 1 / (6 * kappa0)                       # baseline plain capacity constant (2/9 at 7/8)
    def E(d, a, q, R):
        delta = 2 * a - 1
        return a - sigma0 + h * (z0 - Fr(1, 6)) - a * ly - ell / 2 + q * ell + d * (R + delta / 2 - z0)
    def Dx(x): return (1 - x) + (2 - 4 * x * cP)
    def Px(x): return (1 - x) * (2 - 4 * x * cP)
    def R_star(delta, x):                       # balanced selection, eq. (20.8)/(19.4)
        Jv = (alpha - delta) * Dx(x) + delta * Px(x)
        t = 1 + delta * Px(x) / (2 * Jv)
        return 1 - delta + (alpha - delta) * (t - 1)
    worst = []                                  # (value, label)
    # bins: delta in (1/50, alpha], mean amplitude x = q/delta in [0, 1/2], d in [dmin, h + zeta]
    deltas = [Fr(1, 50) + (alpha - Fr(1, 50)) * Fr(k, 40) for k in range(0, 41)]
    xs = [Fr(k, 40) for k in range(0, 21)]          # x = q/delta in [0, 1/2]
    ds = [dmin + (h + zeta - dmin) * Fr(k, 40) for k in range(0, 41)]
    for delta in deltas:
        a = (1 + delta) / 2
        for x in xs:
            q = x * delta
            Rs = R_star(delta, x)
            R_noslot_r1 = 1 - delta                    # r >= 1 branch of (19.3)
            R_noslot_t1 = 1 - Fr(2, 3) * delta         # t = 1, no slots (Prop 19.2)
            for d in ds:
                if d <= Fr(1, 2):
                    R = Fr(76, 75) - Fr(2, 3) * delta          # (20.11): the common exponent covering floor and t=1 no-slot rows
                    worst.append((E(d, a, q, R), f"d<=1/2 delta={float(delta):.3f} x={float(x):.2f} d={float(d):.3f}"))
                else:
                    R = min(Rs, R_noslot_r1) if delta < alpha else R_noslot_r1
                    worst.append((E(d, a, q, R), f"d>1/2 delta={float(delta):.3f} x={float(x):.2f} d={float(d):.3f}"))
    # floor bin a = 51/100, R = 1, q <= delta0/2
    delta0 = 2 * floor_a - 1
    for d in ds:
        worst.append((E(d, floor_a, delta0 / 2, 1), f"floor d={float(d):.3f}"))
    Emax, lab = max(worst)
    small = h * (z0 - Fr(1, 6)) - ly / 2 + 2 * dmin          # (20.6) small-row exponent, must be < 0
    supply = ell / (h + zeta) - Fr(7, 37)                      # prime supply margin, must be > 0
    Csig = sigma0 + lx / 2 - 1 + h / 6
    low_exp = lx / 2 + b / 12                                  # Prop 15.3: |I_modified| << Z^{lx/2 + b/12}
    low_ok = Csig - low_exp                                    # need C(sigma0) >= low exponent (omega < Delta is free)
    Mprime_min = (1 - ell) - 2 * ell                           # M' = M - 2d at d = ell; proof needs M' >= 1/2
    gram_ok = (1 + b - ell) / 2 - ell - Fr(11, 6) * b          # l_y - ell - 11b/6 >= 0 (P_a^2/Y' << P_a^{1/6})
    energy_pen = max(Fr(0), (5 * ell - 1 + ell) / 4)           # Lemma 15.1 penalty at d = ell
    return dict(Emax=Emax, where=lab, small=small, supply=supply, C=Csig, alpha=alpha, kappa0=kappa0, h=h, ly=ly,
                low_ok=low_ok, Mprime_min=Mprime_min, gram_ok=gram_ok, energy_pen=energy_pen)

def report(tag, r):
    high = r['Emax'] < 0 and r['small'] < 0 and r['supply'] > 0
    low = r['low_ok'] >= 0 and r['Mprime_min'] >= Fr(1, 2) and r['gram_ok'] >= 0 and r['energy_pen'] == 0
    ok = high and low
    print(f"{tag}: {'FEASIBLE' if ok else 'infeasible'} [high {'ok' if high else 'FAIL'}, low {'ok' if low else 'FAIL'}]  Emax={float(r['Emax']):+.5f} @{r['where']}  small={float(r['small']):+.4f}  supply={float(r['supply']):+.4f}  C-low={float(r['low_ok']):+.5f}  M'={float(r['Mprime_min']):.4f}  gram={float(r['gram_ok']):+.4f}  pen={float(r['energy_pen']):.4f}  h={float(r['h']):.4f}")
    return ok

if __name__ == "__main__":
    P = dict(lx=Fr(17, 48), b=Fr(1, 8), ell=Fr(1, 6))
    print("== sanity: the paper's Stage II (sigma0 = 7/8, beta_in = 11/12); expect FEASIBLE with C-low = 0 exactly")
    report("StageII@paper", model(Fr(7, 8), Fr(11, 12), **P))
    print("== sanity: ell = 0 (no prime compensation) should put the low side at 11/12")
    for s in (Fr(11, 12), Fr(11, 12) - Fr(1, 1000)):
        report(f"ell=0 sigma0={s}", model(s, Fr(11, 12), lx=Fr(1, 2) - Fr(1, 16), b=Fr(1, 8), ell=Fr(0)))
    print("== the low-side law sigma0 >= 11/12 - ell/4 (b cancels): check at several (ell, b)")
    for ell in (Fr(1, 6), Fr(1, 8), Fr(1, 10)):
        for b in (Fr(1, 8), Fr(1, 16)):
            r = model(Fr(11, 12) - ell / 4, Fr(11, 12), lx=(1 - b - ell) / 2, b=b, ell=ell)
            print(f"   ell={ell} b={b}: C-low={r['low_ok']} (0 = tight)")
    print("== fixed geometry, lower sigma0: the low side fails first, the high side has ~1e-4 of slack")
    for k in (1, 10, 50):
        s = Fr(7, 8) - Fr(k, 10000); report(f"sigma0=7/8-{k}e-4", model(s, Fr(11, 12), **P))
    print("== what if the slot ceiling were ignored: ell above 1/6 with the Stage III inputs (beta_in = 7/8)")
    for ell in (Fr(1, 6), Fr(1, 5), Fr(1, 4), Fr(1, 3)):
        s = Fr(11, 12) - ell / 4
        best = None
        for b in [Fr(k, 64) for k in range(1, 20)]:
            lx = (1 - b - ell) / 2
            if lx <= 0: continue
            r = model(s, Fr(7, 8), lx=lx, b=b, ell=ell)
            key = (r['Emax'] < 0 and r['small'] < 0 and r['supply'] > 0, -r['Emax'])
            if best is None or key > best[0]: best = (key, b, r)
        key, b, r = best
        report(f"ell={ell} sigma0=11/12-ell/4={s} (={float(s):.4f}) best b={b}", r)

    print("== which side binds: ell = 1/6 (the ceiling), Stage III inputs (beta_in = 7/8), HIGH side only, sigma0 descending")
    for s in [Fr(7, 8) - Fr(k, 200) for k in range(0, 13)]:
        best = None
        for b in [Fr(k, 64) for k in range(1, 24)]:
            lx = (1 - b - Fr(1, 6)) / 2
            r = model(s, Fr(7, 8), lx=lx, b=b, ell=Fr(1, 6))
            key = (r['Emax'] < 0 and r['small'] < 0 and r['supply'] > 0, -r['Emax'])
            if best is None or key > best[0]: best = (key, b, r)
        key, b, r = best
        high = key[0]
        print(f"   sigma0={float(s):.4f}: high side {'ok ' if high else 'FAIL'} (best b={b}, Emax={float(r['Emax']):+.5f} @{r['where']}, small={float(r['small']):+.4f}, supply={float(r['supply']):+.4f}); low side needs sigma0 >= 7/8: {'ok' if s >= Fr(7,8) else 'FAIL'}")
