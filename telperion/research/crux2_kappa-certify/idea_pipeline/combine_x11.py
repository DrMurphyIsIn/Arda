"""Final assembly for x = 11.006 (a = 307/256): lam_min(Q_sector) >= min(lam0 - resid - eta_quad, b'' - eps_D) - eps_B,
with eta_quad from the refined, mode-weighted Bernstein bound (quad_opt2.py) for the SAME node set, and lam0, resid,
eps_B, eps_D, b'' read from the certification logs (verified blocked Cholesky, 384-bit factor, Arb residual)."""
import ast, sys, flint
from flint import arb
flint.ctx.prec = 256
def parse(fn, sector):
    for line in open(fn):
        line = line.strip()
        if line.startswith(sector + ':'):
            d = ast.literal_eval(line[len(sector) + 1:].strip())
            return d
    return None
def ball(s):
    s = s.strip('[]')
    if '+/-' in s:
        m, r = s.split('+/-')
        return arb(m.strip()) + arb(0, float(r))
    return arb(s)
bpp = {'even': arb('0.200448'), 'odd': arb('0.736946')}      # lower values of b'' printed in the log headers (rounded down)
eta = {'even': arb('1.49e-55'), 'odd': arb('6.60e-56')}       # refined bounds from log_quad_opt2.txt (rounded up)
for sector in ('even', 'odd'):
    d = parse('log_wa3_a307_%s.txt' % sector, sector)
    if d is None:
        print(sector, 'not finished'); continue
    lam0 = arb(d['lam0'])
    resid = ball(d['resid'])
    epsB = ball(d['epsB']); epsD = ball(d['epsD'])
    lead = lam0 - resid.upper() - eta[sector]
    final = lead.min(bpp[sector] - epsD.upper()) - epsB.upper()
    print("%s: lam0=%s resid=%s eta_refined=%s epsB=%s epsD=%s  =>  lam_min(Q_%s) >= %s  positive=%s" % (
        sector, lam0.str(6), resid.str(3), eta[sector].str(3), epsB.str(3), epsD.str(3), sector, final.str(8), final > 0))
