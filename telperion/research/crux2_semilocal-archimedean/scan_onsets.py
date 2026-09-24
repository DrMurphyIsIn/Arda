import sys, json, time
import mpmath as mp
import semilocal as sl

def lam12(x, N, sector, arith, dps):
    Q, L = sl.build_form(x, N, sector, arith, dps=dps)
    E = sl.eigs(Q)
    return E[0], E[1]

which = sys.argv[1]
N = int(sys.argv[2]) if len(sys.argv) > 2 else 24
dps = int(sys.argv[3]) if len(sys.argv) > 3 else 40
rows = []
if which == 'golden':
    xs = ['4.9', '5.2', '5.5', '6', '6.5', '7', '8', '9', '10', '12', '14', '16', '20', '25', '30']
    arith = ('surgery', 5, 5)
elif which == 'w1':
    xs = ['28', '29.5', '31', '33', '36', '40', '45', '50', '60', '70', '84', '100']
    arith = ('surgery', 29, 11)
elif which.startswith('slocal'):
    P = int(which[6:])
    q = sl.primes_upto(200)
    qn = [p for p in q if p > P][0]
    xs = [str(v) for v in [qn - 0.5, qn + 0.01, qn + 0.2, qn + 0.5, qn + 1, qn * 1.3, qn * 1.6, qn * 2, qn * 3, qn * 4]]
    arith = ('slocal', P)
for x in xs:
    for sector in ('even', 'odd'):
        t0 = time.time()
        l1, l2 = lam12(x, N, sector, arith, dps)
        row = dict(which=which, x=x, sector=sector, N=N, dps=dps, l1=mp.nstr(l1, 6), l2=mp.nstr(l2, 6), s=round(time.time() - t0, 1))
        rows.append(row)
        print(json.dumps(row), flush=True)
json.dump(rows, open(f'scan_{which}_N{N}.json', 'w'), indent=1)
