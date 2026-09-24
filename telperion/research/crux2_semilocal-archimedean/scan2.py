import sys, json, time
import mpmath as mp
import semilocal as sl
which = sys.argv[1]
N = int(sys.argv[2]); dps = int(sys.argv[3])
if which == 'w1':
    xs = ['30', '32', '34', '36', '38', '40', '42', '44', '46', '50', '55', '60']; arith = ('surgery', 29, 11)
elif which == 'refine5':
    xs = ['5.02', '5.04', '5.06', '5.08', '5.1', '5.13', '5.16']; arith = ('slocal', 3)
elif which == 'refine7':
    xs = ['7.02', '7.05', '7.08', '7.11', '7.15', '7.2', '7.3']; arith = ('slocal', 5)
elif which == 'refine3':
    xs = ['3.02', '3.04', '3.06', '3.08', '3.1', '3.13', '3.16']; arith = ('slocal', 2)
elif which == 'refine2':
    xs = ['2.02', '2.05', '2.08', '2.1', '2.13', '2.16', '2.19']; arith = ('slocal', 1)
elif which == 'golden_fine':
    xs = ['5.6', '5.7', '5.8', '5.9']; arith = ('surgery', 5, 5)
for x in xs:
    for sector in ('even', 'odd'):
        t0 = time.time()
        Q, L = sl.build_form(x, N, sector, arith, dps=dps)
        E = sl.eigs(Q)
        print(json.dumps(dict(which=which, x=x, sector=sector, N=N, l1=mp.nstr(E[0], 6), l2=mp.nstr(E[1], 6), s=round(time.time()-t0,1))), flush=True)
