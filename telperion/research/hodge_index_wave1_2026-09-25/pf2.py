import win, json
def show(r): print(json.dumps({k:r[k] for k in ('kind','x','par','lam','lam2','ind_full','lam0_Q0','ind_Q0','signs_full','signs_Q0gs','cone_min') if k in r}, default=float),flush=True)
for x in (3,4,5,6): show(win.analyze('zeta',x,N=40,par=0))
for N in (30,50): show(win.analyze('ZK',28,N=N,par=0))
for x in (32,36,40,45): show(win.analyze('ZK',x,N=40,par=0))
for x in (32,36): show(win.analyze('ZK',x,N=40,par=1))
