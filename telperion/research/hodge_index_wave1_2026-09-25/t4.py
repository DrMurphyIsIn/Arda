import sys; sys.argv=['x','none','0']
exec(open('scan.py').read().split("mode = sys.argv[1]")[0])
for x in [5.03,5.1,6.0]:
  for N in [16,24]:
    out=[]
    for par in [0,1]:
        S=Setup(x,'ZK',N,par); ps=primes_upto(S.nmax)
        ch=lambda p: [('r',1.0),('r',-1.0),('r',0.0)] if p in (2,5) else [('th',th) for th in np.linspace(0,np.pi,25)]+[('in',)]
        v,loc=worst(S,ps,ch,cvec_deg2,sweeps=3,starts=6); out.append((v,loc))
    v,loc=min(out,key=lambda t:t[0]); print(x,N,'%.3e'%v,loc,flush=True)
