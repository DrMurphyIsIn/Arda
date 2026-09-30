from sk import *
gD=85.699348
for x,K in [(31.,3),(8.,6)]:
    for fr in [.2,.3,.45]:
        for tau in np.arange(-1.5,1.51,.25):
            te=Tst(x,fr,2,gD-tau); A=arith('D',te,K)
            neg=[k+1 for k in range(K) if A[k]<0]
            if neg: print('D',x,fr,round(tau,2),'first neg k',neg[0],' '.join(f'{v:+.3g}' for v in A),flush=True)
# control: zeta at the D-test functions
te=Tst(31.,.3,2,gD-0.5); print('zeta ctl',arith('zeta',te,3))
