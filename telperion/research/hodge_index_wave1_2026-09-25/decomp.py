import sys; sys.path.insert(0,'/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
from bcore import *
N=40
wZ=weights_mp('ZK',40); wE=weights_mp('E',40)
for x in [float(a) for a in sys.argv[1:]]:
    A=np.log(x)/2; kap=sector_basis(A,N,0)
    FE=Form(A,'E'); ME,G,PE=real_sector(FE,kap,0,parts=True)
    FZ=Form(A,'ZK'); MZ,_=real_sector(FZ,kap,0)
    eE,VE=gmin(ME,G,vec=True); eZ,VZ=gmin(MZ,G,vec=True)
    ns=sorted(set(n for n,_,_ in FE.pr)|set(n for n,_,_ in FZ.pr))
    Tn={}
    for n in ns:
        FE.pr=[(n,1.0,float(np.log(n)))]
        _,_,P=real_sector(FE,kap,0,parts=True); Tn[n]=P['comb']
    base=PE['pole']+PE['arch']
    for lab,v in (('vE',VE[:,0]),('vZ',VZ[:,0])):
        print(f'x={x} {lab}: QE={v@ME@v:.4e} QZ={v@MZ@v:.4e} pole+arch={v@base@v:.4e}')
        print('   n   -cZ T   -cE T   diff(E-Z)')
        for n in ns:
            t=v@Tn[n]@v; cz=float(wZ[n])/np.sqrt(n); ce=float(wE[n])/np.sqrt(n)
            print(f'  {n:3d} {-cz*t:+.4e} {-ce*t:+.4e} {-(ce-cz)*t:+.4e}   T={t:+.3e}')
