import json,math,numpy as np,mpmath as mp
def ks2(a,b):
    a=np.sort(a);b=np.sort(b);g=np.concatenate([a,b])
    Fa=np.searchsorted(a,g,side='right')/len(a);Fb=np.searchsorted(b,g,side='right')/len(b)
    d=np.max(np.abs(Fa-Fb)); ne=len(a)*len(b)/(len(a)+len(b))
    # asymptotic Kolmogorov p-value
    lam=(math.sqrt(ne)+0.12+0.11/math.sqrt(ne))*d
    p=2*sum((-1)**(j-1)*math.exp(-2*j*j*lam*lam) for j in range(1,100))
    return round(d,4), round(max(0,min(1,p)),5)
def un(name,a0):
  z=np.array(json.load(open(f'zeros_{name}_1200.json'))['zeros'])
  x=np.array([float(mp.im(mp.loggamma(a0+1j*g/2))+g/2*math.log(5/math.pi)) for g in z])/math.pi
  return z,np.diff(x)
zD,sD=un('D',.75); zL,sL=un('L5',.25)
print('KS D vs L5 (unfolded by Weyl phase):',ks2(sD,sL))
print('D gaps>2.2 below 200:',[(round(zD[i],2),round(zD[i+1],2),round(sD[i],2)) for i in range(len(sD)) if sD[i]>2.2 and zD[i]<200])
print('L5 max gap',round(sL.max(),3),' D max gap',round(sD.max(),3),' #gaps>2.2 D:',int((sD>2.2).sum()),' L5:',int((sL>2.2).sum()))
k=sD<2.2; s2=sD[k]/sD[k].mean()
print('KS D(holes removed, renormalised) vs L5:',ks2(s2,sL), 'var',round(s2.var(),4),'vs L5',round(sL.var(),4))
