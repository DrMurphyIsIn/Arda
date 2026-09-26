exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate5.py")).read().split('if __name__=="__main__":')[0])
import pickle
L=math.log(26/23)
sp=pickle.load(open("spider_cache_520.pkl","rb")); phisp={n:math.log(v[0])-(n-1)*F for n,v in sp.items()}
def optkap(D):
    kap={1:0.0,2:0.005,3:0.005}; best=alpha_kap(D,kap)
    step=0.004
    while step>2e-4:
        improved=False
        for j in (1,2,3):
            for sgn in (1,-1):
                k2=dict(kap); k2[j]=max(0.0,k2[j]+sgn*step); a=alpha_kap(D,k2)
                if a>best+1e-9: best,kap,improved=a,k2,True
        if not improved: step/=2
    return best,kap
res={}
for k in range(2,24):
    a,kap=optkap(k); al=a*0.95
    T=types_k(al,k,kap)
    vals=[]
    for nm,b,y,bcc,s in AT:
        if bcc>k-1: continue
        vals.append((y,b+al*s))
    for (bcc,lo,hi) in classes(k):
        for y in (lo,hi): vals.append((y,-rho(bcc,y)-kap.get(bcc,0)))
    best=min(math.log(t)+1/t-1+k*max(w+y/(k*t) for y,w in vals) for t in np.linspace(1.001,6,3000))
    need=[n for n in range(4,521) if -al*(n-1)+best>=phisp[n]]
    res[k]=(al,kap,best,max(need) if need else 3)
    print(f"k={k:2d} alpha={al:.6f} kap={ {j:round(v,4) for j,v in kap.items()} } R_k={best:.4f} threshold n<= {res[k][3]} still open",flush=True)
print("N1 =",max(r[3] for r in res.values())+1)
pickle.dump(res,open("rate6_res.pkl","wb"))
