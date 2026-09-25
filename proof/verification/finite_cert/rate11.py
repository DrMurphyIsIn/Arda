exec(open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"rate10.py")).read().split('if __name__=="__main__":')[0])
import itertools
ks=[int(x) for x in sys.argv[1].split(",")]
for k in ks:
    best=None
    for k1 in (0,0.004,0.008):
        for k2 in (0.0025,0.005,0.0075):
            for k3 in (0.0025,0.005,0.0075):
                for k4 in (0,0.0005,0.001,0.0015,0.002,0.003):
                    kap={1:k1,2:k2,3:k3,4:k4}
                    a=alpha_kap(k,kap)*0.95
                    if a<=0: continue
                    if best is not None and best[0]==0: break
                    th=thresh(k,a,kap)
                    if best is None or th<best[0]: best=(th,a,kap)
    print(f"k={k}: threshold {best[0]} alpha={best[1]:.6f} kap={best[2]}",flush=True)
