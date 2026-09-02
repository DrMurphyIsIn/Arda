import math
F=math.log(621/64)/11
def phi_leaf_share(g):  # leaf tight needs armmid-share k_leaf/11 <= tau_cap; leaf phi<=F* <=> tau_leaf<=F*/logBl
    Bl=(18+g)/(12+g); return F/math.log(Bl)   # max armmid share of leaf edge (tau, real)
def phi_arm(g,tl,to):
    A=(18+g)/12; Bl=(18+g)/(12+g); Bo=(18+g)/18
    return math.log(A)-tl*math.log(Bl)-to*math.log(Bo)
def feasible_real(g):  # best real tau: tau_leaf = min(1,cap), tau_other=1
    tl=min(1.0,phi_leaf_share(g)); return phi_arm(g,tl,1.0)
def best_grid(g,D):  # tau on k/D grid, k_leaf s.t. leaf ok (tau_leaf<=cap), maximize discharge
    cap=phi_leaf_share(g); best=9
    import math as m
    kl_max=int(m.floor(min(1.0,cap)*D))
    for kl in range(0,kl_max+1):
        for ko in range(0,D+1):
            best=min(best,phi_arm(g,kl/D,ko/D))
    return best
print(f"F* = {F:.6f}")
print("  g    tie-sup? real-feasible  intgrid(D=11)  finegrid(D=33)  finer(D=99)")
for g in [0.50,0.60,0.70,0.75,0.78,0.80,0.81,0.816]:
    rf=feasible_real(g); g11=best_grid(g,11); g33=best_grid(g,33); g99=best_grid(g,99)
    def fl(x): return f"{x-F:+.5f}"
    print(f" {g:.3f}   real {fl(rf)}   D11 {fl(g11)}   D33 {fl(g33)}   D99 {fl(g99)}")
print("\n(<=0 means certifiable at that grid; real column = the LP feasibility floor)")
