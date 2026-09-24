import mpmath as mp
mp.mp.dps = 25
c4 = [0, 1, 0, -1]; c5 = [0, 1, -1, -1, 1]
c20 = [c4[n % 4] * c5[n % 5] for n in range(20)]
def EQ(s):
    return mp.zeta(s) * mp.dirichlet(s, c20) + mp.dirichlet(s, c4) * mp.dirichlet(s, c5)
# coarse scan of |E_Q| on [0.52, 1.6] x [20, 30.85]
best = []
for i in range(0, 28):
    sig = mp.mpf('0.52') + i * mp.mpf('0.04')
    for j in range(0, 218):
        t = mp.mpf(20) + j * mp.mpf('0.05')
        v = abs(EQ(mp.mpc(sig, t)))
        best.append((v, sig, t))
best.sort(key=lambda x: x[0])
seen = []
for v, sig, t in best[:40]:
    try:
        z = mp.findroot(EQ, mp.mpc(sig, t))
    except Exception:
        continue
    if abs(EQ(z)) < 1e-18 and z.real > 0.5 + 1e-8 and 20 < z.imag < 30.85:
        if all(abs(z - w) > 1e-8 for w in seen):
            seen.append(z)
print("off-line zeros of E_Q with Re>0.5 in t in [20,30.85]:", [mp.nstr(z, 15) for z in seen])
