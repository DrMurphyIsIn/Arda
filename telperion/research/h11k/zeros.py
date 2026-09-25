import mpmath as mp
mp.mp.dps=20
for T in [mp.mpf(31851)/4, 8000, 11000]:
    print(T, mp.nzeros(T))
n0 = int(mp.nzeros(11000))
for n in range(n0-1, n0+12):
    print(n, mp.zetazero(n).imag)
