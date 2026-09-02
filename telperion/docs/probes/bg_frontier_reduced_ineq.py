import sys, math
sys.path.insert(0,"telperion/src")
from telperion.spider_broom import broom_total
from fractions import Fraction as Fr
F=math.log(621/64)/11
# EXACT broom frontier vertices: (y_{B(c)}, ell(B(c))) plus cherry (size2) and leaf.
def broom_yell(c):
    tot=broom_total(c); U=Fr(3,2)**c; h=U/tot; d=c+1; n=2*c+1
    return float(h)/d, math.log(float(tot))-n*F
verts=[(1.0,-F)]  # leaf
verts.append((1.0/3, math.log(1.5)-2*F))  # cherry
for c in range(1,40): verts.append(broom_yell(c))
verts=sorted(set(verts))
# upper concave hull
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
up=[]
for p in verts:
    while len(up)>=2 and cross(up[-2],up[-1],p)>=0: up.pop()
    up.append(p)
def Phi(y):
    if y<=up[0][0]: return up[0][1]
    if y>=up[-1][0]: return up[-1][1]
    for i in range(len(up)-1):
        (y0,e0),(y1,e1)=up[i],up[i+1]
        if y0<=y<=y1: return e0+(e1-e0)/(y1-y0)*(y-y0)
    return up[-1][1]
print("concave broom-frontier Phi vertices (y,ell):",[(round(y,4),round(e,4)) for y,e in up])
# the reduced inequality: j*Phi(Y/j) + L0(j,Y) <= Phi(1/(j+1+Y))  for j>=1, Y in [0, j*ymax]
def L0(j,Y): return math.log((j+1+Y)/(j+1))-F
worst=-9; argw=None
for j in range(1,25):
    Y=0.0
    while Y<=j*1.0+1e-9:
        yc=1.0/(j+1+Y)
        lhs=j*Phi(Y/j)+L0(j,Y) if j>0 else -9
        gap=lhs-Phi(yc)
        if gap>worst: worst=gap; argw=(j,round(Y,3),round(Y/j,4),round(yc,4))
        Y+=0.02
print(f"\nreduced inequality j*Phi(Y/j)+L0 <= Phi(1/(j+1+Y)): worst gap over j<=24,Y in[0,j] = {worst:+.6f}")
print(f"  worst at (j,Y,Y/j,yc)={argw}")
print("  "+("HOLDS -> single-child lemma closes via frontier induction + Jensen"
       if worst<=1e-6 else "fails at some (j,Y) -- inspect"))
