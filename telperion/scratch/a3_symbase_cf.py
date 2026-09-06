"""
Closed form for Aobj(node[j-star, k-star]) and the collapsed single-child after tree.
Derive the general (j,k) closed form to confirm the neutrality is a clean identity.
"""
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, Ztot_sub, Zopen_sub, LEAF

def kstar(k):
    return tuple([LEAF] * k)

# cavity values of a k-star realized as a subtree (dtSub):
# a k-star = node(replicate k leaf). udeg = k+1. Each leaf child: Ztot=1,Zopen=1,udeg=1,
# weight 1/((k+1)*1). Popen = 1. Matched = k * 1/(k+1) = k/(k+1).
# Ztot(dtSub kstar) = 1 + k/(k+1) = (2k+1)/(k+1). Zopen(dtSub kstar)=1.
for k in range(1, 10):
    ks = kstar(k)
    print(f"k={k}: Ztot(dtSub kstar)={Ztot_sub(ks)}  pred={Fr(2*k+1,k+1)}  Zopen={Zopen_sub(ks)}")

print()
# before = node[j-star,k-star], root degree 2.
# Aobj = P*(1 + qSum/2), P = Ztot(dtSub jstar)*Ztot(dtSub kstar),
# qContrib(star_m) = Zopen/Ztot/udeg = 1 / ((2m+1)/(m+1)) / (m+1) = 1/(2m+1).
# qSum = 1/(2j+1)+1/(2k+1).
def before_cf(j,k):
    P = Fr(2*j+1,j+1)*Fr(2*k+1,k+1)
    q = Fr(1,2*j+1)+Fr(1,2*k+1)
    return P*(1+q/2)

for j in range(2,6):
    for k in range(2,6):
        print(f"j={j} k={k}: engine={Aobj_node((kstar(j),kstar(k)))}  closed={before_cf(j,k)}  {'OK' if Aobj_node((kstar(j),kstar(k)))==before_cf(j,k) else 'X'}")

# symmetric j=k: P=((2k+1)/(k+1))^2, q=2/(2k+1); Aobj = ((2k+1)/(k+1))^2 * (1+1/(2k+1))
# = ((2k+1)/(k+1))^2 * (2k+2)/(2k+1) = (2k+1)^2/(k+1)^2 * 2(k+1)/(2k+1) = 2(2k+1)/(k+1) = (4k+2)/(k+1). QED
print()
print("symmetric closed form 2(2k+1)/(k+1)=(4k+2)/(k+1):")
for k in range(2,8):
    print(f" k={k}: {Fr(4*k+2,k+1)} == {before_cf(k,k)}  {before_cf(k,k)==Fr(4*k+2,k+1)}")
