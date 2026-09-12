from fractions import Fraction as F

# ============ ENGINE A: EXACT PORT OF REPO Lean RECURSION ============
# RTree = ('node', [(weight, child_RTree), ...])
# UTree = ('u', [child_UTree, ...])

# --- CavityTree.lean ---
def Zopen(t):
    # Zopen(node cs) = Popen cs
    return Popen(t[1])

def Ztot(t):
    # Ztot(node cs) = Popen cs + Matched cs
    cs = t[1]
    return Popen(cs) + Matched(cs)

def Popen(cs):
    # Popen [] = 1 ; Popen((_,c)::rest) = Ztot c * Popen rest
    if not cs:
        return F(1)
    (_, c) = cs[0]
    return Ztot(c) * Popen(cs[1:])

def Matched(cs):
    # Matched [] = 0 ; Matched((w,c)::rest) = w*Zopen c*Popen rest + Ztot c*Matched rest
    if not cs:
        return F(0)
    (w, c) = cs[0]
    rest = cs[1:]
    return w * Zopen(c) * Popen(rest) + Ztot(c) * Matched(rest)

# --- R47Tree.lean ---
def udeg(u):
    # udeg(node cs) = cs.length + 1
    return len(u[1]) + 1

def dtSub(u):
    # dtSub(node cs) = RTree.node(dtChildren (cs.length+1) cs)
    cs = u[1]
    return ('node', dtChildren(len(cs) + 1, cs))

def dtChildren(d, cs):
    # dtChildren _ [] = [] ; dtChildren d (K::rest) = (1/(d*udeg K), dtSub K) :: dtChildren d rest
    if not cs:
        return []
    K = cs[0]
    rest = cs[1:]
    return [(F(1, d * udeg(K)), dtSub(K))] + dtChildren(d, rest)

def dtRealize(u):
    # dtRealize(node cs) = RTree.node(dtChildren cs.length cs)
    cs = u[1]
    return ('node', dtChildren(len(cs), cs))

def Aobj(u):
    return Ztot(dtRealize(u))

# ============ ENCODE UTrees ============
def U(children):
    return ('u', children)

# cherryU = node[leaf]; leaf = node[]
LEAF = U([])
CHERRY = U([LEAF])          # node with one child (a leaf) => length-2 pendant path

# T(6,6,6,6): 4 core vertices in a path, each with 6 cherries.
# Build as nested chain. Innermost core vertex has 6 cherries + (chain continues).
# A path of 4 core vertices: v1 - v2 - v3 - v4, each vertex also has 6 cherry pendants.
# Rooted at v1. v1's children = 6 cherries + v2. v2's children = 6 cherries + v3. etc.
# v4 (end) children = 6 cherries only.
def core_chain(depth):
    # depth vertices remaining in the chain
    if depth == 1:
        return U([CHERRY]*6)
    else:
        return U([CHERRY]*6 + [core_chain(depth-1)])

T = core_chain(4)

# size check: count vertices. Each cherry = 2 vertices. 4 core + 4*6 cherries*2 = 4 + 48 = 52.
def count_vertices(u):
    return 1 + sum(count_vertices(c) for c in u[1])
n_T = count_vertices(T)

aobj_T = Aobj(T)

# ============ HUB(a,b,c) size-52 ============
# armU(j) = node(j cherries) i.e. a load-j arm is a vertex with j cherries.
# hub(a,b,c) = single vertex (root) with a load-5 arms + b load-4 arms + c cherries.
# armU(5) = node with 5 cherries; armU(4) = node with 4 cherries.
def armU(j):
    return U([CHERRY]*j)

def hub(a, b, c):
    children = [armU(5)]*a + [armU(4)]*b + [CHERRY]*c
    return U(children)

# Constraint: 11a+9b+2c=51, a+b>=5, c<=5.
# Verify size: hub root=1 vertex. armU(5)= 1 + 5*2 = 11 vertices. armU(4)=1+4*2=9. cherry=2.
# total = 1 + 11a + 9b + 2c = 1 + 51 = 52. Good.
best = None
best_val = None
results = []
for a in range(0, 6):
    for b in range(0, 6):
        for c in range(0, 6):
            if 11*a + 9*b + 2*c == 51 and (a+b) >= 5 and c <= 5:
                h = hub(a,b,c)
                assert count_vertices(h) == 52, (a,b,c,count_vertices(h))
                v = Aobj(h)
                results.append((a,b,c,v))
                if best_val is None or v > best_val:
                    best_val = v
                    best = (a,b,c)

print("n_T =", n_T)
print("Aobj(T(6,6,6,6)) =", aobj_T.numerator, "/", aobj_T.denominator)
print()
print("Valid hubs and Aobj:")
for (a,b,c,v) in sorted(results):
    tag = " <== ARGMAX" if (a,b,c)==best else ""
    print(f"  (a,b,c)=({a},{b},{c}): {v.numerator}/{v.denominator}{tag}")
print()
print("tieArgmax(52) =", best_val.numerator, "/", best_val.denominator, "at", best)
print()

# Baseline comparison
base_aobj = F(1180837892027061, 26306674688)
base_tie  = F(4695479375868117, 104857600000)
base_diff = F(8862581903961897, 82208358400000)
print("MATCH Aobj:", aobj_T == base_aobj)
print("MATCH tie :", best_val == base_tie)
diff = aobj_T - best_val
print("diff Aobj(T)-tie =", diff.numerator, "/", diff.denominator, " sign:", "POSITIVE" if diff>0 else ("NEGATIVE" if diff<0 else "ZERO"))
print("MATCH diff:", diff == base_diff)
