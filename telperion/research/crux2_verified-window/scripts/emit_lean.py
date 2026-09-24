# Emit the Lean data block (weight tree + shift data) for a certificate JSON produced by cert_gen.py.
import json, sys, math

def tree_literal(vals, depth, pad=1):
    n = 2 ** depth
    vals = list(vals) + [pad] * (n - len(vals))
    def build(lo, d):
        if d == 0:
            return f"(.leaf {vals[lo]})"
        half = 2 ** (d - 1)
        return f"(.node {build(lo, d - 1)} {build(lo + half, d - 1)})"
    return build(0, depth)

def emit(cert, prefix):
    N = cert['N']; depth = max(1, math.ceil(math.log2(N)))
    lines = []
    lines.append(f"/-- Weight tree for the {prefix} certificate: {N} cells, depth {depth} (leaves beyond {N} are padding). -/")
    t = tree_literal(cert['w'], depth)
    # wrap long literal lines
    lines.append(f"def {prefix}Tree : WTree :=\n  {t}")
    lines.append(f"def {prefix}Depth : ℕ := {depth}")
    ds = cert['ds']
    items = ",\n    ".join(f"({d['C']}, {d['A']}, {d['B']})" for d in ds)
    lines.append(f"/-- Shift data (C_n, A_n, B_n) for n = {', '.join(str(d['n']) for d in ds)}. -/")
    lines.append(f"def {prefix}Shifts : List (ℕ × ℕ × ℕ) :=\n  [{items}]")
    return "\n\n".join(lines)

if __name__ == "__main__":
    cert = json.load(open(sys.argv[1]))
    print(emit(cert, sys.argv[2]))
