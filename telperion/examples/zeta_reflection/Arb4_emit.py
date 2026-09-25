"""Arb4_emit.py -- lane Arb4: emit COMPACT kernel certificates for a hypothesis-free ladder segment.

The planners of lane h1000-integrate (emit_h1000_offline.py: octant pieces of the horizontal edges,
zero-free slab cells) and lane h1000-prep (emit_h1000_line.py: on-line sign points) are reused
unchanged; only the LEAN FORM of the certificates changes.  Every side condition that the old
modules closed by `norm_num` (budget, remainder, G certificate, scalar geometry, pins, ...) is
checked by a Boolean kernel checker with a soundness theorem proved once (Arb4_Side, Arb4_Edge,
Arb4_Slab, Arb4_Line, Arb4_Gamma), and the evaluator states are recomputed inside the same
`decide +kernel` instead of being stored.  Data definitions are `noncomputable` (no IR).

This module only provides the emission helpers; the drivers are Arb4_emit_h1000.py and
Arb4_emit_h2000.py.  conjecture1_proved = False.
"""
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "arbecon"))


# ------------------------------------------------------------------ literals

def ql(x):
    """a rational as an `Arb4.Q` literal (`Q.frac n d`)."""
    x = Fr(x)
    if x.numerator < 0:
        return "(Q.frac (%d) %d)" % (x.numerator, x.denominator)
    return "(Q.frac %d %d)" % (x.numerator, x.denominator)


def zl(k):
    return "(%d)" % k if k < 0 else "%d" % k


def rl(x):
    """a rational as a Lean real literal"""
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)


# ------------------------------------------------------------------ one octant piece

def piece_fields(pd):
    """the `Arb4.PieceD` fields of a planned piece (emit_h1000_offline.piece_data)."""
    o = pd["o"]
    r = Fr(pd["r"])
    F = Fr(pd["F"])
    if pd["gd"] is None:
        ga, gb, gq, Gn, Gd = 0, 0, 1, 1, 1
    else:
        gb_, Gn_, Gd_, _xm = pd["gd"]
        ga, gb, gq, Gn, Gd = 0, gb_, 16, Gn_, Gd_
    return ("{ a := %d, b := %d, q := %d, rn := %d, rd := %d, kk := %s, FN := %d, FD := %d, "
            "aQ := %s, U := %s, ga := %d, gb := %d, gq := %d, Gn := %d, Gd := %d, "
            "ea := %d, eb := %d, eqd := 16, Rn := %d, Rd := %d, xhi := %s, sigs := %s, "
            "Qr := %d, E := %s }") % (
        o.a, o.b, o.q, r.numerator, r.denominator, zl(pd["kk"]), F.numerator, F.denominator,
        ql(pd["a"]), ql(pd["U"]), ga, gb, gq, Gn, Gd,
        pd["ea"], pd["eb"], pd["Rn"], pd["Rd"], ql(pd["xhi"]), ql(pd["sigs"]),
        pd["Qr"], ql(pd["E"]))


def edge_def(e, name):
    """`noncomputable def <name> : Arb4.EdgeD` for a planned + enclosed edge (emit_h1000_offline)."""
    ps = e["pieces"]
    m = len(ps)
    b0, b1 = e["box0"], e["box1"]
    L = []
    L.append("noncomputable def %s : EdgeD where" % name)
    L.append("  tn := %d" % e["tn"])
    L.append("  tq := %d" % e["tq"])
    L.append("  N := %d" % e["N"])
    L.append("  L := %s" % ql(e["L"]))
    L.append("  m := %d" % m)
    xs = [pd["hi"] for pd in ps] + [ps[-1]["lo"]]
    L.append("  x := fun j => [%s].getD j %s" % (", ".join(ql(x) for x in xs), ql(xs[-1])))
    L.append("  pc := fun j => [%s].getD j %s" % (",\n    ".join(piece_fields(pd) for pd in ps),
                                                piece_fields(ps[-1])))
    for tag, bx, q in (("0", b0, e["q0"]), ("1", b1, e["q1"])):
        L.append("  D%s := %d" % (tag, bx["D"]))
        L.append("  reLo%s := %s" % (tag, zl(bx["reLo"])))
        L.append("  reHi%s := %s" % (tag, zl(bx["reHi"])))
        L.append("  imLo%s := %s" % (tag, zl(bx["imLo"])))
        L.append("  imHi%s := %s" % (tag, zl(bx["imHi"])))
        L.append("  Qp%s := %d" % (tag, bx["Qp"]))
        L.append("  Rn%s := %d" % (tag, bx["Rn"]))
        L.append("  Rd%s := %d" % (tag, bx["Rd"]))
        L.append("  qlo%s := %s" % (tag, ql(q[0])))
        L.append("  qhi%s := %s" % (tag, ql(q[1])))
    L.append("  Lo := %s" % ql(e["Lv"]))
    L.append("  Hi := %s" % ql(e["Hv"]))
    return "\n".join(L)


def edge_tag(T):
    T = Fr(T)
    if T.denominator == 1:
        return "T%d" % T.numerator
    return "T%d_%d" % (T.numerator, T.denominator)


# ------------------------------------------------------------------ one zero-free slab

def slab_cells(sd):
    """the leaves of a planned slab (emit_h1000_offline.plan_slab), as x-columns [xl, xr] x [a, b]."""
    import emit_h1000_offline as OFF
    cells = []
    for tr in sd["trees"]:
        cells += OFF.leaves(tr)
    for cl in cells:
        assert cl["yl"] == sd["a"] and cl["yh"] == sd["b"], "slab %s: a y-split (unsupported)" % sd["tag"]
    cells.sort(key=lambda cl: cl["xl"])
    assert cells[0]["xl"] == Fr(1, 2) and cells[-1]["xr"] == 1
    for u, v in zip(cells, cells[1:]):
        assert u["xr"] == v["xl"]
    return cells


def cell_fields(cl):
    o = cl["o"]
    return "{ a := %d, b := %d, q := %d, tn := %d, rn := %d, rd := %d, w := %s, hh := %s }" % (
        o.a, o.b, o.q, cl["tn"], cl["rn"], cl["rd"], ql(cl["w"]), ql(cl["hh"]))


def slab_def(sd, name):
    """`noncomputable def <name> : Arb4.SlabD` for a planned slab."""
    cells = slab_cells(sd)
    xs = [cl["xl"] for cl in cells] + [cells[-1]["xr"]]
    F = Fr(sd["F"])
    L = []
    L.append("noncomputable def %s : SlabD where" % name)
    L.append("  tq := %d" % sd["tq"])
    L.append("  N := %d" % sd["N"])
    L.append("  L := %s" % ql(sd["L"]))
    L.append("  R := %s" % ql(sd["R"]))
    L.append("  lo := %s" % sd.get("lo_q", ql(sd["a"])))
    L.append("  hi := %s" % sd.get("hi_q", ql(sd["b"])))
    L.append("  U := %s" % ql(sd["U"]))
    L.append("  Qr := %d" % sd["Qr"])
    L.append("  r0 := %d" % sd["r0"])
    L.append("  FN := %d" % F.numerator)
    L.append("  FD := %d" % F.denominator)
    L.append("  m := %d" % len(cells))
    L.append("  xs := fun j => [%s].getD j %s" % (", ".join(ql(x) for x in xs), ql(xs[-1])))
    L.append("  cell := fun j => [%s].getD j %s" % (",\n    ".join(cell_fields(cl) for cl in cells),
                                                  cell_fields(cells[-1])))
    return "\n".join(L)


# ------------------------------------------------------------------ one on-line band

def pt_lean(p):
    """`Arb4.mkPt …` for a planned point (emit_h1000_line.make_point)."""
    return "mkPt %d %d %d %d %d %d %d %d %s" % (p.tn, p.tq, p.N, p.Q, p.r, p.k, p.nl, p.m,
                                              "true" if p.pos else "false")


def band_pts_def(pts, name):
    L = ["noncomputable def %s : List H1000Line.LinePt := [" % name]
    L.append(",\n".join("  " + pt_lean(p) for p in pts) + "]")
    return "\n".join(L)
