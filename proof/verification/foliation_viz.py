"""Cavity-FOLIATION visualization of the amplitude recursion behind Phi<=1 -- the matplotlib companion to
wolfram_viz.wl, in the spirit of the Wolfram Physics Project's foliations of causal graphs.

A rooted branch is sliced into depth layers (a "time" ordering); the cavity field
    m_v = z_v / (1 + z_v * sum_children m_c),   z_v = 3/(3 d_v + c_v),   m_leaf = z_leaf,
is UPDATED leaf -> root across the slices, and the log-amplitude telescopes across the foliation
    log Phi = sum_v ( log(a_v z_v) - log m_v ),   a_v = F(d_v,c_v)/rho_B^(1+2 c_v).
The two exact ties (Phi=1) root at the tie cavity m=3/23; a deep chain's cavity accumulates at sqrt(2)-1
(the E2 Cantor point).  Run: python -m ...foliation_viz  (writes cavity_foliation.png).  Requires numpy,
matplotlib.
"""
from __future__ import annotations

from collections import defaultdict

import numpy as np

RHO_B = (621 / 64) ** (1 / 11)
ARM = (0, [(0, [])])


def _build(spec, depth=0, nodes=None, edges=None, parent=None):
    if nodes is None:
        nodes, edges = [], []
    c, kids = spec
    idx = len(nodes)
    nodes.append({"c": c, "depth": depth})
    if parent is not None:
        edges.append((parent, idx))
    nodes[idx]["children"] = [_build(k, depth + 1, nodes, edges, idx) for k in kids]
    return idx if parent is not None else (nodes, edges)


def _cavity(nodes, i):
    nd = nodes[i]
    S = sum(_cavity(nodes, k) for k in nd["children"])
    d = len(nd["children"]) + 1 + nd["c"]
    nd.update(m=3 / (3 * d + nd["c"] + 3 * S), d=d)
    return nd["m"]


def _contrib(nodes, i):
    nd = nodes[i]
    d, c = nd["d"], nd["c"]
    F = (1.5 ** c) * (1 + c / (3 * d))
    z = 3 / (3 * d + c)
    a = F / RHO_B ** (1 + 2 * c)
    return np.log(a * z) - np.log(nd["m"])


def render(path="cavity_foliation.png"):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.cm as cm
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle
    specs = {
        "tie N(0,5)  (Phi=1)": (0, [ARM] * 5),
        "arm-substitute root(4)-0-0  (Phi=1)": (4, [(0, [(0, [])])]),
        "deep chain  (m -> sqrt(2)-1)": (0, [(0, [(0, [(0, [(0, [(0, [])])])])])]),
    }
    fig, axes = plt.subplots(1, 3, figsize=(16, 5.4))
    for ax, (title, spec) in zip(axes, specs.items()):
        nodes, edges = _build(spec)
        _cavity(nodes, 0)
        bd = defaultdict(list)
        for i, nd in enumerate(nodes):
            bd[nd["depth"]].append(i)
        pos = {i: ((j - (len(idxs) - 1) / 2) * 1.6, -dpt * 1.4)
               for dpt, idxs in bd.items() for j, i in enumerate(idxs)}
        dmax = max(nd["depth"] for nd in nodes)
        for dpt in range(dmax + 1):
            ax.axhspan(-dpt * 1.4 - 0.6, -dpt * 1.4 + 0.6,
                       color=("#f4f6fb" if dpt % 2 == 0 else "#eef1f8"), zorder=0)
            ax.text(-6.4, -dpt * 1.4, f"slice {dpt}", fontsize=7, color="gray", va="center")
        for a_, b in edges:
            ax.plot([pos[a_][0], pos[b][0]], [pos[a_][1], pos[b][1]], color="#b8c0d0", lw=1, zorder=1)
        for i, nd in enumerate(nodes):
            ax.add_patch(Circle(pos[i], 0.34, color=cm.turbo((nd["m"] - 0.05) / 0.45), ec="k", lw=0.6, zorder=2))
            ax.text(pos[i][0], pos[i][1], f"{nd['m']:.2f}", ha="center", va="center", fontsize=6.5, zorder=3)
        logphi = sum(_contrib(nodes, i) for i in range(len(nodes)))
        ax.set_title(f"{title}\nlog Phi = {logphi:+.4f}", fontsize=10)
        ax.set_xlim(-7, 7)
        ax.set_ylim(-dmax * 1.4 - 1, 1.1)
        ax.axis("off")
    sm = cm.ScalarMappable(cmap="turbo", norm=plt.Normalize(0.05, 0.5))
    sm.set_array([])
    fig.colorbar(sm, ax=axes, fraction=0.02, pad=0.01).set_label(
        "cavity field m_v = z_v/(1 + z_v * sum m_children)")
    plt.suptitle("Cavity foliation of the amplitude recursion (mechanism behind Phi <= 1); "
                 "tie at m = 3/23 ~ 0.130", fontsize=12, y=1.02)
    plt.savefig(path, dpi=150, bbox_inches="tight")
    return path


if __name__ == "__main__":
    print("wrote", render())
