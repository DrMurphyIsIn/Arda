#!/usr/bin/env python3
"""Split R3Cert between hosted CI (16 GB runner) and the self-hosted Mac (proof-lean-heavy.yml).

HEAVY = the G149 envelope-certificate fragments R3Cert.BGEnvCert.G149.Frag<C> plus every module
that imports one of them transitively (computed from the `import` lines, so it stays exact as
the library changes). Each Frag is a single `decide +kernel` capCheck whose retained kernel
reduction does not fit in 16 GB (measured 2026-10-08, /usr/bin/time -l, lean -j 4: Frag6
25.4 GB, Frag7 28.4 GB, Frag12 42.2 GB max RSS; Frag16/Frag22 larger). Hosted CI builds
everything else; the Mac builds HEAVY one module at a time and then re-runs the full,
unfiltered checks.

  heavy_bg.py heavy                 HEAVY modules, in dependency order (one per line)
  heavy_bg.py hosted-targets        every other R3Cert/**.lean module (one per line)
  heavy_bg.py hosted-guard IN OUT DROPPED
      Write OUT = IN (AxiomGuard.lean) with each `import <HEAVY>` replaced by the non-HEAVY
      modules it reaches (so every other directive still resolves exactly as before) and each
      `#print axioms <name>` whose declaration lives in a HEAVY module (name starts with
      `<module>.`) removed. The removed names go to DROPPED. Anything else unresolved still
      makes `lean OUT` fail, so this cannot hide a missing declaration.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEED = re.compile(r"^R3Cert\.BGEnvCert\.G149\.Frag\d+$")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def graph():
    g = {}
    for d, _, fs in os.walk(os.path.join(ROOT, "R3Cert")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                with open(p, encoding="utf-8") as fh:
                    g[m] = IMPORT.findall(fh.read())
    return g


def heavy(g):
    rev = {}
    for m, imps in g.items():
        for i in imps:
            rev.setdefault(i, set()).add(m)
    hv = {m for m in g if SEED.match(m)}
    st = list(hv)
    while st:
        for y in rev.get(st.pop(), ()):
            if y not in hv:
                hv.add(y)
                st.append(y)
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for i in sorted(g.get(m, [])):
            if i in hv:
                visit(i)
        order.append(m)

    for m in sorted(hv, key=lambda s: [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]):
        visit(m)
    return order


def frontier(g, hv, m, acc):
    for i in g.get(m, []):
        if i in hv:
            frontier(g, hv, i, acc)
        elif i not in acc:
            acc.append(i)


def main():
    g = graph()
    hv = heavy(g)
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "heavy":
        print("\n".join(hv))
    elif cmd == "hosted-targets":
        hs = set(hv)
        print("\n".join(sorted(m for m in g if m not in hs)))
    elif cmd == "hosted-guard":
        src, out, dropped_path = sys.argv[2:5]
        hs = set(hv)
        lines, dropped, seen_imports = [], [], set()
        with open(src, encoding="utf-8") as fh:
            text = fh.read()
        for line in text.splitlines():
            mi = re.match(r"^import\s+(\S+)\s*$", line)
            mp = re.match(r"^#print\s+axioms\s+(\S+)", line)
            if mi:
                mods = [mi.group(1)]
                if mi.group(1) in hs:
                    mods = []
                    frontier(g, hs, mi.group(1), mods)
                for m in mods:
                    if m not in seen_imports:
                        seen_imports.add(m)
                        lines.append(f"import {m}")
                continue
            if mp and any(mp.group(1).startswith(m + ".") for m in hs):
                dropped.append(mp.group(1))
                lines.append(f"-- [hosted CI] moved to proof-lean-heavy.yml: {line}")
                continue
            lines.append(line)
        with open(out, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines) + "\n")
        with open(dropped_path, "w", encoding="utf-8") as fh:
            fh.write("".join(n + "\n" for n in dropped))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
