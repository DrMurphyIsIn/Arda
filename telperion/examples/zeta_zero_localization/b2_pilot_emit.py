#!/usr/bin/env python3
"""B2 sharding pilot emitter.

Materialises the sharded lake layout at BOUNDED scale (zzl_core + the
(375000,400000] block) as REAL lake packages, using the disk-safe wiring proved
out during the pilot:

  * source layout = `srcDir = ".."` (the package lakefile lives in a subdir of the
    island, but reads the flat `.lean` files IN PLACE from the island root).  No
    file moves, no symlinks of sources; module identity is preserved so every
    existing `import Foo` keeps resolving.
  * dependency reuse = each package copies the monolith's `lake-manifest.json`
    (so all dep revs match exactly) AND symlinks its `.lake/packages` at the
    monolith's already-built packages dir.  Result: mathlib + toolchain deps are
    reused IN PLACE -- zero re-clone, zero re-fetch, zero Mathlib rebuild.
  * zzl_core requires ZeroFreeBridge too (its ZetaZeroConfinement /
    AllZerosUpToHeight modules import DlvpZetaZeroFree), in addition to mathlib.

This is a pilot-scoped generator; the production path is `campaign.py
register-lakefile --sharded` (whose emit_block_lakefile this mirrors, plus the
disk-safe require wiring).  conjecture1_proved = False.
"""
from __future__ import annotations
import json
import os
import shutil
from pathlib import Path


def _relpath(target: Path, start: Path) -> str:
    return os.path.relpath(target, start)

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE / "lean"
MONO_MANIFEST = LEAN_DIR / "lake-manifest.json"
MONO_PACKAGES = LEAN_DIR / ".lake" / "packages"
MONO_BUILD_LIB = LEAN_DIR / ".lake" / "build" / "lib" / "lean"
ZFB_DIR = HERE.parent / "zero_free_bridge" / "lean"
TOOLCHAIN = (LEAN_DIR / "lean-toolchain").read_text()
MATHLIB_REV = "v4.32.0"
CORE_PKG = "zzl_core"
LAKE_BLOCK = 25_000  # height per lake package (charter B2), matches campaign.py

# 16 height-independent core modules (import closure of the block modules minus
# the bands/capstones; verified present as flat .lean files in the island root).
CORE_MODULES = [
    "LambdaLineReal", "XiLineZeros", "WindingCount", "BoxArgPrinciple",
    "BoxArgPrincipleZeta", "RigorousWinding", "BlaschkeBox", "BoxLocalization",
    "RHInBoxCore", "RHInBoxAnalytic", "RHInBox", "RHInBoxBands",
    "DiffractionCore", "ZetaZeroConfinement", "AllZerosUpToHeight", "TuringBand",
]


def _capstone_bands(top: int) -> list[str]:
    """Band modules imported by AllZeros_h<top> (its segment's RHInBox* imports)."""
    f = LEAN_DIR / f"AllZeros_h{top}.lean"
    bands = []
    for ln in f.read_text().splitlines():
        ln = ln.strip()
        if ln.startswith("import RHInBox"):
            bands.append(ln[len("import "):])
    return bands


def block_modules(from_top: int, to_top: int) -> tuple[list[str], list[str]]:
    """(band_modules, capstone_modules) for capstone tops in [from_top, to_top]."""
    caps = list(range(from_top, to_top + 1, 1000))
    bands: set[str] = set()
    for t in caps:
        bands.update(_capstone_bands(t))
    return sorted(bands), [f"AllZeros_h{t}" for t in caps]


def _pkg_wiring(pkg_dir: Path, require_core: bool = False,
               extra_path_deps: list[tuple[str, str]] | None = None) -> None:
    """Copy the monolith manifest + symlink the built packages dir so all deps
    resolve to the existing checkouts (zero re-clone).  Also drop the toolchain
    file so elan pins v4.32.0.  All build-lib search paths (ZFB, zzl_core, prior
    boundary) come from `[[require]]` path deps -- lake derives LEAN_PATH from the
    require graph, so no LEAN_PATH sidecar is needed."""
    pkg_dir.mkdir(parents=True, exist_ok=True)
    (pkg_dir / "lean-toolchain").write_text(TOOLCHAIN)
    # Copy the monolith manifest, but rewrite the ZeroFreeBridge path dep so it
    # resolves relative to THIS package dir (one level deeper than the monolith
    # root).  All other deps are git/scope-based and resolve via the symlinked
    # packages dir, so they need no rewrite.
    manifest = json.loads(MONO_MANIFEST.read_text())
    zfb_rel = _relpath(ZFB_DIR, pkg_dir)
    for p in manifest.get("packages", []):
        if p.get("name") == "ZeroFreeBridge" and p.get("type") == "path":
            p["dir"] = zfb_rel
    new_deps: list[tuple[str, str]] = []
    if require_core:
        new_deps.append((CORE_PKG, _relpath(LEAN_DIR / CORE_PKG, pkg_dir)))
    for name, rel in (extra_path_deps or []):
        # rel is relative to the package's own lakefile; store the manifest dir
        # relative to the same package dir.
        new_deps.append((name, rel))
    for name, rel in new_deps:
        manifest["packages"].insert(0, {
            "type": "path", "scope": "", "name": name,
            "manifestFile": "lake-manifest.json", "inherited": False,
            "dir": rel, "configFile": "lakefile.toml",
        })
    (pkg_dir / "lake-manifest.json").write_text(json.dumps(manifest, indent=1))
    lake = pkg_dir / ".lake"
    lake.mkdir(exist_ok=True)
    link = lake / "packages"
    if not link.exists():
        link.symlink_to(MONO_PACKAGES)


def emit_core() -> Path:
    pkg = LEAN_DIR / CORE_PKG
    lines = [f'name = "{CORE_PKG}"\n']
    targets = ", ".join(f'"{m}"' for m in CORE_MODULES)
    lines.append(f"defaultTargets = [{targets}]\n")
    lines.append('srcDir = ".."\n\n')
    lines.append('[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
                 f'rev = "{MATHLIB_REV}"\n\n')
    lines.append('[[require]]\nname = "ZeroFreeBridge"\n'
                 'path = "../../../zero_free_bridge/lean"\n\n')
    for m in CORE_MODULES:
        lines.append(f'[[lean_lib]]\nname = "{m}"\n')
    (pkg / "lakefile.toml").parent.mkdir(parents=True, exist_ok=True)
    _pkg_wiring(pkg)
    (pkg / "lakefile.toml").write_text("".join(lines))
    return pkg


def emit_prior_boundary(top: int) -> Path:
    """Emit the PRIOR block's boundary package `ZetaBands_h<top-25000>/` that the
    pilot block chains to.

    A block's lowest capstone imports the prior block's TOP capstone, which itself
    chains all the way down to AllZeros_h100 -- so the cross-block edge needs the
    ENTIRE prior chain's oleans available (not just one).  lake ignores a pre-set
    LEAN_PATH and derives its own from the require graph, so the prior chain must
    come from a REQUIRED package's build lib.

    In production that is the real prior block package.  In the pilot we synthesise
    it: a package declaring only the prior top capstone as its lean_lib, with its
    `.lake/build/lib/lean` symlinked at the MONOLITH build lib (which already holds
    the whole prior chain).  lake `Replay`s those oleans (reuses, never recompiles)
    and exposes the dir on LEAN_PATH for the requiring block."""
    prior_top = _prior_block_top(top)
    pkg = LEAN_DIR / f"ZetaBands_h{prior_top}"
    cap = f"AllZeros_h{prior_top}"
    lines = [f'name = "ZetaBands_h{prior_top}"\n',
             f'defaultTargets = ["{cap}"]\n', 'srcDir = ".."\n\n',
             '[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
             f'rev = "{MATHLIB_REV}"\n\n',
             '[[require]]\nname = "ZeroFreeBridge"\n'
             'path = "../../../zero_free_bridge/lean"\n\n',
             f'[[lean_lib]]\nname = "{cap}"\n']
    pkg.mkdir(parents=True, exist_ok=True)
    _pkg_wiring(pkg)
    (pkg / "lakefile.toml").write_text("".join(lines))
    # Expose the whole prior chain by symlinking this package's build lib at the
    # monolith build lib (which holds AllZeros_h100..h<prior_top> + all their bands).
    build_lib = pkg / ".lake" / "build" / "lib"
    build_lib.mkdir(parents=True, exist_ok=True)
    lean_link = build_lib / "lean"
    if not lean_link.exists():
        lean_link.symlink_to(MONO_BUILD_LIB)
    return pkg


def emit_block(top: int, bands: list[str], caps: list[str]) -> Path:
    """Emit ZetaBands_h<top>/.  Requires zzl_core, ZeroFreeBridge, mathlib, and
    the prior boundary package (for the cross-block chain edge)."""
    pkg = LEAN_DIR / f"ZetaBands_h{top}"
    prior_top = _prior_block_top(top)
    mods = bands + caps
    lines = [f'name = "ZetaBands_h{top}"\n']
    targets = ", ".join(f'"{m}"' for m in mods)
    lines.append(f"defaultTargets = [{targets}]\n")
    lines.append('srcDir = ".."\n\n')
    lines.append('[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
                 f'rev = "{MATHLIB_REV}"\n\n')
    lines.append('[[require]]\nname = "ZeroFreeBridge"\n'
                 'path = "../../../zero_free_bridge/lean"\n\n')
    lines.append(f'[[require]]\nname = "{CORE_PKG}"\npath = "../{CORE_PKG}"\n\n')
    lines.append(f'[[require]]\nname = "ZetaBands_h{prior_top}"\n'
                 f'path = "../ZetaBands_h{prior_top}"\n\n')
    for m in mods:
        lines.append(f'[[lean_lib]]\nname = "{m}"\n')
    pkg.mkdir(parents=True, exist_ok=True)
    _pkg_wiring(pkg, require_core=True,
                extra_path_deps=[(f"ZetaBands_h{prior_top}",
                                  f"../ZetaBands_h{prior_top}")])
    (pkg / "lakefile.toml").write_text("".join(lines))
    return pkg


def _prior_block_top(top: int) -> int:
    """Top capstone of the block below `top` (the cross-block chain edge).  For a
    25k block ending at `top`, its lowest capstone is at top-24000, which imports
    top-25000 = the prior block's top capstone."""
    return top - LAKE_BLOCK


def main() -> None:
    core = emit_core()
    print(f"emitted {core}  ({len(CORE_MODULES)} core modules)")
    prior = emit_prior_boundary(400000)
    print(f"emitted {prior}  (prior-block boundary; build lib -> monolith, "
          "exposes the whole prior chain via Replay)")
    bands, caps = block_modules(376000, 400000)
    blk = emit_block(400000, bands, caps)
    print(f"emitted {blk}  ({len(bands)} bands + {len(caps)} capstones "
          f"= {len(bands) + len(caps)} modules)")
    print("cross-block chain edge AllZeros_h375000 resolved via required package "
          "ZetaBands_h375000 (production: the real prior block package)")


if __name__ == "__main__":
    main()
