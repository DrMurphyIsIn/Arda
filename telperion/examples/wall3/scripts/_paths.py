"""Where the WALL-3 track-T scripts read and write.  No absolute home paths in the repo (PR #743 cleanup).

  TELPERION_RH_TEAM                 the rh-team checkout whose track outputs the scripts read (default ~/rh-team).
                                    Unless it is set explicitly, rh() prefers the copy vendored under ../inputs/
                                    (same relative layout), so the scripts rerun from the repo alone.
  TELPERION_WALL3_CERTS             where certificates are WRITTEN (default ~/.cache/telperion/wall3-certs, a
                                    scratch dir outside the repo)
  TELPERION_WRITE_COMMITTED_CERTS=1 write into ../certs, OVERWRITING the committed copies (deliberate regeneration
                                    only; ignored if TELPERION_WALL3_CERTS is set)

The default used to be ../certs, so a rerun silently overwrote committed cert JSON (bb, review of PR #744).
Certificates a script READS as inputs (cert_read) come from the write dir if it already holds that file, else
from the committed copy.  Certificates committed before the path cleanup record their original absolute paths in
their provenance text; they are left as they were.  New runs record rh-team inputs as "rh-team:<path>" (shown)."""
import os
import sys
from pathlib import Path

WALL3 = Path(__file__).resolve().parents[1]
COMMITTED = WALL3 / "certs"
RH_TEAM = Path(os.environ.get("TELPERION_RH_TEAM", "~/rh-team")).expanduser()
if os.environ.get("TELPERION_WALL3_CERTS"):
    CERTS = Path(os.environ["TELPERION_WALL3_CERTS"]).expanduser()
elif os.environ.get("TELPERION_WRITE_COMMITTED_CERTS") == "1":
    CERTS = COMMITTED
else:
    CERTS = Path("~/.cache/telperion/wall3-certs").expanduser()
if str(WALL3) not in sys.path:
    sys.path.insert(0, str(WALL3))         # t3tools
_announced = False


VENDORED = WALL3 / "inputs"
_RH_EXPLICIT = bool(os.environ.get("TELPERION_RH_TEAM"))


def rh(rel):
    """An rh-team input: the vendored copy ../inputs/<rel> if it exists (and TELPERION_RH_TEAM is not set
    explicitly), else RH_TEAM/<rel>.  Globs are resolved against the same choice of root."""
    v = VENDORED / rel
    if not _RH_EXPLICIT and (v.exists() or (any(ch in rel for ch in "*?[") and v.parent.is_dir())):
        return v
    return RH_TEAM / rel


def cert_path(name):
    """Path to WRITE certificate ``name``."""
    global _announced
    CERTS.mkdir(parents=True, exist_ok=True)
    if not _announced:
        what = "the COMMITTED copies" if CERTS.resolve() == COMMITTED.resolve() else "a scratch dir"
        print(f"[_paths] writing certificates to {CERTS} ({what})", file=sys.stderr)
        _announced = True
    return CERTS / name


def cert_read(name):
    """Path to READ certificate ``name`` as an input: the write dir's copy if present, else the committed one."""
    p = CERTS / name
    return p if p.exists() else COMMITTED / name


def shown(p):
    """'rh-team:<relative path>' for a path under RH_TEAM or under the vendored ../inputs/ mirror of it, else the
    path as given."""
    for root in (RH_TEAM, VENDORED):
        try:
            return "rh-team:" + str(Path(p).resolve().relative_to(root.resolve()))
        except ValueError:
            pass
    return str(p)
