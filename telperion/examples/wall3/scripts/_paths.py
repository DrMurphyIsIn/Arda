"""Where the WALL-3 track-T scripts read and write.  No absolute home paths in the repo (PR #743 cleanup).

  TELPERION_RH_TEAM                 the rh-team checkout whose track outputs the scripts read (default ~/rh-team)
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


def rh(rel):
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
    """'rh-team:<relative path>' for a path under RH_TEAM, else the path as given."""
    try:
        return "rh-team:" + str(Path(p).resolve().relative_to(RH_TEAM.resolve()))
    except ValueError:
        return str(p)
