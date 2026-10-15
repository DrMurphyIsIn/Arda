"""Where the WALL-3 track-T scripts read and write.  No absolute home paths in the repo (PR #743 cleanup).

  TELPERION_RH_TEAM      the rh-team checkout whose track outputs the scripts read (default ~/rh-team)
  TELPERION_WALL3_CERTS  where certificates are written and re-read (default: ../certs, the committed copies)

Certificates committed before this change record their original absolute paths in their provenance text; they
are left as they were.  New runs record rh-team inputs as "rh-team:<relative path>" (see ``shown``)."""
import os
import sys
from pathlib import Path

WALL3 = Path(__file__).resolve().parents[1]
RH_TEAM = Path(os.environ.get("TELPERION_RH_TEAM", "~/rh-team")).expanduser()
CERTS = Path(os.environ.get("TELPERION_WALL3_CERTS", str(WALL3 / "certs"))).expanduser()
if str(WALL3) not in sys.path:
    sys.path.insert(0, str(WALL3))         # t3tools


def rh(rel):
    return RH_TEAM / rel


def cert_path(name):
    return CERTS / name


def shown(p):
    """'rh-team:<relative path>' for a path under RH_TEAM, else the path as given."""
    try:
        return "rh-team:" + str(Path(p).resolve().relative_to(RH_TEAM.resolve()))
    except ValueError:
        return str(p)
