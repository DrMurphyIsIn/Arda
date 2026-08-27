#!/usr/bin/env bash
# landrun-CLI-compatible sandbox wrapper backed by bubblewrap (bwrap).
#
# WHY: openai/ten-proofs Comparator wraps its children (lake build, lean4export,
# nanoda) in landrun (github.com/Zouuup/landrun) for isolation, invoking
#   <COMPARATOR_LANDRUN> <landrun-flags...> <cmd> <cmd-args...>
# Real landrun uses urfave/cli, whose Args().Slice() STRIPS the `--` separator,
# which silently corrupts lean4export's `<module> -- <constants>` contract.  This
# wrapper accepts the same flag surface but (a) preserves `--`, and (b) provides a
# REAL sandbox via bwrap (mount namespace + network unshare).
#
# USE: point COMPARATOR_LANDRUN at this script when judging UNTRUSTED third-party
# solutions.  For verifying your OWN emitted proofs the lighter no-sandbox shim is
# enough (the kernel replay is the real guarantee).
#
# Flag translation (landrun -> bwrap):
#   --ro P / --rox P   -> --ro-bind P P      (readable; exec allowed on ro binds)
#   --rw P / --rwx P    -> --bind P P         (writable)
#   --env K            -> --setenv K "$K"    (pass current value)
#   --env K=V          -> --setenv K V
#   --best-effort, -ldd, -add-exec, --log-level X -> ignored
# Base hardening (applied AFTER the binds so they override the ro-root):
#   fresh /proc, /dev, writable /tmp; --unshare-net (no network),
#   --die-with-parent, --new-session, --clearenv (+ only the --env vars).
#
# Dry run: set BWRAP=echo to print the bwrap command instead of running it.
set -euo pipefail
BWRAP="${BWRAP:-bwrap}"

args=("$@"); i=0; n=${#args[@]}
binds=(); setenvs=()
while (( i < n )); do
  a="${args[$i]}"
  case "$a" in
    --ro|--rox) p="${args[$((i+1))]}"; binds+=( --ro-bind "$p" "$p" ); i=$((i+2)) ;;
    --rw|--rwx) p="${args[$((i+1))]}"; binds+=( --bind    "$p" "$p" ); i=$((i+2)) ;;
    --env)
      v="${args[$((i+1))]}"
      if [[ "$v" == *"="* ]]; then setenvs+=( --setenv "${v%%=*}" "${v#*=}" )
      else setenvs+=( --setenv "$v" "${!v:-}" ); fi
      i=$((i+2)) ;;
    --env=*) kv="${a#--env=}"; setenvs+=( --setenv "${kv%%=*}" "${kv#*=}" ); i=$((i+1)) ;;
    --log-level) i=$((i+2)) ;;
    --*=*) i=$((i+1)) ;;
    -*)    i=$((i+1)) ;;   # --best-effort, -ldd, -add-exec (bool flags)
    *)     break ;;        # first non-flag = the command
  esac
done
cmd=( "${args[@]:$i}" )    # command + its args, verbatim (INCLUDING `--`)

exec "$BWRAP" \
  "${binds[@]}" \
  --proc /proc --dev /dev --tmpfs /tmp \
  --die-with-parent --unshare-net --new-session \
  --clearenv "${setenvs[@]}" \
  -- "${cmd[@]}"
