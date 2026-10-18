#!/usr/bin/env bash
# SPDX-License-Identifier: CC0-1.0
#
# Build the Lean library: `./build.sh [lake build arguments]`.
#
# Optional resource limits, for shared machines:
#   LEAN_MEM=8G            cap memory through `systemd-run --user --scope` (when available)
#   LEAN_NUM_THREADS=2     limit Lean's worker threads
# Without LEAN_MEM this is `nice lake build`.
set -euo pipefail
cd "$(dirname "$0")"
if [ -n "${LEAN_MEM:-}" ] && command -v systemd-run >/dev/null 2>&1; then
  exec systemd-run --user --scope -q -p MemoryMax="$LEAN_MEM" nice -n 10 lake build "$@"
fi
exec nice -n 10 lake build "$@"
