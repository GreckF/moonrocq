#!/usr/bin/env bash
# Build MoonRocq inside WSL with the opam switch that has Rocq 9.1.
# Usage (from WSL):   bash scripts/build.sh [dune args...]
# Usage (from Windows Git Bash):
#   MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu -- bash -l /mnt/c/.../moonrocq/scripts/build.sh
set -euo pipefail
eval "$(opam env --switch=5.5.0 --set-switch)"
cd "$(dirname "$0")/.."
dune build "$@" 2>&1
echo "BUILD_OK"
