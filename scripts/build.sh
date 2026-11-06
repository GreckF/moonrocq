#!/usr/bin/env bash
# Build MoonRocq inside WSL with the Rocq 9.4+alpha switch of rocq2mbt (see env.sh).
# Usage (from WSL):   bash scripts/build.sh [dune args...]
# Usage (from Windows Git Bash):
#   MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu -- bash -l /mnt/c/.../moonrocq/scripts/build.sh
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$(dirname "$0")/.."
dune build "$@" 2>&1
echo "BUILD_OK"
