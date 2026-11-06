#!/usr/bin/env bash
# Axiom audit: compile tests/Assumptions.v against the dune build and print
# the assumptions of the main theorems (all must be closed).
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$(dirname "$0")/.."
dune build 2>&1
rocq c -R _build/default/theories MoonRocq -o /tmp/Assumptions.vo tests/Assumptions.v 2>&1
rocq c -R _build/default/theories MoonRocq -o /tmp/Examples.vo tests/Examples.v 2>&1
echo "TESTS_OK"
