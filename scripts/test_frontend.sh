#!/usr/bin/env bash
# End-to-end tests of the extracted checker, differential against `moon check`:
#   examples/ok/*.mbt           moonrocq accepts, moon accepts
#   examples/bad/*.mbt          moonrocq rejects, moon rejects
#   examples/unsupported/*.mbt  moonrocq rejects (not yet supported), moon accepts
# Requires scripts/extract.sh to have been run.
set -uo pipefail
source "$(dirname "$0")/env.sh"
ROOT=$MOONROCQ_ROOT
(cd "$ROOT/mbt" && moon build --target native --release 2>&1 | grep -e "^Error" -A20) && exit 1
BIN="$ROOT/mbt/_build/native/release/build/cmd/main/main.exe"

REF=$(mktemp -d)
mkdir -p "$REF/main" "$REF/lib"
printf 'name = "moonrocq/ref"\n\nversion = "0.1.0"\n' > "$REF/moon.mod"
printf 'pkgtype(kind: "executable")\n' > "$REF/main/moon.pkg"
: > "$REF/lib/moon.pkg"
# does the official toolchain accept the file?
moon_accepts() {
  rm -f "$REF/main/"*.mbt "$REF/lib/"*.mbt
  if grep -q '^fn main' "$1"; then cp "$1" "$REF/main/main.mbt"; else cp "$1" "$REF/lib/lib.mbt"; echo 'fn main {}' > "$REF/main/main.mbt"; fi
  (cd "$REF" && moon check --target native >/dev/null 2>&1)
}

fail=0; total=0
check() { # dir, expected-ours (0 accept / 1 reject), expected-moon (0/1)
  for f in "$ROOT/examples/$1"/*.mbt; do
    total=$((total + 1))
    out=$("$BIN" "$f"); ours=$?
    moon_accepts "$f"; ref=$?
    [ $ours -ne 0 ] && ours=1; [ $ref -ne 0 ] && ref=1
    if [ $ours -eq "$2" ] && [ $ref -eq "$3" ]; then
      echo "ok    $1/$(basename "$f"): $(echo "$out" | head -1 | sed "s|$ROOT/||")"
    else
      echo "FAIL  $1/$(basename "$f"): moonrocq=$ours moon=$ref"; echo "$out"
      fail=$((fail + 1))
    fi
  done
}
check ok 0 0
check bad 1 1
check unsupported 1 0
rm -rf "$REF"
echo "frontend tests: $total, failed: $fail"
[ $fail -eq 0 ] && echo "FRONTEND_OK"
