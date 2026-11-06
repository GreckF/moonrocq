#!/usr/bin/env bash
# Extract the checker to MoonBit (inside WSL):
#   1. build the MoonRocq library and the rocq2mbt plugin;
#   2. fetch the MoonBit dependencies of mbt/ (the official parser);
#   3. mbti2rocq: parser interface -> extraction/Parser.v;
#   4. compile extraction/Driver.v, which writes mbt/checker/moonrocq.mbt.
set -euo pipefail
source "$(dirname "$0")/env.sh"
ROOT=$MOONROCQ_ROOT
cd "$ROOT" && dune build 2>&1
(cd "$ROCQ2MBT" && dune build 2>&1)

MBTI2ROCQ="$ROCQ2MBT/mbt/mbti2rocq/_build/native/release/build/cmd/main/main.exe"
[ -x "$MBTI2ROCQ" ] || (cd "$ROCQ2MBT/mbt/mbti2rocq" && moon build --target native --release)

PARSER_MBTI="$ROOT/mbt/.mooncakes/moonbitlang/parser/pkg.generated.mbti"
[ -f "$PARSER_MBTI" ] || (cd "$ROOT/mbt" && moon check >/dev/null 2>&1 || true)
"$MBTI2ROCQ" "$PARSER_MBTI" -o "$ROOT/extraction/Parser.v"

export OCAMLPATH="$ROCQ2MBT/_build/install/default/lib${OCAMLPATH:+:$OCAMLPATH}"
FLAGS=(-Q "$ROCQ2MBT/_build/default/theories" RocqMbt
       -R "$ROOT/_build/default/theories" MoonRocq
       -R "$ROOT/extraction" MoonRocqExtr)
cd "$ROOT/extraction"
rocq c "${FLAGS[@]}" Parser.v 2>&1
rocq c "${FLAGS[@]}" Driver.v 2>&1
echo "EXTRACT_OK"
