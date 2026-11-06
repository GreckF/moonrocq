# Source this file (inside WSL) to enter the Rocq environment of MoonRocq.
# MoonRocq shares the project-local opam switch of the sibling project
# rocq2mbt (Rocq 9.4+alpha with the extensible extraction API, plus
# rocq-stdlib), because extraction to MoonBit needs the rocq2mbt plugin.
MOONROCQ_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ROCQ2MBT=${ROCQ2MBT:-$(cd "$MOONROCQ_ROOT/../rocq2mbt" && pwd)}
export MOONROCQ_ROOT ROCQ2MBT
source "$ROCQ2MBT/scripts/env.sh"
