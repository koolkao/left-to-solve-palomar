#!/usr/bin/env bash
# Build one entry and judge Solution against Challenge with the toolchain's `lake comparator`, adding the
# bundled NanoDa and con-ron kernels as Palomar does (see PalomarTemplate scripts/verify-comparator.sh).
# Usage: scripts/verify-entry.sh <entry> [--no-sandbox]
#   --no-sandbox passes --inadvisably-no-sandbox, for machines without bwrap (macOS); only for code you trust.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root/palomar/$1"
extra=(); [ "${2:-}" = "--no-sandbox" ] && extra=(--inadvisably-no-sandbox)
prefix=$(lean --print-prefix)
cfg=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX"); trap 'rm -f "$cfg"' EXIT
python3 - comparator.json "$cfg" "$prefix" <<'PY'
import json, sys
src, dst, prefix = sys.argv[1:]
c = json.load(open(src)); c.pop("enable_nanoda", None)
c["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"], "con-ron": [f"{prefix}/bin/con-ron"]}
json.dump(c, open(dst, "w"), indent=2)
PY
lake exe cache get
lake build
lake comparator --config "$cfg" ${extra[@]+"${extra[@]}"}
