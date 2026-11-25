#!/bin/bash
# usage: bash repro/overlay.sh FIVE_SPEED_CHECKOUT [--check]
#
# This repository ships only the Lean modules that are NOT in the public five-speed archive
# (https://github.com/ElVec1o/lonely-runner-five-speed, version 1.0.2, DOI 10.5281/zenodo.24443755).
# The import closure of LRSpectrumFull.Sext6.Release is the 17,597 modules of that archive's closure (after its
# repro/regen_data.sh has restored the omitted generated modules) plus the 1,353 modules of this repository.
# This script copies lean/LRSpectrumFull/ of this repository into FIVE_SPEED_CHECKOUT/lean/LRSpectrumFull/.
# It never overwrites an existing file; if a target file exists it stops. With --check it only reports.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"
FS="${1:?usage: overlay.sh FIVE_SPEED_CHECKOUT [--check]}"
FS="$(cd "$FS" 2>/dev/null && pwd)" || { echo "checkout path not found"; exit 2; }
MODE="${2:-}"
[ -f "$FS/lean/lakefile.toml" ] || { echo "not a five-speed checkout: $FS/lean/lakefile.toml missing"; exit 2; }
[ -f "$FS/lean/LRSpectrumFull/L5S5/FiveSpeedOfTree.lean" ] || { echo "five-speed module L5S5/FiveSpeedOfTree.lean missing"; exit 2; }
cmp -s "$FS/lean/lake-manifest.json" "$HERE/lean/lake-manifest.json" || { echo "lake-manifest.json differs: Mathlib pin must be identical"; exit 2; }
cmp -s "$FS/lean/lean-toolchain" "$HERE/lean/lean-toolchain" || { echo "lean-toolchain differs"; exit 2; }
n=0; clash=0
while IFS= read -r rel; do
  n=$((n+1))
  if [ -e "$FS/lean/$rel" ]; then clash=$((clash+1)); echo "EXISTS: $rel"; fi
done < <(cd "$HERE/lean" && find LRSpectrumFull -type f -name '*.lean' | LC_ALL=C sort)
echo "modules in this repository: $n; already present in the target: $clash"
[ "$clash" -eq 0 ] || { echo "stop: refusing to overwrite"; exit 3; }
[ "$MODE" = "--check" ] && { echo "check only: nothing copied"; exit 0; }
(cd "$HERE/lean" && find LRSpectrumFull -type f -name '*.lean' -print0 | LC_ALL=C sort -z | xargs -0 -I{} sh -c 'mkdir -p "$1/$(dirname "$2")" && cp "$2" "$1/$2"' _ "$FS/lean" {})
echo "copied $n modules into $FS/lean/LRSpectrumFull"
echo "next (from $FS/lean, one module at a time; never a bare 'lake build'):"
echo "  lake build LRSpectrumFull.Sext6.Gap.All          # the Gap library, cheap check"
echo "  lake build LRSpectrumFull.Sext6.Release          # everything (long; see README)"
