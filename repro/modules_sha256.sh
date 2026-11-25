#!/bin/bash
# usage: bash repro/modules_sha256.sh   -> prints "sha256  path" for every shipped module (compare with MODULES.sha256)
cd "$(dirname "$0")/../lean" && find LRSpectrumFull -type f -name '*.lean' | LC_ALL=C sort | xargs shasum -a 256
