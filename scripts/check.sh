#!/usr/bin/env bash
# Build and audit the entire current project; forward verifier options.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/verify.py "$@"
