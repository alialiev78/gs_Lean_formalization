#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for command_name in bwrap lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 1; }
done
lean_prefix=$(lean --print-prefix)
for binary in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$lean_prefix/bin/$binary" || { echo "Missing bundled kernel tool: $binary" >&2; exit 1; }
done
config_path=$(mktemp)
trap 'rm -f "$config_path"' EXIT
python3 - "$lean_prefix" "$config_path" <<'PYCONFIG'
import json
from pathlib import Path
import sys
prefix, destination = sys.argv[1:]
config = json.loads(Path("comparator.json").read_text())
if "external_kernels" in config:
    raise SystemExit("external_kernels must not be present in the submitted comparator.json")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config))
PYCONFIG
lake comparator --config "$config_path"
