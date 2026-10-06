#!/usr/bin/env python3
"""Fetch mathlib cache entries required by this project's supported sources."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
files = list((root / "GS").rglob("*.lean")) + list(root.glob("*.lean"))
modules = set()
for path in files:
    for line in re.findall(r"^(?:public )?import[ \t]+([^\n]+)", path.read_text(), re.M):
        modules.update(name for name in line.split() if name.startswith("Mathlib."))
if not modules:
    raise SystemExit("No direct mathlib imports found")
raise SystemExit(subprocess.call(["lake", "exe", "cache", "get", *sorted(modules)], cwd=root))
