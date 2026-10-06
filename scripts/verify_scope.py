#!/usr/bin/env python3
"""Build selected GS modules and audit their complete local import closure.

Use verify.py for the complete supported-library check.
Private and generated safe kernel declarations are included in the audit.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from audit_source import strip_comments_strings

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
BANNED = ("sorry", "admit", "axiom", "sorryAx", "native_decide", "unsafe", "implemented_by")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_closure(targets: list[str]) -> list[str]:
    modules: set[str] = set()

    def visit(module: str) -> None:
        if module in modules or not module.startswith("GS"):
            return
        if not re.fullmatch(r"GS\w*(?:\.\w+)*", module):
            raise ValueError(f"Invalid project module: {module}")
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise ValueError(f"Missing project module: {module}")
        modules.add(module)
        code = strip_comments_strings(path.read_text())
        for imports in re.findall(r"^(?:public )?import[ \t]+([^\n]+)", code, re.M):
            for dependency in imports.split():
                visit(dependency)

    for target in targets:
        if not target.startswith("GS"):
            raise ValueError("Targets must be project modules.")
        visit(target)
    return sorted(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+")
    parser.add_argument("--output", default=".lake/verification/scoped")
    args = parser.parse_args()
    out = (ROOT / args.output).resolve()
    out.mkdir(parents=True, exist_ok=True)
    status = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Only the listed targets and their complete local import closure",
        "targets": args.targets,
        "kernel_checked_for_this_scope": False,
        "full_project_kernel_checked": False,
        "steps": [],
    }

    def save() -> None:
        (out / "STATUS.json").write_text(json.dumps(status, indent=2) + "\n")

    def run(label: str, command: list[str]) -> str:
        print(f"{label}: {' '.join(command)}", flush=True)
        with (out / f"{label}.log").open("w") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        status["steps"].append({"label": label, "command": command,
                                "exit_code": result.returncode, "log": f"{label}.log"})
        save()
        text = (out / f"{label}.log").read_text(errors="replace")
        if result.returncode:
            raise RuntimeError(f"{label} failed:\n{text[-7000:]}")
        if "sorryAx" in text or re.search(r"declaration uses ['\"]sorry", text):
            raise RuntimeError(f"Incomplete proof in {label}")
        return text

    save()
    try:
        modules = local_closure(args.targets)
        paths = [ROOT / (m.replace(".", "/") + ".lean") for m in modules]
        hashes = {str(p.relative_to(ROOT)): digest(p) for p in paths}
        config = ["lean-toolchain", "lakefile.lean", "lake-manifest.json",
                  "scripts/verify_scope.py", "scripts/audit_source.py"]
        config_hashes = {p: digest(ROOT / p) for p in config}
        for path in paths:
            code = strip_comments_strings(path.read_text())
            for token in BANNED:
                if re.search(r"\b" + token + r"\b", code):
                    raise RuntimeError(f"Forbidden proof construct {token} in {path}")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        pins = {p["name"]: p["rev"] for p in manifest["packages"]}
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        if toolchain != "leanprover/lean4:v4.35.0-rc2" or pins.get("mathlib") != MATHLIB_REV:
            raise RuntimeError("Unexpected Lean/mathlib pin")
        for name, rev in pins.items():
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"],
                cwd=ROOT / ".lake/packages" / name, text=True).strip()
            if actual != rev:
                raise RuntimeError(f"Dependency revision mismatch: {name}")
        status.update(modules=modules, source_sha256=hashes, input_sha256=config_hashes,
                      dependency_revisions=pins, lean_toolchain=toolchain)
        save()
        lake = os.environ.get("LAKE", "lake")
        version = run("version", [lake, "env", "lean", "--version"])
        if not re.search(r"\b4\.35\.0-rc2\b", version):
            raise RuntimeError("The running compiler is not Lean 4.35.0-rc2")
        run("build", [lake, "build", *("+" + name for name in args.targets)])
        audit = out / "Audit.lean"
        audit.write_text("\n".join([
            "module",
            *("import all " + target for target in modules),
            "meta import Lean",
            "open Lean Elab Command", "set_option maxHeartbeats 0", "run_cmd do",
            "  let projectModules : Array Name := #[" + ", ".join("`" + m for m in modules) + "]",
            "  let env ← getEnv",
            "  let names := env.constants.fold (init := (#[] : Array Name)) fun names name info =>",
            "    match env.getModuleIdxFor? name with",
            "    | some idx => if !info.isUnsafe && projectModules.contains env.header.moduleNames[idx]! then names.push name else names",
            "    | none => names",
            '  if names.isEmpty then throwError "No project declarations found"',
            "  let mut theoremCount : Nat := 0",
            "  for name in names do",
            "    match env.checked.get.find? name with",
            '    | none => throwError "Missing kernel declaration: {name}"',
            "    | some (.thmInfo _) => theoremCount := theoremCount + 1",
            "    | some _ => pure ()",
            "  let mut axioms : NameSet := {}",
            "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]",
            "  for name in names do",
            "    for axiomName in (← Lean.collectAxioms name) do",
            '      unless allowed.contains axiomName do throwError "Unexpected axiom: {axiomName}"',
            "      axioms := axioms.insert axiomName",
            '  logInfo m!"AUDIT_DECLARATIONS {names.size}"',
            '  logInfo m!"AUDIT_THEOREMS {theoremCount}"',
            '  logInfo m!"AUDIT_AXIOMS {axioms.toList}"',
            "  for moduleName in projectModules do",
            '    unless (env.getModuleIdx? moduleName).isSome do throwError "Missing module: {moduleName}"',
            '    logInfo m!"AUDIT_MODULE {moduleName}"', "",
        ]))
        output = run("axioms", [lake, "env", "lean", str(audit)])
        if sorted(re.findall(r"^AUDIT_MODULE (\S+)\s*$", output, re.M)) != modules:
            raise RuntimeError("Incomplete module audit")
        groups = re.findall(r"AUDIT_AXIOMS \[([^\]]*)\]", output)
        if len(groups) != 1:
            raise RuntimeError("Missing or ambiguous axiom report")
        axioms = {a.strip() for a in groups[0].split(",") if a.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms: {axioms - ALLOWED_AXIOMS}")
        declarations = re.findall(r"^AUDIT_DECLARATIONS (\d+)\s*$", output, re.M)
        theorems = re.findall(r"^AUDIT_THEOREMS (\d+)\s*$", output, re.M)
        if len(declarations) != 1 or len(theorems) != 1:
            raise RuntimeError("Missing declaration counts")
        if local_closure(args.targets) != modules or any(
                digest(ROOT / p) != h for p, h in (hashes | config_hashes).items()):
            raise RuntimeError("Build inputs changed during verification")
        status.update(kernel_checked_for_this_scope=True,
                      result="scope_built_and_axiom_audited", axioms=sorted(axioms),
                      declarations=int(declarations[0]), theorems=int(theorems[0]),
                      audit_source_sha256=digest(audit))
        save()
        print(f"Verified {len(modules)} modules, {declarations[0]} declarations, "
              f"{theorems[0]} theorems. Full-project certificate: not claimed.", flush=True)
        return 0
    except Exception as error:
        status.update(result="failed", error=str(error))
        save()
        print(str(error), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
