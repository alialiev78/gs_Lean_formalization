#!/usr/bin/env python3
"""Build every supported GS module and audit declarations from Lean's environment.

The axiom check covers private and
generated kernel declarations. Unsafe compiler implementation artifacts are
excluded; they cannot occur in kernel proofs. The source scan is an early guard;
successful compilation and the kernel-environment audit are mandatory.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from audit_source import strip_comments_strings

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
BANNED = ("sorry", "admit", "axiom", "sorryAx", "native_decide", "unsafe", "implemented_by")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources() -> list[Path]:
    return sorted((ROOT / "GS").rglob("*.lean")) + sorted(ROOT.glob("GS*.lean"))


def build_order(files: list[Path]) -> list[str]:
    """Order every supported module after its local imports."""
    modules = {str(p.relative_to(ROOT))[:-5].replace("/", "."): p for p in files}
    graph = {}
    for module, path in modules.items():
        code = strip_comments_strings(path.read_text())
        imports = [name for line in re.findall(r"^(?:public )?import[ \t]+([^\n]+)", code, re.M)
                   for name in line.split()]
        missing = [name for name in imports if name.startswith("GS") and name not in modules]
        if missing:
            raise RuntimeError(f"Missing supported imports in {module}: {missing}")
        graph[module] = [name for name in imports if name in modules]
    return list(TopologicalSorter(graph).static_order())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=".lake/verification/full")
    parser.add_argument("--sequential", action="store_true",
                        help="Build project modules one at a time in dependency order")
    args = parser.parse_args()
    out = (ROOT / args.output).resolve()
    out.mkdir(parents=True, exist_ok=True)
    status = {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "kernel_checked": False,
        "scope": "All supported GS modules; all safe kernel declarations, including private and generated ones; experimental/ is excluded",
        "full_supported_library_kernel_checked": False,
        "experimental_kernel_checked": False,
        "article_complete": False,
        "steps": [],
        "build_mode": "sequential" if args.sequential else "lake",
    }

    def save() -> None:
        (out / "STATUS.json").write_text(json.dumps(status, indent=2) + "\n")

    def run(label: str, command: list[str]) -> str:
        print(f"{label}: {' '.join(command)}", flush=True)
        log = out / f"{label}.log"
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("w") as stream:
            with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, text=True,
                                  errors="replace", bufsize=1) as process:
                assert process.stdout is not None
                for line in process.stdout:
                    stream.write(line)
                    stream.flush()
                    sys.stdout.write(line)
                    sys.stdout.flush()
                returncode = process.wait()
        status["steps"].append({"label": label, "command": command,
                                "exit_code": returncode, "log": str(log.relative_to(out))})
        save()
        text = log.read_text(errors="replace")
        if returncode:
            raise RuntimeError(f"{label} failed with exit code {returncode}; see {log}")
        if "sorryAx" in text or re.search(r"declaration uses ['\"]sorry", text):
            raise RuntimeError(f"Incomplete proof in {label}")
        return text

    save()
    try:
        files = sources()
        hashes = {str(p.relative_to(ROOT)): digest(p) for p in files}
        hashes.update({name: digest(ROOT / name) for name in
                       ("lean-toolchain", "lakefile.lean", "lake-manifest.json",
                        "scripts/verify.py", "scripts/audit_source.py")})
        modules = [str(p.relative_to(ROOT))[:-5].replace("/", ".") for p in files]
        for path in files:
            code = strip_comments_strings(path.read_text())
            for token in BANNED:
                if re.search(r"\b" + token + r"\b", code):
                    raise RuntimeError(f"Forbidden proof construct {token} in {path}")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        pins = {p["name"]: p.get("rev", "") for p in manifest["packages"]}
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        if toolchain != "leanprover/lean4:v4.35.0-rc2" or pins.get("mathlib") != MATHLIB_REV:
            raise RuntimeError("Unexpected Lean/mathlib version")
        experimental_files = sorted((ROOT / "experimental").rglob("*.lean"))
        status.update(source_sha256=hashes, local_modules=len(modules),
                      excluded_experimental_modules=len(experimental_files),
                      excluded_experimental_source_sha256={
                          str(p.relative_to(ROOT)): digest(p) for p in experimental_files},
                      dependency_revisions=pins, lean_toolchain=toolchain)
        lake = os.environ.get("LAKE", "lake")
        version = run("version", [lake, "env", "lean", "--version"])
        if not re.search(r"\b4\.35\.0-rc2\b", version):
            raise RuntimeError("The running compiler is not Lean 4.35.0-rc2")
        if args.sequential:
            for index, module in enumerate(build_order(files), 1):
                print(f"Building module {index}/{len(modules)}: {module}", flush=True)
                # '+' selects the module even when a library has the same name.
                run(f"build/{module}", [lake, "build", "+" + module])
        else:
            run("build", [lake, "build", "GS", "GSChecked"])
        audit = out / "Audit.lean"
        audit.write_text("\n".join([
            "module",
            *("import all " + module for module in modules),
            "import Lean",
            "", "open Lean Elab Command", "set_option maxHeartbeats 0", "run_cmd do",
            "  let projectModules : Array Name := #[" + ", ".join("`" + m for m in modules) + "]",
            "  let env ← getEnv",
            "  let names := env.constants.fold (init := (#[] : Array Name)) fun names name info =>",
            "    match env.getModuleIdxFor? name with",
            "    | some idx => if !info.isUnsafe && projectModules.contains env.header.moduleNames[idx]! then names.push name else names",
            "    | none => names",
            "  if names.isEmpty then throwError \"No project declarations were found\"",
            "  let mut theoremCount : Nat := 0",
            "  for name in names do",
            "    match env.checked.get.find? name with",
            "    | none => throwError \"Missing kernel declaration: {name}\"",
            "    | some (.thmInfo _) => theoremCount := theoremCount + 1",
            "    | some _ => pure ()",
            "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]",
            "  let mut axioms : NameSet := {}",
            "  for name in names do",
            "    for axiomName in (← Lean.collectAxioms name) do",
            "      unless allowed.contains axiomName do throwError \"Unexpected axiom: {axiomName} in {name}\"",
            "      axioms := axioms.insert axiomName",
            '  logInfo m!"AUDIT_DECLARATIONS {names.size}"',
            '  logInfo m!"AUDIT_THEOREMS {theoremCount}"',
            '  logInfo m!"AUDIT_AXIOMS {axioms.toList}"',
            "  for moduleName in projectModules do",
            "    unless (env.getModuleIdx? moduleName).isSome do throwError \"Missing module: {moduleName}\"",
            '    logInfo m!"AUDIT_MODULE {moduleName}"',
            "", "example : GS.Specifications.NonManifoldGoal := GS.NonmanifoldTopology.nonManifold",
            "example : GS.Specifications.ConeProductNonManifoldGoal := GS.NonmanifoldTopology.coneProductNonManifold",
            "",
        ]))
        output = run("axioms", [lake, "env", "lean", str(audit)])
        audited = re.findall(r"^AUDIT_MODULE (\S+)\s*$", output, re.M)
        if sorted(audited) != sorted(modules):
            raise RuntimeError("Incomplete module audit")
        groups = re.findall(r"AUDIT_AXIOMS \[([^\]]*)\]", output)
        if len(groups) != 1:
            raise RuntimeError("Missing or ambiguous axiom report")
        axioms = {a.strip() for a in groups[0].split(",") if a.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms: {axioms - ALLOWED_AXIOMS}")
        counts = re.findall(r"^AUDIT_DECLARATIONS (\d+)\s*$", output, re.M)
        theorem_counts = re.findall(r"^AUDIT_THEOREMS (\d+)\s*$", output, re.M)
        if len(counts) != 1 or len(theorem_counts) != 1:
            raise RuntimeError("Missing declaration count")
        if sources() != files or any(digest(ROOT / p) != value for p, value in hashes.items()):
            raise RuntimeError("Build inputs changed during verification; rerun after edits finish")
        status.update(kernel_checked=True, full_supported_library_kernel_checked=True,
                      result="all_modules_built_and_axiom_audited",
                      axioms=sorted(axioms), declarations=int(counts[0]),
                      theorems_including_generated=int(theorem_counts[0]),
                      audit_sha256=digest(audit),
                      nonmanifold_original_specification_checked=True,
                      cone_original_specification_checked=True)
        print(f"Verified {len(modules)} modules and {counts[0]} kernel declarations.", flush=True)
    except Exception as error:
        status.update(result="failed", error=str(error))
        print(str(error), flush=True)
        save()
        return 1
    save()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
