#!/usr/bin/env python3
"""Audit every source module in a Lake package for nonstandard axioms.

Usage: scripts/axiom-audit.py codelib --report /tmp/codelib-axioms.json

Unlike an umbrella import or a source grep, this checks the transitive axiom
dependencies of every declaration, including private helpers and proof fields
in definitions. Untracked, nonignored Lean sources are included. Nested Lake
packages must be audited separately. A missing module or failed build is an
audit failure, never an exemption. The verifier audit also materializes and
checks both of its proof templates against this checkout's dependencies.
"""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def source_modules(root: Path, package: Path) -> list[str]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others",
         "--exclude-standard", "--", "*.lean"],
        check=True, stdout=subprocess.PIPE,
    )
    modules = set()
    for filename in result.stdout.decode().split("\0"):
        if not filename:
            continue
        path = root / filename
        if not path.is_relative_to(package):
            continue
        parents = path.relative_to(package).parents
        if any(
            parent != Path(".") and any(
                (package / parent / manifest).exists()
                for manifest in ("lakefile.toml", "lakefile.lean")
            )
            for parent in parents
        ):
            continue
        modules.add(".".join(path.relative_to(package).with_suffix("").parts))
    return sorted(modules)


def audit_source(modules: list[str], report: Path) -> str:
    imports = "\n".join(f"import {module}" for module in modules)
    expected = ", ".join(json.dumps(module) for module in modules)
    return imports + f"""
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected : Array String := #[{expected}]
  for moduleName in expected do
    unless env.header.moduleNames.any (fun name => name.toString == moduleName) do
      throwError "Audit import missing: {{moduleName}}"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut violations : Array Json := #[]
  let mut declarations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!.toString
    unless expected.contains moduleName do continue
    checked := checked + 1
    declarations := declarations.push <| Json.mkObj [
      ("module", toJson moduleName), ("name", toJson name.toString),
      ("theorem", toJson info.isTheorem)]
    if info.isTheorem then theorems := theorems + 1
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound
    unless bad.isEmpty do
      violations := violations.push <| Json.mkObj [
        ("module", toJson moduleName),
        ("declaration", toJson name.toString),
        ("axioms", toJson (bad.map Name.toString))]
  let report := Json.mkObj [
    ("modules", toJson expected),
    ("declarations_checked", toJson checked),
    ("theorems_checked", toJson theorems),
    ("declarations", toJson declarations),
    ("violations", toJson violations)]
  liftIO <| IO.FS.writeFile {json.dumps(str(report))} report.pretty
"""


def audit_groups(package: Path, modules: list[str]) -> list[dict]:
    """Split conflicting executable namespaces without skipping any module."""
    with tempfile.TemporaryDirectory(prefix="talos-axiom-audit-") as temp:
        source = Path(temp) / "TalosAxiomAudit.lean"
        report = Path(temp) / "report.json"
        source.write_text(audit_source(modules, report))
        process = subprocess.run(["lake", "env", "lean", str(source)],
                                 cwd=package, text=True, capture_output=True)
        if process.returncode == 0:
            return [json.loads(report.read_text())]
        if "environment already contains" in process.stdout and len(modules) > 1:
            mid = len(modules) // 2
            return (audit_groups(package, modules[:mid]) +
                    audit_groups(package, modules[mid:]))
        print(process.stdout, end="", file=sys.stderr)
        print(process.stderr, end="", file=sys.stderr)
        raise subprocess.CalledProcessError(process.returncode, process.args)


def audit_verifier_templates(root: Path) -> list[dict]:
    """Materialize both scaffolds against this checkout, including the starter proof."""
    template = root / "verifier/template"
    with tempfile.TemporaryDirectory(prefix="talos-template-audit-") as temp:
        package = Path(temp) / "lean"
        shutil.copytree(template / "project/lean", package,
                        ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
        # Use the exact dependency graph under review, not the template's remote main.
        manifest = json.loads((root / "programs/lean/lake-manifest.json").read_text())
        manifest["packagesDir"] = str(root / ".lake/packages")
        for dependency in manifest["packages"]:
            if dependency["type"] == "path":
                dependency["dir"] = str(
                    (root / "programs/lean" / dependency["dir"]).resolve())
        (package / "lake-manifest.json").write_text(json.dumps(manifest))
        (package / "lakefile.toml").write_text(
            'name = "Project"\nversion = "0.1.0"\n'
            f'packagesDir = {json.dumps(str(root / ".lake/packages"))}\n'
            '[[require]]\nname = "CodeLib"\n'
            f'path = {json.dumps(str(root / "codelib"))}\n'
            '[[lean_lib]]\nname = "Project"\n')
        generated = package / "Project/KernelAudit"
        generated.mkdir(parents=True)
        starter = package / "Project/IsEven/Program.lean"
        (generated / "Program.lean").write_text(
            starter.read_text().replace("Project.IsEven", "Project.KernelAudit"))
        for source in (template / "module").rglob("*.lean"):
            target = generated / source.relative_to(template / "module")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source.read_text().replace("MODULE_NAME", "KernelAudit")
                              .replace("CRATE_NAME", "kernel_audit"))
        modules = sorted(".".join(source.relative_to(package).with_suffix("").parts)
                         for source in package.rglob("*.lean")
                         if ".lake" not in source.relative_to(package).parts)
        subprocess.run(["lake", "build", *modules], cwd=package, check=True)
        return audit_groups(package, modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="Lake package directory")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--no-build", action="store_true",
                        help="Use existing package artifacts; templates still build and missing modules fail")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    package = args.package.resolve()
    report = args.report.resolve()
    if not package.is_relative_to(root):
        parser.error("package must be inside this repository")
    if not any((package / name).is_file()
               for name in ("lakefile.toml", "lakefile.lean")):
        parser.error("package has no Lake manifest")
    modules = source_modules(root, package)
    if not modules:
        parser.error("package has no Lean source modules")
    report.parent.mkdir(parents=True, exist_ok=True)
    report.unlink(missing_ok=True)
    template_groups = []
    if package == root / "verifier":
        # These are source templates, not importable modules. Audit their
        # materializations; never treat placeholder syntax as a skipped proof.
        template_groups = audit_verifier_templates(root)
        modules = [module for module in modules
                   if not module.startswith("template.module.")]
    if not args.no_build:
        subprocess.run(["lake", "build", *modules], cwd=package, check=True)
    groups = audit_groups(package, modules) + template_groups
    declarations = [d for group in groups for d in group["declarations"]]
    result = {
        "modules": modules,
        "template_modules": [module for group in template_groups
                             for module in group["modules"]],
        "declarations_checked": len(declarations),
        "theorems_checked": sum(d["theorem"] for d in declarations),
        "violations": [v for group in groups for v in group["violations"]],
    }
    report.write_text(json.dumps(result, indent=2) + "\n")
    violations = result["violations"]
    print(f"{package.relative_to(root)}: {len(modules)} modules, "
          f"{len(result['template_modules'])} template modules, "
          f"{result['declarations_checked']} declarations, "
          f"{result['theorems_checked']} theorems, "
          f"{len(violations)} violations")
    print(f"Full report: {report}")
    return int(bool(violations))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
