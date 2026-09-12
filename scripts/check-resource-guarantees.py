#!/usr/bin/env python3
"""Build and audit mergesort and hex resource proofs and executable budgets.

Run from any directory. Paths in the receipt are relative to this repository;
the report and adjacent logs may be written elsewhere with --report.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


PACKAGES = ("interpreter", "codelib", "programs/lean")
ROOTS = {
    "Project.Mergesort.ExportWorkProof":
        "Project.Mergesort.ExportWorkProof.named_export_work",
    "Project.Mergesort.ExecutionBudget":
        "Project.Mergesort.ExecutionBudget.run_export_sorted",
    "HexEncodeStdio.ResourceProof":
        "Project.HexEncodeStdio.ResourceProof.named_export_resources",
    "HexEncodeStdio.ExecutionBudget":
        "Project.HexEncodeStdio.ExecutionBudget.run_export_encoded",
    "CodeLib.SepLogic.CostedTerminalBounds":
        "Wasm.SmallStep.runSteps_result_of_steps_le",
    "Project.HexStdio.Proof":
        "Project.HexStdio.Proof.encode_memory_correct",
}
# Existing hex proofs emit legacy linter warnings. CI checks Project with
# --wfail before running this combined validation target.
BUILD = ["lake", "build", "Project", "HexEncodeStdio", "HexDecodeStdio"]
CONFIG_NAMES = {"lean-toolchain", "lakefile.lean", "lakefile.toml",
                "lake-manifest.json", "Cargo.toml", "Cargo.lock",
                "rust-toolchain.toml"}


def files_below(directory: Path):
    """Exclude generated Lake/Rust caches, including shared dependency trees."""
    for current, directories, files in os.walk(directory):
        directories[:] = sorted(d for d in directories
                                if d not in {".lake", ".git", "target", "__pycache__"})
        yield from (Path(current) / name for name in sorted(files))


def source_paths(root: Path) -> list[Path]:
    paths = set()
    for package in PACKAGES:
        paths.update(path for path in files_below(root / package)
                     if path.suffix in {".lean", ".wat", ".wasm"}
                     or path.name in CONFIG_NAMES)
    paths.update(path for path in files_below(root / "programs/rust")
                 if path.suffix in {".rs", ".wat", ".wasm"}
                 or path.name in CONFIG_NAMES)
    paths.update(root / path for path in (
        "lean-toolchain", "scripts/axiom-audit.py",
        "scripts/check-resource-guarantees.py"))
    return sorted(paths)


def source_inventory(root: Path) -> dict[str, str]:
    return {path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in source_paths(root)}


def inventory_changes(before: dict, after: dict) -> list[str]:
    return sorted(path for path in before.keys() | after.keys()
                  if before.get(path) != after.get(path))


def local_modules(inventory: dict) -> dict[str, str]:
    modules = {}
    for filename in inventory:
        path = Path(filename)
        if path.suffix != ".lean" or path.name == "lakefile.lean":
            continue
        for package in PACKAGES:
            if path.is_relative_to(package):
                name = ".".join(path.relative_to(package).with_suffix("").parts)
                if name in modules:
                    raise ValueError(f"Duplicate local module: {name}")
                modules[name] = filename
    return modules


def closure_source(report: Path) -> str:
    imports = "\n".join(f"import {module}" for module in ROOTS)
    return imports + f'''
import Lean.Elab.Command
open Lean Elab Command

-- Recheck current WAT against the imported AST even on an incremental build.
#eval Wasm.checkWatFidelity "../rust/build/mergesort/program.wat" Project.Mergesort.module
#eval Wasm.checkWatFidelity "../rust/build/hex_stdio/program.wat" Project.HexStdio.module

-- Exercise canonical initialization and the proved numerical runner budget.
#eval do
  let cases : List (List UInt32 × List UInt32) :=
    [([], []), ([7], [7]), ([3, 1, 2], [1, 2, 3]),
     ([5, 1, 5, 0, 1], [0, 1, 1, 5, 5]),
     ([4294967295, 0, 2147483648, 1], [0, 1, 2147483648, 4294967295])]
  for (input, expected) in cases do
    match Project.Mergesort.ExecutionBudget.run input with
    | some (.success values store) =>
      unless values == [] &&
          store.wasm.host.stdio.output == Project.Mergesort.Spec.encodeValues expected &&
          store.wasm.host.stdio.input == [] && !store.wasm.host.oom.raised &&
          decide (store.wasm.mem.pages ≤ Project.Mergesort.Spec.growingPageBound input) do
        throw <| IO.userError "mergesort budget execution returned an unexpected result"
    | _ => throw <| IO.userError "mergesort budget execution did not return normally"
  IO.println "Five mergesort named-export budget executions passed"

-- Literal encodings cover empty input, byte boundaries, and multi-read input.
#eval do
  let cases : List (List UInt8 × List UInt8) :=
    [([], []), ([0], [48, 48]), ([255], [102, 102]),
     ([0, 15, 16, 127, 128, 255], "000f107f80ff".toUTF8.toList),
     (List.replicate 256 65, (List.replicate 256 [52, 49]).flatten),
     (List.replicate 257 0, (List.replicate 257 [48, 48]).flatten)]
  for (input, expected) in cases do
    match Project.HexEncodeStdio.ExecutionBudget.run input with
    | some (.success values store) =>
      unless values == [] && store.wasm.host.stdio.output == expected &&
          store.wasm.host.stdio.output == Project.HexStdio.Spec.encode input &&
          store.wasm.host.stdio.input == [] && !store.wasm.host.oom.raised &&
          decide (17 ≤ store.wasm.mem.pages ∧
            store.wasm.mem.pages ≤ Project.HexEncodeStdio.ResourceBounds.pageBound input) do
        throw <| IO.userError "hex budget execution returned an unexpected result"
    | _ => throw <| IO.userError "hex budget execution did not return normally"
  IO.println "Six hex named-export budget executions passed"

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.map Name.toString
  liftIO <| IO.FS.writeFile {json.dumps(str(report))} (toJson modules).pretty
'''


def validate_groups(groups: list[dict], modules: list[str], roots: dict) -> dict:
    """Reject incomplete or inconsistent JSON; retain private and def entries."""
    if sorted(m for group in groups for m in group["modules"]) != sorted(modules):
        raise ValueError("Audit module coverage differs from the requested import closure")
    declarations = []
    for group in groups:
        entries = group["declarations"]
        for entry in entries:
            if (entry["module"] not in group["modules"]
                    or not isinstance(entry["name"], str)
                    or type(entry["theorem"]) is not bool):
                raise ValueError("Malformed audit declaration")
        if (group["declarations_checked"] != len(entries)
                or group["theorems_checked"] != sum(d["theorem"] for d in entries)):
            raise ValueError("Audit declaration counts do not match its inventory")
        declarations.extend(entries)
    pairs = {(d["module"], d["name"]) for d in declarations}
    if len(pairs) != len(declarations):
        raise ValueError("Audit contains duplicate declarations")
    theorems = {(d["module"], d["name"]) for d in declarations if d["theorem"]}
    if not set(roots.items()) <= theorems:
        raise ValueError("A required resource or runner theorem was not audited")
    return {
        "modules": sorted(modules),
        "declarations_checked": len(declarations),
        "theorems_checked": len(theorems),
        "private_declarations_checked": sum(d["name"].startswith("_private.")
                                            for d in declarations),
        "declarations": sorted(declarations, key=lambda d: (d["module"], d["name"])),
        "violations": [v for group in groups for v in group["violations"]],
    }


def load_auditor(root: Path):
    spec = importlib.util.spec_from_file_location("talos_axiom_audit", root / "scripts/axiom-audit.py")
    module = importlib.util.module_from_spec(spec)
    previous = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def run_check(root: Path, report: Path) -> int:
    # Refuse before entering any path that can write the report, including finally.
    if report.resolve() in {path.resolve() for path in source_paths(root)}:
        raise ValueError("The report would overwrite a validation input")
    report.parent.mkdir(parents=True, exist_ok=True)
    package = root / "programs/lean"
    result = {
        "schema_version": 1,
        "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "roots": ROOTS,
        "build": {"cwd": "programs/lean", "argv": BUILD},
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "source_unchanged": False,
    }
    before = None
    stage = "source inventory"
    try:
        before = source_inventory(root)
        result["source_inventory"] = before
        # Remove any previous PASS immediately, including if interrupted later.
        report.write_text(json.dumps(result, indent=2) + "\n")
        stage = "toolchain"
        result["lean_version"] = subprocess.check_output(
            ["lake", "env", "lean", "--version"], cwd=package, text=True).strip()
        result["python_version"] = sys.version.split()[0]
        stage = "build"
        build_log = report.with_suffix(".build.log")
        result["build"]["log"] = build_log.name
        print("Building Project and the complete mergesort and hex resource proofs", flush=True)
        with build_log.open("w") as log:
            build = subprocess.run(BUILD, cwd=package, stdout=log, stderr=subprocess.STDOUT)
        result["build"]["returncode"] = build.returncode
        build.check_returncode()
        stage = "import closure and WAT fidelity"
        with tempfile.TemporaryDirectory(prefix="talos-resource-imports-") as temp:
            source, closure_report = Path(temp) / "ImportClosure.lean", Path(temp) / "imports.json"
            source.write_text(closure_source(closure_report))
            probe_log = report.with_suffix(".imports.log")
            result["import_probe_log"] = probe_log.name
            with probe_log.open("w") as log:
                subprocess.run(["lake", "env", "lean", str(source)], cwd=package,
                               stdout=log, stderr=subprocess.STDOUT, check=True)
            imported = json.loads(closure_report.read_text())
        if (not isinstance(imported, list) or not all(isinstance(m, str) for m in imported)
                or len(imported) != len(set(imported))):
            raise ValueError("Malformed imported-module inventory")
        sources = local_modules(before)
        modules = sorted(set(imported) & sources.keys())
        if not set(ROOTS) <= set(modules):
            raise ValueError("Required resource root absent from the local import closure")
        # A missing local source must not be silently treated as an external dependency.
        local_prefixes = ("Interpreter", "CodeLib", "Project", "HexEncodeStdio", "HexDecodeStdio")
        missing = [m for m in imported if m.split(".")[0] in local_prefixes and m not in sources]
        if missing:
            raise ValueError(f"Imported local modules have no source: {missing}")
        result["module_sources"] = {m: sources[m] for m in modules}
        result["external_imports"] = sorted(set(imported) - set(modules))
        result["wat_fidelity_checked"] = [
            "programs/rust/build/mergesort/program.wat",
            "programs/rust/build/hex_stdio/program.wat",
        ]
        result["named_export_budget_execution_cases"] = 11
        result["named_export_budget_cases_by_program"] = {"mergesort": 5, "hex_encode": 6}
        changes = inventory_changes(before, source_inventory(root))
        if changes:
            raise ValueError(f"Validation inputs changed during the build: {changes}")
        stage = "all-declaration axiom audit"
        print(f"Auditing every declaration in {len(modules)} local imported modules", flush=True)
        groups = load_auditor(root).audit_groups(package, modules)
        result["audit"] = validate_groups(groups, modules, ROOTS)
        if result["audit"]["violations"]:
            raise ValueError("Nonstandard axiom dependencies found; see audit.violations")
        result["status"] = "PASS"
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        result["status"] = "FAIL"
        result["failed_stage"] = stage
        if isinstance(error, subprocess.CalledProcessError):
            result["error"] = f"Command exited {error.returncode}; inspect the stage log"
        else:
            result["error"] = str(error).replace(str(root), "<repository>")
    finally:
        if before is not None:
            try:
                after = source_inventory(root)
                result["final_source_inventory"] = after
                result["changed_inputs"] = inventory_changes(before, after)
                result["source_unchanged"] = not result["changed_inputs"]
                if result["changed_inputs"]:
                    result["status"] = "FAIL"
                    result["failed_stage"] = "source identity"
            except OSError as error:
                result["status"] = "FAIL"
                result["failed_stage"] = "final source inventory"
                result["error"] = str(error).replace(str(root), "<repository>")
        result["finished_utc"] = datetime.now(timezone.utc).isoformat()
        report.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{result['status']}: {report}", flush=True)
    return int(result["status"] != "PASS")


class ValidatorTests(unittest.TestCase):
    def test_refuses_report_overwriting_input_before_running_lake(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = root / "programs/lean/lake-manifest.json"
            manifest.parent.mkdir(parents=True)
            original = b'{"packages": []}\n'
            manifest.write_bytes(original)
            with patch.object(subprocess, "run") as run, patch.object(subprocess, "check_output") as output:
                with self.assertRaisesRegex(ValueError, "overwrite a validation input"):
                    run_check(root, manifest)
                run.assert_not_called()
                output.assert_not_called()
            self.assertEqual(manifest.read_bytes(), original)

    def test_source_changes_and_cache_exclusion(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name in ("lean-toolchain", "scripts/axiom-audit.py",
                         "scripts/check-resource-guarantees.py", "codelib/CodeLib/Proof.lean"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("original")
            before = source_inventory(root)
            cache = root / "codelib/.lake/build/cache.lean"
            cache.parent.mkdir(parents=True)
            cache.write_text("generated")
            self.assertEqual(before, source_inventory(root))
            proof = root / "codelib/CodeLib/Proof.lean"
            proof.write_text("changed")
            added = root / "codelib/CodeLib/Added.lean"
            added.write_text("new")
            (root / "lean-toolchain").unlink()
            with self.assertRaises(FileNotFoundError):
                source_inventory(root)
            (root / "lean-toolchain").write_text("original")
            self.assertEqual(inventory_changes(before, source_inventory(root)),
                             ["codelib/CodeLib/Added.lean", "codelib/CodeLib/Proof.lean"])
            proof.unlink()
            self.assertIn("codelib/CodeLib/Proof.lean", inventory_changes(before, source_inventory(root)))

    def test_report_coverage_and_private_definitions(self):
        group = {"modules": ["M"], "declarations_checked": 2, "theorems_checked": 1,
                 "declarations": [{"module": "M", "name": "M.public", "theorem": True},
                                  {"module": "M", "name": "_private.M.hidden", "theorem": False}],
                 "violations": []}
        result = validate_groups([group], ["M"], {"M": "M.public"})
        self.assertEqual(result["private_declarations_checked"], 1)
        self.assertEqual(result["declarations_checked"], 2)
        for modules, roots in ((["M", "Missing"], {}), (["M"], {"M": "M.missing"})):
            with self.assertRaises(ValueError):
                validate_groups([group], modules, roots)
        group["violations"] = [{"module": "M", "declaration": "_private.M.hidden", "axioms": ["sorryAx"]}]
        self.assertEqual(validate_groups([group], ["M"], {})["violations"], group["violations"])
        group["declarations_checked"] = 1
        with self.assertRaises(ValueError):
            validate_groups([group], ["M"], {})


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=Path(".lake/resource-guarantees/report.json"),
                        help="Receipt path; relative paths are repository-relative")
    parser.add_argument("--self-test", action="store_true", help="Test validation logic without running Lean")
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(ValidatorTests)
        return int(not unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful())
    root = Path(__file__).resolve().parent.parent
    report = (root / args.report).resolve()
    if report.suffix != ".json":
        parser.error("--report must end in .json")
    try:
        return run_check(root, report)
    except (OSError, ValueError) as error:
        print(f"Validation refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
