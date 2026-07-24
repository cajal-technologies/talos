#!/usr/bin/env python3
"""Generate/check the Iris-migration instruction coverage ledger.

The constructor inventory is parsed from `Instruction` itself.  Adding a new
constructor therefore changes the generated CSV and makes `--check` fail until
the row is regenerated and reviewed.

Authors: Abraxas1010 (IAOM / Apoth3osis).
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SYNTAX = ROOT / "interpreter/Interpreter/Wasm/Syntax.lean"
DECODER = ROOT / "interpreter/Interpreter/Wasm/Decoder/Wat.lean"
SEMANTICS = ROOT / "interpreter/Interpreter/Wasm/Semantics.lean"
EXAMPLES = ROOT / "interpreter/Interpreter/Wasm/Examples"
SMALL_STEP_EXAMPLE = EXAMPLES / "SmallStep.lean"
OUTPUT = ROOT / "IrisMigrationCoverage.csv"

SUPPORTED = {
    "localGet",
    "localSet",
    "const",
    "constI64",
    "add",
    "sub",
    "mul",
    "divU",
}

FIELDS = [
    "instruction",
    "decoder",
    "old_semantics",
    "step_relation",
    "step_function",
    "soundness",
    "completeness",
    "determinism",
    "invariant_preservation",
    "old_new_refinement",
    "examples",
    "testsuite",
    "differential_seed",
    "milestone",
    "notes",
]


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def instruction_constructors(source: str) -> list[str]:
    try:
        block = source.split("inductive Instruction where", 1)[1].split(
            "\nderiving Repr", 1
        )[0]
    except IndexError as exc:
        raise SystemExit("could not locate the complete Instruction declaration") from exc

    names: list[str] = []
    for raw_line in block.splitlines():
        line = raw_line.split("--", 1)[0]
        names.extend(re.findall(r"\|\s*([A-Za-z_][A-Za-z0-9_]*)", line))
    if not names or len(names) != len(set(names)):
        raise SystemExit("Instruction constructor parse was empty or duplicated")
    return names


def mentions_constructor(source: str, name: str) -> bool:
    return re.search(rf"(?:Instruction)?\.{re.escape(name)}\b", source) is not None


def render() -> str:
    syntax = read(SYNTAX)
    decoder = read(DECODER)
    semantics = read(SEMANTICS)
    examples = "\n".join(read(path) for path in sorted(EXAMPLES.glob("*.lean")))
    small_step_example = read(SMALL_STEP_EXAMPLE)
    constructors = instruction_constructors(syntax)

    buffer = io.StringIO()
    source_hash = hashlib.sha256(syntax.encode()).hexdigest()
    buffer.write(
        "# authors=Abraxas1010 (IAOM / Apoth3osis); "
        "The Institute for Ontological Mathematics / "
        "Equation Capital dba Apoth3osis\n"
    )
    buffer.write("# generated_by=scripts/small-step-coverage.py\n")
    buffer.write(f"# instruction_source_sha256={source_hash}\n")
    writer = csv.DictWriter(buffer, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()

    for name in constructors:
        migrated = name in SUPPORTED
        proof = "proved_global" if migrated else "not_started"
        writer.writerow(
            {
                "instruction": name,
                "decoder": "present"
                if mentions_constructor(decoder, name)
                else "not_found",
                "old_semantics": "present"
                if mentions_constructor(semantics, name)
                else "not_found",
                "step_relation": "migrated" if migrated else "not_started",
                "step_function": "migrated" if migrated else "not_started",
                "soundness": proof,
                "completeness": proof,
                "determinism": proof,
                "invariant_preservation": proof,
                "old_new_refinement": proof,
                "examples": "small_step_examples"
                if mentions_constructor(small_step_example, name)
                else (
                    "existing_big_step"
                    if mentions_constructor(examples, name)
                    else "not_found"
                ),
                # The committed wast report is outcome-oriented and does not
                # attribute each row to a Lean constructor.
                "testsuite": "baseline_not_attributed",
                "differential_seed": "not_attributed",
                "milestone": "M2_pure_core" if migrated else "future_milestone",
                "notes": "initial observation-labelled slice"
                if migrated
                else "no small-step claim",
            }
        )
    return buffer.getvalue()


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    expected = render()
    if args.write:
        OUTPUT.write_text(expected, encoding="utf-8")
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0

    actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else ""
    if actual != expected:
        print(
            "IrisMigrationCoverage.csv is stale; run "
            "python3 scripts/small-step-coverage.py --write",
            file=sys.stderr,
        )
        return 1
    rows = len(instruction_constructors(read(SYNTAX)))
    print(f"small-step coverage ledger fresh: {rows} instruction constructors")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
