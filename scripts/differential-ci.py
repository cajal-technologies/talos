#!/usr/bin/env python3
"""Run a deterministic miscast corpus and compare individual outcomes with a reviewed baseline.

Invoked by differential.sh --ci after its dependency and runner contract checks.
The pinned miscast package owns generation, execution and value classification.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import threading

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {"CRASH", "timeout", "process-error", "uncomparable"}
NODE_FLAGS = ["--experimental-wasm-exnref"]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def snapshot(records, versions):
    return {
        "schema": 1,
        "versions": versions,
        "corpus": {"count": len(records), "sha256": digest([r["input_sha256"] for r in records])},
        "exceptions": {
            r["id"]: {"verdict": r["verdict"], "engines": r["engines"], "reason": ""}
            for r in records if r["verdict"] != "agree"
        },
    }


def compare(records, versions, baseline):
    """An exception matches an exact case and outcome, never an aggregate failure budget."""
    observed = snapshot(records, versions)
    errors = []
    if not records:
        errors.append("No cases ran.")
    elif not any(r["verdict"] == "agree" for r in records):
        errors.append("No cases produced agreement; this is not a usable comparison.")
    if len({r["id"] for r in records}) != len(records):
        errors.append("Duplicate case identifiers.")
    for key in ("schema", "versions", "corpus"):
        if baseline.get(key) != observed[key]:
            errors.append(f"{key} changed; inspect report.json and review a fresh baseline.")
    exceptions = baseline.get("exceptions", {})
    if not isinstance(exceptions, dict):
        return errors + ["Baseline exceptions must be an object."]
    for record in records:
        name, verdict = record["id"], record["verdict"]
        allowed = exceptions.get(name)
        if verdict in FORBIDDEN:
            errors.append(f"{name}: {verdict} (cannot be baselined)")
        elif verdict != "agree":
            actual = {"verdict": verdict, "engines": record["engines"]}
            if (not isinstance(allowed, dict) or not isinstance(allowed.get("reason"), str)
                    or not allowed["reason"].strip()
                    or {k: allowed.get(k) for k in actual} != actual):
                errors.append(f"{name}: new or changed {verdict}: {record['engines']}")
    # A fixed gap must be removed, so the old exception cannot conceal its return later.
    for name in exceptions.keys() - observed["exceptions"].keys():
        errors.append(f"{name}: stale baseline exception; remove it after review.")
    return errors


def generate_jobs(miscast):
    from miscast.invalid import segs
    from miscast.modes import MODES
    from miscast.wast import load_corpus

    jobs = []
    for suite, mode, count in (("all", "all", 300), ("recgroup", "recgroup", 300)):
        cases, _ = MODES[mode]([], count)
        jobs.extend((suite, "execution", case) for case in cases)
    jobs.extend(("invalid", "validation", segment) for segment in segs())
    for prefix, path in (("talos", ROOT / "differential/seeds"), ("upstream", miscast / "seeds")):
        if any(path.glob("*.wast")):
            raise ValueError(f"CI seeds must be standalone .wat modules, not stateful .wast scripts: {path}")
        cases, stats = load_corpus(str(path))
        if not cases or not stats["files"]:
            raise ValueError(f"Empty seed corpus: {path}")
        jobs.extend((prefix, "execution", case) for case in cases)
        if prefix == "talos":
            variants, _ = MODES["mutate"](cases, 0)
            if not variants:
                raise ValueError("The Talos seed corpus produced no mutations.")
            jobs.extend(("mutate", "mutation", case) for case in variants)
    return jobs


@contextmanager
def record_processes():
    """Observe miscast's subprocess boundary and enable V8 exception references.

    This deliberately uses two private imports from the pinned revision. In that
    revision, a timeout is CompletedProcess(124, '', 'miscast: timeout'), which
    otherwise becomes UNSUP/ERR and can disappear behind an expected-value oracle.
    Thread-local records also retain stderr and the exact argv for diagnosis.
    """
    from miscast import engines, toolchain

    original = toolchain._run
    if engines._run is not original:
        raise RuntimeError("miscast subprocess API changed; review the CI adapter")
    local = threading.local()

    def observed(cmd, timeout=None):
        role = "v8" if cmd[0] == engines.NODE else "wasm-tools" if cmd[0] == "wasm-tools" else "custom"
        if cmd[0] == engines.NODE:
            cmd = [cmd[0], *NODE_FLAGS, *cmd[1:]]
        result = original(cmd, timeout)
        local.processes.append({"role": role, "argv": list(cmd), "returncode": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
        return result

    engines._run = toolchain._run = observed
    try:
        yield local
    finally:
        engines._run = toolchain._run = original


def unexpected_process_exit(process):
    """Only the pinned tools' documented failures may reach baseline matching.

    Talos uses 1 for a Wasm trap, 2 for exhausted fuel, and 3 for a diagnostic.
    A nonzero exit plus arbitrary text (or a numeric stdout prefix) is a process
    failure, regardless of how miscast normalized it. V8's oracle reports Wasm
    rejection/traps on stdout with exit 0; wasm-tools rejects with exit 1.
    """
    code = process["returncode"]
    if code == 0:
        return False
    stderr = process["stderr"].strip()
    if process["stdout"].strip():
        return True
    if process["role"] == "wasm-tools":
        return not (code == 1 and stderr.startswith("error:"))
    if process["role"] != "custom":
        return True
    if code == 1:
        return not (stderr == "trap" or stderr.startswith("trap: "))
    if code == 2:
        return stderr != "out of fuel"
    if code == 3:
        return not stderr.startswith("error: ")
    return True


def run_case(job, engines, local):
    from miscast.engines import _CRASH
    from miscast.runner import differential, validation_differential
    from miscast.toolchain import prepare
    from miscast.verdict import _floatbits_key, _ikey

    suite, kind, case = job
    local.processes = []
    if kind == "mutation":
        _, wasm, valid = prepare(case[1])
        if wasm is not None and not valid:
            kind = "validation"
            case = {"name": case[0], "module": case[1], "reason": "mutated ill-typed module"}
    if kind == "validation":
        result = validation_differential(case, "custom", engines)
    else:
        result = differential(case, "custom", engines)
    name, verdicts, expected, verdict, _, repro = result
    processes = local.processes
    if any(p["returncode"] == 124 and p["stderr"] == "miscast: timeout" for p in processes):
        verdict = "timeout"
    elif any(_CRASH.search(p["stdout"] + p["stderr"]) for p in processes):
        # Validation probes normalize host crashes to ACCEPT upstream. Preserve
        # the stronger signal so an existing validation exception cannot waive it.
        verdict = "CRASH"
    elif any(unexpected_process_exit(p) for p in processes):
        verdict = "process-error"
    elif verdict == "agree":
        # Self-checking expectations are useful, but this gate promises a V8 comparison.
        if verdicts.get("v8", "").split(" ")[0] not in {"OK", "TRAP", "REJECT", "ACCEPT"}:
            verdict = "oracle-unsup"
        elif kind != "validation" and verdicts.get("custom", "").startswith("OK"):
            rtype = repro["rtype"]
            key = ({"int": lambda v: _ikey(v, 32), "int64": lambda v: _ikey(v, 64),
                    "f32bits": lambda v: _floatbits_key(v, 32),
                    "f64bits": lambda v: _floatbits_key(v, 64)}).get(rtype)
            if key and any(key(verdicts[e]) is None for e in ("v8", "custom")):
                verdict = "uncomparable"
    # Upstream can give two different mutations the same label (e.g. reordering
    # either recursion group). Include the input hash instead of conflating them.
    input_hash = digest(job)
    return {"id": f"{suite}/{name}@{input_hash[:12]}", "input_sha256": input_hash, "kind": kind,
            "verdict": verdict, "engines": verdicts, "expected": expected,
            "processes": processes, "repro": repro}


def save_reproducer(output, record):
    """Keep the input and relative replay commands together, independent of CI paths."""
    repro = record["repro"]
    folder = output / "repro" / digest(record["id"])[:16]
    folder.mkdir(parents=True)
    (folder / "module.wat").write_text(repro["wat"], encoding="utf-8")
    if repro.get("wasm_path"):
        shutil.copyfile(repro["wasm_path"], folder / "module.wasm")
    args = [v for _, v in repro["args"]]
    v8_args = [v + ("n" if t == "i64" else "") for t, v in repro["args"]]
    export = repro["export"]
    oracle_export = "__validate__" if record["kind"] == "validation" else export
    script = ["#!/usr/bin/env bash", "set -uo pipefail",
              'runner="${1:?usage: bash replay.sh /absolute/path/to/runner}"',
              'cd "$(dirname "$0")"',
              'wasm-tools parse module.wat -o module.wasm || exit "$?"',
              '"${NODE:-node}" ' + shlex.join(NODE_FLAGS) + ' ../../v8.js module.wasm '
              + shlex.join([oracle_export, *v8_args]),
              '"$runner" module.wat ' + shlex.join([export, *args])]
    (folder / "replay.sh").write_text("\n".join(script) + "\n", encoding="utf-8")
    write_json(folder / "result.json", record)
    return str(folder.relative_to(output))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--miscast", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, default=ROOT / "differential/baseline.json")
    parser.add_argument("--output", type=Path, default=ROOT / ".differential-cache/ci")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--record", action="store_true", help="write a candidate baseline for manual review")
    args = parser.parse_args()
    if args.jobs < 1 or args.jobs > 32:
        parser.error("--jobs must be between 1 and 32")
    miscast = args.miscast.resolve()
    output = args.output.resolve()
    # Never mix a new run with stale findings, or delete a user-supplied directory.
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        parser.error(f"Output directory must be empty: {output}")
    sys.path.insert(0, str(miscast))
    os.environ["MISCAST_TIMEOUT"] = "20"
    from miscast import config, engines

    def command(*argv):
        return subprocess.check_output(argv, text=True, timeout=30).strip()

    if command("git", "-C", str(miscast), "status", "--porcelain", "--untracked-files=no"):
        parser.error("miscast has modified tracked files; use the pinned checkout")
    versions = {"miscast": command("git", "-C", str(miscast), "rev-parse", "HEAD"),
                "node": command(config.NODE, "--version"),
                "node-flags": NODE_FLAGS,
                "wasm-tools": command("wasm-tools", "--version"),
                "lean": (ROOT / "lean-toolchain").read_text().strip()}
    baseline = None if args.record else json.loads(args.baseline.read_text(encoding="utf-8"))
    selected = {key: engines.ENGINES[key] for key in ("v8", "custom")}
    jobs = generate_jobs(miscast)
    print(f"Differential CI: {len(jobs)} cases, {args.jobs} workers; {versions}", flush=True)
    shutil.copyfile(config.ORACLE, output / "v8.js")
    records = []
    with (record_processes() as local, ThreadPoolExecutor(max_workers=args.jobs) as pool,
          (output / "results.jsonl").open("w", encoding="utf-8") as journal):
        for record in pool.map(lambda job: run_case(job, selected, local), jobs):
            if record["verdict"] != "agree":
                record["artifact"] = save_reproducer(output, record)
                print(f"{record['id']}: {record['verdict']} {record['engines']}", flush=True)
            records.append(record)
            journal.write(json.dumps(record, sort_keys=True) + "\n")
            journal.flush()
            if len(records) % 100 == 0:
                print(f"Completed {len(records)}/{len(jobs)}", flush=True)
    errors = [] if args.record else compare(records, versions, baseline)
    counts = dict(Counter(r["verdict"] for r in records))
    report = {"versions": versions, "talos_commit": command("git", "-C", str(ROOT), "rev-parse", "HEAD"),
              "counts": counts, "errors": errors, "records": records}
    write_json(output / "report.json", report)
    write_json(output / "baseline-candidate.json", snapshot(records, versions))
    decision = ("Candidate only; no regression decision." if args.record else
                "FAILED: see errors below." if errors else "No new regressions against the reviewed baseline.")
    summary = ["## Differential comparison with V8", "", decision, "", f"Cases: {len(records)}", "",
               "| Outcome | Count |", "| --- | ---: |"]
    summary += [f"| {label} | {count} |" for label, count in sorted(counts.items())]
    summary += ["", "Unsupported cases and oracle disagreements are coverage gaps, not passes.", ""]
    summary += [f"- {error}" for error in errors]
    summary += ["", "See report.json and repro/*/replay.sh in the uploaded artifact."]
    (output / "summary.md").write_text("\n".join(summary) + "\n", encoding="utf-8")
    print(f"Outcomes: {counts}")
    print(f"Report: {output / 'report.json'}")
    if args.record:
        print("Candidate only: review every exception and fill in its reason before committing a baseline.")
    for error in errors:
        print(error, file=sys.stderr)
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
