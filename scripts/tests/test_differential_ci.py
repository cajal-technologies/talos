"""Regression-policy tests; these need only Python, not the Lean build or miscast."""
import copy
import importlib.util
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "differential_ci", Path(__file__).resolve().parents[1] / "differential-ci.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def row(name="recgroup/recgroup0", verdict="agree", sut="TRAP", oracle="TRAP"):
    return {"id": name, "input_sha256": gate.digest(name), "verdict": verdict,
            "engines": {"custom": sut, "v8": oracle}}


class RegressionPolicy(unittest.TestCase):
    def setUp(self):
        self.versions = {"miscast": "pinned", "node": "v24.13.0", "wasm-tools": "1.251.0"}
        self.good = [row(), row("values/i64", sut="OK 4294967296", oracle="OK 4294967296")]
        self.baseline = gate.snapshot(self.good, self.versions)

    def check(self, records, baseline=None, versions=None):
        return gate.compare(records, versions or self.versions, baseline or self.baseline)

    def test_real_traps_and_matching_values_pass(self):
        self.assertEqual(self.check(self.good), [])

    def test_regression_108_running_an_ill_typed_call_fails(self):
        bad = [row(verdict="SOUNDNESS", sut="OK 40"), self.good[1]]
        self.assertTrue(any("SOUNDNESS" in error for error in self.check(bad)))

    def test_new_wrong_value_fails(self):
        bad = copy.deepcopy(self.good)
        bad[1].update(verdict="VALUE", engines={"custom": "OK 0", "v8": "OK 4294967296"})
        self.assertTrue(self.check(bad))

    def test_timeout_or_missing_oracle_cannot_be_a_pass(self):
        for verdict in ("timeout", "oracle-unsup", "sut-reject", "uncomparable", "process-error"):
            with self.subTest(verdict=verdict):
                bad = [row(verdict=verdict, sut="UNSUP", oracle="ERR"), self.good[1]]
                self.assertTrue(self.check(bad))

    def test_crashes_timeouts_and_unreadable_results_cannot_be_allowlisted(self):
        for verdict in gate.FORBIDDEN:
            with self.subTest(verdict=verdict):
                bad = [row(verdict=verdict)]
                baseline = gate.snapshot(bad, self.versions)
                baseline["exceptions"][bad[0]["id"]]["reason"] = "A reason cannot waive this failure."
                self.assertTrue(self.check(bad, baseline))

    def test_known_soundness_defect_is_matched_by_exact_case_and_result(self):
        records = [row("invalid/known", "SOUNDNESS", "ACCEPT", "REJECT"), self.good[1]]
        baseline = gate.snapshot(records, self.versions)
        baseline["exceptions"][records[0]["id"]]["reason"] = "Existing invalid-module acceptance tracked in #152."
        self.assertEqual(self.check(records, baseline), [])
        changed = copy.deepcopy(records)
        changed[0]["engines"]["v8"] = "ERR"
        self.assertTrue(self.check(changed, baseline))

    def test_exact_documented_gap_is_reported_and_accepted(self):
        records = [row(verdict="oracle-unsup", oracle="ERR"), self.good[1]]
        baseline = gate.snapshot(records, self.versions)
        baseline["exceptions"][records[0]["id"]]["reason"] = "Pinned V8 lacks this proposal."
        self.assertEqual(self.check(records, baseline), [])
        self.assertEqual(len(baseline["exceptions"]), 1)

    def test_a_corpus_of_only_known_gaps_cannot_pass(self):
        records = [row(verdict="oracle-unsup", oracle="ERR")]
        baseline = gate.snapshot(records, self.versions)
        baseline["exceptions"][records[0]["id"]]["reason"] = "Known oracle gap."
        self.assertTrue(any("No cases produced agreement" in error for error in self.check(records, baseline)))

    def test_candidate_without_review_reason_fails(self):
        records = [row(verdict="oracle-unsup", oracle="ERR")]
        self.assertTrue(self.check(records, gate.snapshot(records, self.versions)))

    def test_same_total_failure_count_cannot_hide_a_new_failure(self):
        original = [row("a", "VALUE", "OK 1", "OK 2"), row("b")]
        baseline = gate.snapshot(original, self.versions)
        baseline["exceptions"]["a"]["reason"] = "Reviewed specific printer discrepancy."
        changed = [row("a"), row("b", "VALUE", "OK 1", "OK 2")]
        errors = self.check(changed, baseline)
        self.assertTrue(any("b:" in error for error in errors))
        self.assertTrue(any("stale" in error for error in errors))

    def test_same_case_with_changed_wrong_value_fails(self):
        original = [row("a", "VALUE", "OK 1", "OK 2")]
        baseline = gate.snapshot(original, self.versions)
        baseline["exceptions"]["a"]["reason"] = "Reviewed specific printer discrepancy."
        self.assertTrue(self.check([row("a", "VALUE", "OK 3", "OK 2")], baseline))

    def test_fixed_gap_must_be_removed(self):
        original = [row(verdict="oracle-unsup", oracle="ERR"), self.good[1]]
        baseline = gate.snapshot(original, self.versions)
        baseline["exceptions"][original[0]["id"]]["reason"] = "Known oracle gap."
        self.assertTrue(any("stale" in error for error in self.check(self.good, baseline)))

    def test_empty_truncated_duplicate_and_changed_corpora_fail(self):
        changed = copy.deepcopy(self.good)
        changed[0]["input_sha256"] = gate.digest("different module with the same case name")
        for records in ([], self.good[:1], [self.good[0], self.good[0]], changed):
            with self.subTest(records=records):
                self.assertTrue(self.check(records))

    def test_toolchain_drift_fails(self):
        versions = dict(self.versions, node="v99.0.0")
        self.assertTrue(self.check(self.good, versions=versions))

    def test_only_documented_nonzero_exits_are_allowed(self):
        def process(role, code, stderr, stdout=""):
            return {"role": role, "returncode": code, "stderr": stderr, "stdout": stdout}

        for p in [process("custom", 1, "trap: unreachable\n"),
                  process("custom", 2, "out of fuel\n"),
                  process("custom", 3, "error: bad integer literal: $d\n"),
                  process("wasm-tools", 1, "error: invalid module\n")]:
            with self.subTest(process=p):
                self.assertFalse(gate.unexpected_process_exit(p))
        for p in [process("custom", 1, "fatal runtime failure\n"),
                  process("custom", 42, "error: failed\n"),
                  process("custom", 3, "uncaught exception: failed\n"),
                  process("custom", 1, "trap: unreachable\n", "20\n"),
                  process("custom", -9, ""),
                  process("v8", 1, "error: failed\n"),
                  process("wasm-tools", 1, "fatal runtime failure\n")]:
            with self.subTest(process=p):
                self.assertTrue(gate.unexpected_process_exit(p))

    def test_reproducer_uses_local_files_and_quotes_arguments(self):
        record = row("name with / special chars")
        record.update(kind="execution", repro={
            "wat": '(module (func (export "f with spaces") (param i64)))',
            "wasm_path": None, "args": [["i64", "-1"]], "export": "f with spaces"})
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory) / gate.save_reproducer(Path(directory), record)
            script = (folder / "replay.sh").read_text()
            self.assertIn("'f with spaces' -1n", script)
            self.assertIn("'f with spaces' -1", script)
            self.assertIn("../../v8.js module.wasm", script)
            self.assertNotIn(directory, script)
            self.assertEqual((folder / "module.wat").read_text(), record["repro"]["wat"])


@unittest.skipUnless(os.environ.get("TALOS_DIFFERENTIAL_INTEGRATION"), "requires the built runner and pinned miscast")
class RealEngineChecks(unittest.TestCase):
    """Fault-inject the SUT process while keeping the real V8 oracle and gate path."""
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(gate.ROOT / ".differential-cache/miscast"))
        cls.runner = gate.ROOT / "interpreter/.lake/build/bin/runner"
        os.environ["NODE"] = shutil.which("node")
        os.environ["CUSTOM_CMD"] = shlex.join([str(cls.runner), "{wat}", "{export}"])
        from miscast import config, engines, modes, toolchain
        cls.config, cls.backends, cls.toolchain = config, engines, toolchain
        cls.engines = {key: engines.ENGINES[key] for key in ("v8", "custom")}
        cls.recgroup = ("test", "execution", modes.MODES["recgroup"]([], 1)[0][0])
        cls.integer = ("test", "execution", ("wide-integer",
            '(module (func (export "f") (result i64) i64.const 4294967296))',
            "f", [], None, "int64"))

    def run_job(self, job, code=None, oracle=None):
        engines = dict(self.engines)
        if code is not None:
            engines["custom"] = self.backends.make_be_cmd(
                shlex.join([sys.executable, "-c", code, "{wat}", "{export}"]))
        if oracle is not None:
            engines["v8"] = oracle
        with gate.record_processes() as local:
            return gate.run_case(job, engines, local)

    def test_108_fault_is_detected_against_real_v8(self):
        good = self.run_job(self.recgroup)
        self.assertEqual(good["verdict"], "agree")
        bad = self.run_job(self.recgroup, "print(40)")
        self.assertEqual(bad["verdict"], "SOUNDNESS")
        self.assertTrue(gate.compare([bad], {}, gate.snapshot([good], {})))

    def test_exception_reference_proposal_is_enabled_in_v8(self):
        from miscast.wast import load_corpus
        cases, _ = load_corpus(str(gate.ROOT / ".differential-cache/miscast/seeds"))
        case = next(case for case in cases if case[0] == "eh_two_tags:f")
        result = self.run_job(("test", "execution", case))
        self.assertEqual(result["verdict"], "agree")
        self.assertEqual(result["engines"]["v8"], "OK 33")
        self.assertTrue(any("--experimental-wasm-exnref" in p["argv"] for p in result["processes"]))

    def test_different_mutations_with_the_same_label_stay_distinct(self):
        jobs = gate.generate_jobs(gate.ROOT / ".differential-cache/miscast")
        mutations = [job for job in jobs if job[0] == "mutate" and job[2][0].endswith("|reorder-rec")]
        self.assertEqual(len(mutations), 2)
        first, second = [self.run_job(job) for job in mutations]
        self.assertNotEqual(first["id"], second["id"])

    def test_lost_high_i64_bits_are_detected(self):
        bad = self.run_job(self.integer, "print(0)")
        self.assertEqual(bad["verdict"], "VALUE")

    def test_missing_numeric_output_is_not_agreement(self):
        bad = self.run_job(self.integer, "pass")
        self.assertEqual(bad["verdict"], "uncomparable")

    def test_oracle_failure_cannot_fall_back_to_self_check(self):
        bad = self.run_job(self.recgroup, oracle=lambda *args: "ERR")
        self.assertEqual(bad["verdict"], "oracle-unsup")

    def test_real_process_timeout_is_retained(self):
        previous = self.toolchain.TIMEOUT
        self.toolchain.TIMEOUT = 0.2
        try:
            bad = self.run_job(self.integer, "import time; time.sleep(3)")
        finally:
            self.toolchain.TIMEOUT = previous
        self.assertEqual(bad["verdict"], "timeout")
        self.assertTrue(any(p["stderr"] == "miscast: timeout" for p in bad["processes"]))

    def test_host_crash_is_distinct_from_a_wasm_trap(self):
        bad = self.run_job(self.integer, "raise SystemExit('thread main panicked: simulated host failure')")
        self.assertEqual(bad["verdict"], "CRASH")

    def test_unrecognized_failure_cannot_match_a_decoder_gap(self):
        # Use the exact generated input already recorded as a decoder gap.
        jobs = gate.generate_jobs(gate.ROOT / ".differential-cache/miscast")
        job = next(job for job in jobs if job[0] == "all"
                   and job[2][0] == "constinit16|constinit-data[i8-bytes]")
        bad = self.run_job(job, "raise SystemExit('fatal runtime failure')")
        self.assertEqual(bad["engines"], {"v8": "OK 20", "custom": "UNSUP"})
        self.assertEqual(bad["verdict"], "process-error")
        # Even an explicitly allowed copy of this result cannot waive it.
        baseline = gate.snapshot([bad], {})
        baseline["exceptions"][bad["id"]]["reason"] = "Existing decoder gap."
        self.assertTrue(any("cannot be baselined" in e
                            for e in gate.compare([bad], {}, baseline)))

    def test_numeric_stdout_does_not_hide_a_nonzero_exit(self):
        bad = self.run_job(self.integer, "print(4294967296); raise SystemExit(42)")
        self.assertEqual(bad["engines"]["custom"], "OK 4294967296")
        self.assertEqual(bad["verdict"], "process-error")

    def test_v8_nonzero_exit_is_a_process_failure(self):
        def failing_oracle(*args):
            self.backends._run([self.config.NODE, "-e", "process.exit(1)"])
            return "ERR"
        bad = self.run_job(self.integer, oracle=failing_oracle)
        self.assertEqual(bad["verdict"], "process-error")

    def test_validation_host_crash_cannot_be_baselined_as_acceptance(self):
        from miscast.invalid import segs
        command = shlex.join([sys.executable, "-c",
                              "raise SystemExit('thread main panicked: simulated host failure')"])
        with patch.dict(os.environ, {"CUSTOM_CMD": command}):
            bad = self.run_job(("test", "validation", segs()[0]))
        self.assertEqual(bad["engines"]["custom"], "ACCEPT")
        self.assertEqual(bad["verdict"], "CRASH")

    def test_artifact_replays_from_a_different_directory(self):
        bad = self.run_job(self.recgroup, "print(40)")
        with tempfile.TemporaryDirectory(prefix="talos replay ") as directory:
            output = Path(directory)
            shutil.copyfile(self.config.ORACLE, output / "v8.js")
            folder = output / gate.save_reproducer(output, bad)
            result = subprocess.run(["bash", str(folder / "replay.sh"), str(self.runner)],
                                    cwd="/", capture_output=True, text=True, timeout=20)
            self.assertIn("=> TRAP", result.stdout)
            self.assertIn("trap:", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
