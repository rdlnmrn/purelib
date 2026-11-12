"""Checked reload tests; synthetic producers establish no mathematical outcome."""
import hashlib
import io
import json
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from scripts.profiling import cubic_sheets


class CubicCaseCheckpoints(unittest.TestCase):
    """Retain completed requests and reject incomplete or corrupt cache data."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="ccl-cubic-checkpoint-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "Purelib").mkdir()
        (self.root / "Purelib/Fixture.lean").write_text("module\n")
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            (self.root / name).write_text("test-fixture\n")
        self.binary = self.root / "fixture-harness"
        self.binary.write_text("""#!/usr/bin/python3
import json,sys
from pathlib import Path
if sys.argv[1:]==['--compound-cases']:
    print('ordered-invalid')
    print('retry')
    raise SystemExit(0)
if sys.argv[1:]==['--comparison-cases']:
    print('nested')
    print('higher')
    raise SystemExit(0)
if sys.argv[1:]==['--root-comparison-cases']:
    print('retry')
    print('other')
    raise SystemExit(0)
case=sys.argv[2]
if sys.argv[1]=='--root-comparison-case':
    case='root:'+case
    if len(sys.argv)==5:
        case+=':'+sys.argv[4]
if sys.argv[1]=='--comparison-case':
    case+=':'+sys.argv[4]
path=Path(__file__).with_name('calls.json')
calls=json.loads(path.read_text()) if path.exists() else {}
calls[case]=calls.get(case,0)+1
path.write_text(json.dumps(calls))
if calls[case]!=1:
    raise SystemExit('completed producer was called again')
print('synthetic checkpoint producer',case)
""")
        self.binary.chmod(0o755)
        self.store = self.root / "store"

    def calls(self):
        """Read only the fixture's actual producer-call counter."""
        return json.loads((self.root / "calls.json").read_text())

    def test_completed_case_recovers_without_running_its_producer(self):
        with self.assertRaises(SystemExit) as stopped:
            cubic_sheets.run_cases(self.binary, self.root, self.store,
                                   ["ordered-invalid", "retry"], after_case=1)
        self.assertEqual(stopped.exception.code, 17)
        first = next((self.store / "cases").rglob("result.json"))
        before = (first.stat().st_ino, first.stat().st_mtime_ns, first.read_bytes())
        resumed = cubic_sheets.run_cases(self.binary, self.root, self.store,
                                        ["ordered-invalid", "retry"])
        self.assertEqual([entry["reused"] for entry in resumed], [True, False])
        self.assertEqual(self.calls(), {"ordered-invalid": 1, "retry": 1})
        self.assertEqual(before, (first.stat().st_ino, first.stat().st_mtime_ns, first.read_bytes()))

    def test_corrupt_and_missing_artifacts_are_rejected_before_production(self):
        cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        log = next((self.store / "cases").rglob("stdout.log"))
        original = log.read_bytes()
        log.write_bytes(original + b"corrupt")
        with self.assertRaises(RuntimeError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        log.write_bytes(original)
        log.unlink()
        with self.assertRaises(RuntimeError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        self.assertEqual(self.calls(), {"ordered-invalid": 1})

    def test_explicit_protocol_recovers_and_separates_same_named_requests(self):
        protocol = ("--root-comparison-cases", "--root-comparison-case")
        with self.assertRaises(SystemExit) as stopped:
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["retry", "other"],
                                   after_case=1, case_protocol=protocol)
        self.assertEqual(stopped.exception.code, 17)
        root_retry = next((self.store / "cases").glob("*/retry/result.json"))
        original = (root_retry.stat().st_ino, root_retry.stat().st_mtime_ns, root_retry.read_bytes())
        resumed = cubic_sheets.run_cases(self.binary, self.root, self.store, ["retry", "other"],
                                        case_protocol=protocol)
        self.assertEqual([row["reused"] for row in resumed], [True, False])
        self.assertEqual(original, (root_retry.stat().st_ino, root_retry.stat().st_mtime_ns, root_retry.read_bytes()))
        compound = cubic_sheets.run_cases(self.binary, self.root, self.store, ["retry"])
        self.assertNotEqual(compound[0]["receipt"], resumed[0]["receipt"])
        self.assertEqual(self.calls(), {"root:retry": 1, "root:other": 1, "retry": 1})

    def test_invalid_explicit_protocol_does_not_start_a_worker(self):
        for protocol, request in [(("--only-one",), None), (("not-a-flag", "--case"), None),
                                  (("--root-comparison-cases", "--root-comparison-case"),
                                   (self.root / "banks", "invalid"))]:
            with self.subTest(protocol=protocol, request=request):
                with mock.patch.object(cubic_sheets.subprocess, "run") as run:
                    with self.assertRaises(ValueError):
                        cubic_sheets.run_cases(self.binary, self.root, self.store,
                                               ["retry"], root_request=request, case_protocol=protocol)
                    run.assert_not_called()

    def test_cli_cubic_roots_selects_the_actual_distinct_case_interface(self):
        arguments = ["cubic-sheets", "--executable", str(self.binary), "--store", str(self.store),
                     "--case-protocol", "cubic-roots", "--case", "retry"]
        with mock.patch.object(cubic_sheets.paths, "ROOT", self.root), \
                mock.patch.object(cubic_sheets.sys, "argv", arguments), \
                mock.patch.object(cubic_sheets.signal, "signal"):
            cubic_sheets.main()
            cubic_sheets.main()
        self.assertEqual(self.calls(), {"root:retry": 1})
        manifest = json.loads(next((self.store / "manifests").glob("*.json")).read_text())
        self.assertEqual(manifest["case_protocol"], ["--root-comparison-cases", "--root-comparison-case"])

    def test_cli_cubic_root_checkpoint_recovery_keeps_directory_mode_and_protocol(self):
        directory = self.root / "banks"
        arguments = ["cubic-sheets", "--executable", str(self.binary), "--store", str(self.store),
                     "--case-protocol", "cubic-roots", "--case", "retry", "--case", "other",
                     "--checkpoint-directory", str(directory), "--checkpoint-mode", "resume"]
        with mock.patch.object(cubic_sheets.paths, "ROOT", self.root), \
                mock.patch.object(cubic_sheets.signal, "signal"):
            with mock.patch.object(cubic_sheets.sys, "argv", arguments + ["--after-case", "1"]):
                with self.assertRaises(SystemExit) as stopped:
                    cubic_sheets.main()
            self.assertEqual(stopped.exception.code, 17)
            with mock.patch.object(cubic_sheets.sys, "argv", arguments):
                cubic_sheets.main()
                cubic_sheets.main()
            arguments[-1] = "replay"
            with mock.patch.object(cubic_sheets.sys, "argv", arguments):
                cubic_sheets.main()
        self.assertEqual(self.calls(), {"root:retry:resume": 1, "root:other:resume": 1,
                                       "root:retry:replay": 1, "root:other:replay": 1})
        manifests = [json.loads(path.read_text()) for path in (self.store / "manifests").glob("*.json")]
        self.assertEqual(len(manifests), 2)
        self.assertEqual({row["root_comparison_request"]["mode"] for row in manifests}, {"resume", "replay"})
        for row in manifests:
            self.assertEqual(row["case_protocol"], ["--root-comparison-cases", "--root-comparison-case"])
            self.assertEqual(row["root_comparison_request"]["directory"], str(directory.resolve()))
        results = list((self.store / "cases").rglob("result.json"))
        self.assertEqual(len(results), 4)
        for path in results:
            command = json.loads(path.read_text())["request"]["command"]
            self.assertEqual(command[1], "--root-comparison-case")
            self.assertEqual(command[-2], str(directory.resolve()))
            self.assertIn(command[-1], ("resume", "replay"))

    def test_unknown_or_duplicate_requests_do_not_execute_cases(self):
        for requested in (["unknown"], ["retry", "retry"]):
            with self.subTest(requested=requested), self.assertRaises(ValueError):
                cubic_sheets.run_cases(self.binary, self.root, self.store, requested)
        self.assertFalse((self.root / "calls.json").exists())

    def test_root_request_recovery_retains_its_exact_directory_and_mode(self):
        request = (self.root / "banks", "resume")
        with self.assertRaises(SystemExit) as stopped:
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested", "higher"],
                                   after_case=1, root_request=request)
        self.assertEqual(stopped.exception.code, 17)
        resumed = cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested", "higher"],
                                        root_request=request)
        self.assertEqual([entry["reused"] for entry in resumed], [True, False])
        self.assertEqual(self.calls(), {"nested:resume": 1, "higher:resume": 1})
        replayed = cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                         root_request=(request[0], "replay"))
        self.assertFalse(replayed[0]["reused"])
        self.assertEqual(self.calls()["nested:replay"], 1)

    def test_invalid_root_checkpoint_mode_does_not_start_a_worker(self):
        with self.assertRaises(ValueError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                   root_request=(self.root / "banks", "invalid"))
        self.assertFalse((self.root / "calls.json").exists())
        with mock.patch.object(cubic_sheets.sys, "argv", ["cubic-sheets", "--store", str(self.store),
                                                        "--checkpoint-mode", "replay"]):
            with mock.patch.object(cubic_sheets.sys, "stderr"), mock.patch.object(cubic_sheets, "run_cases") as run:
                with self.assertRaises(SystemExit) as rejected:
                    cubic_sheets.main()
        self.assertEqual(rejected.exception.code, 2)
        run.assert_not_called()

    def install_digest_fixture(self, frame: str | None = None):
        """Extend only the synthetic CLI with the retained exact-byte exchange."""
        source = self.binary.read_text()
        if frame is None:
            body = """if '--input-digest-stdio-v1' in sys.argv:
    import hashlib
    payloads = [b'', ('original \u03b1\\n\u96ea' * 20000).encode('utf-8')]
    for payload in payloads:
        sys.stdout.buffer.write(b'CCL_WINDING_SHA256_V1 '+str(len(payload)).encode()+b'\\n'+payload)
        sys.stdout.buffer.flush()
        if sys.stdin.buffer.readline()!=hashlib.sha256(payload).hexdigest().encode()+b'\\n':
            raise SystemExit('wrong actual byte digest')
"""
        else:
            body = "if '--input-digest-stdio-v1' in sys.argv:\n    sys.stdout.buffer.write(" + repr(frame.encode()) + ")\n    sys.stdout.buffer.flush()\n    sys.stdin.buffer.readline()\n"
        self.binary.write_text(source.replace('case=sys.argv[2]\n', body + 'case=sys.argv[2]\n'))

    def test_exact_utf8_pipe_and_complete_checked_reload(self):
        self.install_digest_fixture()
        request = (self.root / "banks", "resume")
        first = cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                       root_request=request, input_digest_stdio=True)
        directory = Path(first[0]["receipt"]).parent
        events = [json.loads(line) for line in (directory / "digest-events.jsonl").read_text().splitlines()]
        log = (directory / "stdout.log").read_bytes()
        payloads = [b'', ('original \u03b1\n\u96ea' * 20000).encode('utf-8')]
        for ordinal, (event, payload) in enumerate(zip(events, payloads, strict=True)):
            start = event["stdout_offset"] + event["header_bytes"]
            self.assertEqual(log[start:start + event["payload_bytes"]], payload)
            self.assertEqual(event["sha256"], hashlib.sha256(payload).hexdigest())
            self.assertEqual(event["ordinal"], ordinal)
        native = json.loads((directory / "native.json").read_text())
        self.assertEqual(native["input_digest_transport"]["requests"], 2)
        before = {p.name: (p.stat().st_ino, p.stat().st_mtime_ns, p.read_bytes())
                  for p in directory.iterdir() if p.is_file()}
        second = cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                        root_request=request, input_digest_stdio=True)
        self.assertTrue(second[0]["reused"])
        self.assertEqual(self.calls(), {"nested:resume": 1})
        self.assertEqual(before, {p.name: (p.stat().st_ino, p.stat().st_mtime_ns, p.read_bytes())
                                 for p in directory.iterdir() if p.is_file()})
        with (directory / "digest-events.jsonl").open("a") as output:
            output.write("corrupt\n")
        with self.assertRaises(RuntimeError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                   root_request=request, input_digest_stdio=True)
        self.assertEqual(self.calls(), {"nested:resume": 1})

    def test_malformed_frame_preserves_failure_and_releases_the_worker(self):
        self.install_digest_fixture('CCL_WINDING_SHA256_V1 invalid\n')
        with self.assertRaises(RuntimeError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                   root_request=(self.root / "banks", "resume"), input_digest_stdio=True)
        native = json.loads(next((self.store / "cases").rglob("native.json")).read_text())
        self.assertIn("malformed digest frame", native["input_digest_transport"]["failure"])
        self.assertEqual(native["live_handles"], [])
        self.assertFalse(list((self.store / "cases").rglob("result.json")))

    def test_raw_exit_is_saved_before_group_inspection_and_stream_close(self):
        streams = []
        original_open = Path.open
        original_members = cubic_sheets.group_members

        def opened(path, *args, **kwargs):
            result = original_open(path, *args, **kwargs)
            if path.name == "stdout.log" and args == ("wb",):
                streams.append(result)
            return result

        def members(pgid):
            raw = next((self.store / "cases").rglob("exit.json"))
            self.assertEqual(json.loads(raw.read_text()), {"exit_code": 0, "errors": []})
            self.assertTrue(streams)
            self.assertTrue(all(not stream.closed for stream in streams))
            return original_members(pgid)

        with mock.patch.object(Path, "open", opened), \
                mock.patch.object(cubic_sheets, "group_members", side_effect=members):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        self.assertTrue(all(stream.closed for stream in streams))

    def test_reader_start_failure_keeps_the_owned_wait_and_reaps_worker(self):
        self.install_digest_fixture()
        processes = []
        identities = []
        captured_at_start = []
        original_spawn = subprocess.Popen
        original_identity = cubic_sheets.worker_identity

        def spawn(command, *args, **kwargs):
            process = original_spawn(command, *args, **kwargs)
            if command[0] == "/usr/bin/time":
                processes.append(process)
            return process

        def identity(pid):
            owner = original_identity(pid)
            identities.append(owner)
            return owner

        def start_failure():
            captured_at_start.append(any(owner["pid"] == processes[0].pid and
                                         owner["start_ticks"] is not None for owner in identities))
            raise OSError("reader start failed")

        with mock.patch.object(cubic_sheets.subprocess, "Popen", side_effect=spawn), \
                mock.patch.object(cubic_sheets, "worker_identity", side_effect=identity), \
                mock.patch.object(cubic_sheets.threading.Thread, "start", side_effect=start_failure):
            with self.assertRaises(RuntimeError):
                cubic_sheets.run_cases(self.binary, self.root, self.store, ["nested"],
                                       root_request=(self.root / "banks", "resume"), input_digest_stdio=True)
        self.assertEqual(len(processes), 1)
        self.assertEqual(captured_at_start, [True])
        worker = processes[0]
        self.assertIsNotNone(worker.returncode)
        self.assertTrue(worker.stdin.closed)
        self.assertTrue(worker.stdout.closed)
        self.assertEqual(cubic_sheets.group_members(worker.pid), [])
        raw = json.loads(next((self.store / "cases").rglob("exit.json")).read_text())
        self.assertEqual(raw["exit_code"], worker.returncode)
        self.assertIn("reader start failed", raw["errors"][0]["failure"])
        self.assertFalse(list((self.store / "cases").rglob("result.json")))

    def test_running_receipt_failure_still_waits_and_retains_error(self):
        original_save = cubic_sheets.branch_builds.atomic_json

        def save(path, value):
            if path.name == "state.json" and value["status"] == "RUNNING":
                raise OSError("running receipt unavailable")
            return original_save(path, value)

        with mock.patch.object(cubic_sheets.branch_builds, "atomic_json", side_effect=save):
            with self.assertRaises(RuntimeError):
                cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        raw = json.loads(next((self.store / "cases").rglob("exit.json")).read_text())
        self.assertIn("running receipt unavailable", raw["errors"][0]["failure"])
        native = json.loads(next((self.store / "cases").rglob("native.json")).read_text())
        self.assertEqual(native["exit_code"], raw["exit_code"])
        self.assertEqual(native["outcome"], "attempt-stopped-or-failed")
        self.assertEqual(native["live_handles"], [])
        self.assertFalse(list((self.store / "cases").rglob("result.json")))

    def test_group_inspection_failure_cannot_erase_a_successful_raw_exit(self):
        with mock.patch.object(cubic_sheets, "group_members", side_effect=OSError("group metadata unavailable")):
            with self.assertRaises(RuntimeError):
                cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        raw = json.loads(next((self.store / "cases").rglob("exit.json")).read_text())
        self.assertEqual(raw, {"exit_code": 0, "errors": []})
        native = json.loads(next((self.store / "cases").rglob("native.json")).read_text())
        self.assertEqual(native["exit_code"], 0)
        self.assertEqual(native["outcome"], "attempt-stopped-or-failed")
        self.assertEqual(native["errors"][0]["phase"], "group")
        self.assertIsNone(native["live_handles"])
        self.assertFalse(list((self.store / "cases").rglob("result.json")))

    def test_raw_receipt_failure_is_retained_and_refuses_acceptance(self):
        original_save = cubic_sheets.branch_builds.atomic_json

        def save(path, value):
            if path.name == "exit.json":
                raise OSError("raw receipt unavailable")
            return original_save(path, value)

        with mock.patch.object(cubic_sheets.branch_builds, "atomic_json", side_effect=save):
            with self.assertRaises(RuntimeError):
                cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"])
        native = json.loads(next((self.store / "cases").rglob("native.json")).read_text())
        self.assertEqual(native["exit_code"], 0)
        self.assertEqual(native["errors"][0]["phase"], "raw_exit_receipt")
        self.assertEqual(native["outcome"], "attempt-stopped-or-failed")
        self.assertFalse(list((self.store / "cases").rglob("result.json")))

    def test_stopping_a_group_stops_children_after_its_leader_exits(self):
        import ctypes
        import os
        import signal

        # Adopt the synthetic orphan so the test can reap it itself instead
        # of leaving zombie cleanup to the host's PID 1.
        libc = ctypes.CDLL(None, use_errno=True)
        previous = ctypes.c_int()
        self.assertEqual(libc.prctl(37, ctypes.byref(previous), 0, 0, 0), 0)
        self.assertEqual(libc.prctl(36, 1, 0, 0, 0), 0)
        child = None
        leader = None
        try:
            program = ("import os,subprocess,sys; "
                       "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); "
                       "print(child.pid,flush=True)")
            leader = subprocess.Popen([sys.executable, "-c", program], stdout=subprocess.PIPE,
                                      start_new_session=True, text=True)
            owner = cubic_sheets.worker_identity(leader.pid)
            child = int(leader.stdout.readline())
            self.assertEqual(leader.wait(), 0)
            self.assertIn(child, cubic_sheets.group_members(owner["pgid"]))
            cubic_sheets.stop_worker_group(owner)
            # Keep the terminated child unreaped while checking liveness.
            # WNOWAIT makes the zombie state deterministic; its parent still
            # has to perform the owning wait below.
            stopped = os.waitid(os.P_PID, child, os.WEXITED | os.WNOWAIT)
            self.assertEqual(stopped.si_pid, child)
            state = (Path("/proc") / str(child) / "stat").read_text().rsplit(")", 1)[1].split()[0]
            self.assertEqual(state, "Z")
            self.assertEqual(cubic_sheets.group_members(owner["pgid"]), [],
                             f"terminated unreaped child {child} has state {state}")
            reaped, status = os.waitpid(child, os.WNOHANG)
            self.assertEqual(reaped, child)
            child = None
            self.assertTrue(os.WIFSIGNALED(status))
            self.assertEqual(os.WTERMSIG(status), signal.SIGTERM)
            self.assertEqual(cubic_sheets.group_members(owner["pgid"]), [])
        finally:
            if child is not None:
                try:
                    os.kill(child, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                os.waitpid(child, 0)
            if leader is not None:
                leader.wait()
                leader.stdout.close()
            self.assertEqual(libc.prctl(36, previous.value, 0, 0, 0), 0)

    def test_changed_leader_identity_is_rejected_without_a_signal(self):
        owner = {"pid": 12345, "pgid": 12345, "start_ticks": "1",
                 "namespace": cubic_sheets.os.stat("/proc/self/ns/pid").st_ino}
        changed = {**owner, "start_ticks": "2"}
        with mock.patch.object(cubic_sheets, "worker_identity", return_value=changed), \
                mock.patch.object(cubic_sheets.os, "killpg") as send:
            with self.assertRaisesRegex(RuntimeError, "leader identity changed"):
                cubic_sheets.stop_worker_group(owner)
        send.assert_not_called()

    def test_actual_winding_cli_shape_uses_same_reader_and_closes_at_eof(self):
        self.install_digest_fixture()
        log, events = io.BytesIO(), io.StringIO()
        process = subprocess.Popen([str(self.binary), "winding-child", "unused", "saved",
                                    "--input-digest-stdio-v1"],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True, bufsize=0)
        try:
            result = cubic_sheets.forward_input_digests(process, log, events)
            self.assertEqual(process.wait(), 0)
            self.assertEqual(result["requests"], 2)
            self.assertTrue(process.stdin.closed)
        finally:
            cubic_sheets.build_costs.stop_owned(process)
            process.stdout.close()

    def test_truncated_or_non_utf8_payload_closes_the_retained_input(self):
        for frame, failure in ((b"CCL_WINDING_SHA256_V1 3\nxy", EOFError),
                               (b"CCL_WINDING_SHA256_V1 1\n\xff", UnicodeDecodeError)):
            with self.subTest(frame=frame):
                command = "import os,sys;sys.stdout.buffer.write(" + repr(frame) + ");sys.stdout.buffer.flush();os.close(1);sys.stdin.buffer.read()"
                process = subprocess.Popen([sys.executable, "-c", command], stdin=subprocess.PIPE,
                                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                           start_new_session=True, bufsize=0)
                try:
                    with self.assertRaises(failure):
                        cubic_sheets.forward_input_digests(process, io.BytesIO(), io.StringIO())
                    self.assertTrue(process.stdin.closed)
                    self.assertEqual(process.wait(), 0)
                finally:
                    cubic_sheets.build_costs.stop_owned(process)
                    process.stdout.close()
                    process.stderr.close()

    def test_digest_option_rejects_nonroot_route_before_production(self):
        with self.assertRaises(ValueError):
            cubic_sheets.run_cases(self.binary, self.root, self.store, ["ordered-invalid"],
                                   input_digest_stdio=True)
        self.assertFalse((self.root / "calls.json").exists())

    def test_unverified_foreign_worker_namespace_is_preserved(self):
        pending = self.root / "pending"
        pending.mkdir()
        state = {"status": "RUNNING", "worker": {"namespace": -1}}
        (pending / "state.json").write_text(json.dumps(state))
        with self.assertRaises(RuntimeError):
            cubic_sheets.preserve_incomplete(pending)
        self.assertEqual(json.loads((pending / "state.json").read_text()), state)

    def test_surviving_worker_group_is_preserved_after_its_leader_exits(self):
        pending = self.root / "pending"
        pending.mkdir()
        state = {"status": "RUNNING", "worker": {
            "namespace": cubic_sheets.os.stat("/proc/self/ns/pid").st_ino,
            "pid": 12345, "pgid": 12345, "start_ticks": "1"}}
        state_path = pending / "state.json"
        state_path.write_text(json.dumps(state))
        original = state_path.read_bytes()
        with mock.patch.object(cubic_sheets, "worker_identity", side_effect=FileNotFoundError), \
                mock.patch.object(cubic_sheets, "group_members", return_value=[12346]) as members:
            with self.assertRaisesRegex(RuntimeError, "group still has live members"):
                cubic_sheets.preserve_incomplete(pending)
        members.assert_called_once_with(12345)
        self.assertEqual(state_path.read_bytes(), original)
        self.assertFalse(list(self.root.glob("pending.interrupted.*")))


if __name__ == "__main__":
    unittest.main()
