"""Exercise the original epoch reader's completed and live foreign-cache boundaries.

The tiny byte fixtures test cache metadata only; they are not Lean artifacts or
mathematical proof evidence. Reader cases invoke no compiler; timeout cases use
a synthetic child process rather than Lean.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest

from scripts.verification.processes import process_record

OWNER = Path(__file__).resolve().parents[2] / "toolchain/epoch_worker.py"
PARTS = (".olean", ".olean.server", ".olean.private", ".ir", ".ilean", ".c")


def digest(value):
    """Use the owner's retained canonical request encoding."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def bind(path):
    """Bind one deliberately synthetic reader-fixture byte file."""
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def put(path, value):
    """Write an input fixture before the actual reader is launched."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")


class EpochReaderTests(unittest.TestCase):
    """A complete foreign receipt reuses bytes; unfinished and stale bytes fail."""

    def fixture(self, directory, *, complete=True, stale=False, state="TERMINAL"):
        root = Path(directory)
        source = root / "CacheReader.lean"
        source.write_text("module\n")
        host = bind(Path("/usr/bin/false"))
        context = {"module": "CacheReader", "package": "readerFixture", "isModule": True}
        recovery = root / "recovery.json"
        contexts = root / "contexts.json"
        graph = root / "graph.json"
        put(recovery, {"rows": [], "original_sources": [{"module": "CacheReader", "immutable": bind(source)}]})
        put(contexts, {"rows": [context]})
        put(graph, {"CacheReader": []})
        request = {"root_private_compilation_authorized": True, "source_in_place": True,
                   "host": host, "recovery": bind(recovery), "contexts": bind(contexts),
                   "full_import_graph": bind(graph), "topological_order": ["CacheReader"]}
        request_path = root / "request.json"
        put(request_path, request)
        out = root / ".lake/reader-epoch"
        setup = {"name": "CacheReader", "package": "readerFixture", "isModule": True,
                 "imports": None, "importArts": {}, "options": {}, "dynlibs": [], "plugins": []}
        key = {"source": bind(source), "module": "CacheReader", "host": host,
               "setup": setup, "all_import_parts": [], "context": context}
        job = out / "jobs/CacheReader" / digest(key)
        job.mkdir(parents=True)
        setup_path = job / "setup.json"
        put(setup_path, setup)
        parts = {}
        for extension in PARTS:
            part = job / ("synthetic-reader-fixture" + extension)
            part.write_bytes(("READER-ONLY, NOT A LEAN ARTIFACT " + extension).encode())
            parts[extension] = bind(part)
        state_path = job / "STATE.json"
        put(state_path, {"key": key, "status": state, "exit_code": 0,
                         "worker": {"namespace": os.stat("/proc/self/ns/pid").st_ino + 1,
                                    "pid": 999999, "pgid": 999999, "start_ticks": "0"}})
        if complete:
            put(job / "COMPILE.json", {"key": key, "exit_code": 0, "parts": parts,
                "status": "PASS_PRIVATE_COMPLETE_EMISSION_PENDING_DOWNSTREAM_KERNEL_AUDIT",
                "source": bind(source), "setup": bind(setup_path), "live_handles": [],
                "seconds": 0.0, "whole_owned_PGID_peak_rss_kib": 0})
        if stale:
            Path(parts[".ir"]["path"]).write_bytes(b"CORRUPT READER FIXTURE")
        preserved = {str(p): p.read_bytes() for p in job.rglob("*") if p.is_file()}
        return request_path, out, job, preserved

    def invoke(self, request, out):
        return subprocess.run([sys.executable, str(OWNER), "--request", str(request),
                               "--out", str(out), "--jobs", "1"], capture_output=True, text=True)

    def test_complete_foreign_preserves_original_receipts_and_parts(self):
        with tempfile.TemporaryDirectory() as directory:
            request, out, job, preserved = self.fixture(directory)
            result = self.invoke(request, out)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("REUSE CacheReader", result.stdout)
            self.assertTrue((out / "EPOCH.json").is_file())
            self.assertEqual({str(p): p.read_bytes() for p in job.rglob("*") if p.is_file()}, preserved)

    def test_incomplete_foreign_still_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            request, out, job, preserved = self.fixture(directory, complete=False, state="RUNNING")
            result = self.invoke(request, out)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Cannot rule out worker in another process namespace", result.stderr)
            self.assertFalse((out / "EPOCH.json").exists())
            self.assertEqual({str(p): p.read_bytes() for p in job.rglob("*") if p.is_file()}, preserved)

    def test_stale_complete_part_still_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            request, out, job, preserved = self.fixture(directory, stale=True)
            result = self.invoke(request, out)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("synthetic-reader-fixture.ir", result.stderr)
            self.assertNotIn("REUSE CacheReader", result.stdout)
            self.assertFalse((out / "EPOCH.json").exists())
            self.assertEqual({str(p): p.read_bytes() for p in job.rglob("*") if p.is_file()}, preserved)

    def test_success_without_terminal_state_still_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            request, out, job, preserved = self.fixture(directory, state="RUNNING")
            result = self.invoke(request, out)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn("REUSE CacheReader", result.stdout)
            self.assertFalse((out / "EPOCH.json").exists())
            self.assertEqual({str(p): p.read_bytes() for p in job.rglob("*") if p.is_file()}, preserved)

    def test_fresh_worker_timeout_stops_compiler_and_never_publishes_success(self):
        # Accelerate only the supervisor clock; the synthetic host is a normal
        # child process, so both TERM handling and KILL escalation are exercised.
        for resist in (False, True):
            with self.subTest(resist=resist), tempfile.TemporaryDirectory() as directory:
                request, out, _, _ = self.fixture(directory)
                root = Path(directory)
                pid_path, stopped_path = root / 'pid', root / 'terminated'
                host = root / 'synthetic-compiler'
                host.write_text(f'#!{sys.executable}\n'
                    'import os,signal,time\nfrom pathlib import Path\n'
                    'def stop(*_):\n'
                    f'    Path({str(stopped_path)!r}).touch()\n'
                    + ('    return\n' if resist else '    raise SystemExit(0)\n') +
                    'signal.signal(signal.SIGTERM, stop)\n'
                    f'Path({str(pid_path)!r}).write_text(str(os.getpid()))\n'
                    'while True: time.sleep(.02)\n')
                host.chmod(0o755)
                data = json.loads(request.read_text())
                data['host'] = bind(host)
                put(request, data)
                harness = ('import runpy,sys,time\n'
                           'real=time.monotonic; start=real()\n'
                           'time.monotonic=lambda: start+(real()-start)*1000\n'
                           'sys.argv=sys.argv[1:]\n'
                           'runpy.run_path(sys.argv[0],run_name="__main__")\n')
                result = subprocess.run([sys.executable, '-c', harness, str(OWNER),
                    '--request', str(request), '--out', str(out), '--jobs', '1'],
                    capture_output=True, text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('exceeded 120s', result.stdout)
                self.assertTrue(stopped_path.exists(), result.stderr)
                self.assertFalse((out / 'EPOCH.json').exists())
                timed_out = [json.loads(p.read_text()) for p in out.rglob('COMPILE.json')
                             if json.loads(p.read_text()).get('timed_out')]
                self.assertEqual(len(timed_out), 1)
                self.assertEqual(timed_out[0]['exit_code'], 124)
                self.assertEqual(timed_out[0]['parts'], {})
                self.assertIsNone(process_record(int(pid_path.read_text()), live=True))


if __name__ == "__main__":
    unittest.main()
