"""Compare query concurrency on actual compact data, without a proof-pass claim."""
import gc
import multiprocessing
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from scripts.lean_module_data import audit_workers
from scripts.lean_module_data.audit import AuditObservation
from scripts.lean_module_data.importer import Graph
from scripts.lean_module_data.observations import name_observer
from scripts.lean_module_data.paths import search_path

@unittest.skipUnless(hasattr(os, 'fork') and len(os.sched_getaffinity(0)) >= 2, 'parallel process controls require two allowed Linux CPUs')
class ParallelQueryTests(unittest.TestCase):

    def setUp(self):
        """Budget these tiny fixtures independently of whole-library reservations."""
        budget = patch.object(audit_workers, 'worker_count', side_effect=lambda cores, *_: min(cores, 2))
        budget.start()
        self.addCleanup(budget.stop)

    def observation(self):
        """Compare two genuine modules without claiming other imported cache entries."""
        root = next((path for path in search_path() if (path / 'Lean/Expr.olean').is_file()))
        obs = AuditObservation.__new__(AuditObservation)
        obs.graph = Graph([root])
        obs.constants = {}
        obs.by_name = {}
        obs.names = {}
        obs.owners = {}
        obs.state = {}
        obs.axiom_tables = {}
        obs.dependency_projections = {}
        for module in ('Init.Prelude', 'Lean.Expr'):
            mod = obs.graph.load(module)
            obs.state[module] = {'module': mod}
            for key, ref, _ in mod.entries(True):
                name = name_observer(ref.d, ref.name)
                obs.constants[key] = ref
                obs.by_name[name] = ref
                obs.names[key] = name
                obs.owners[name] = module
        obs.axiom_tables = {module: [] for module in obs.state}
        return obs

    def test_exact_query_order_duplicates_and_parent_environment_are_preserved(self):
        serial = self.observation()
        queries = list(serial.by_name)
        queries += queries[::7]
        expected = audit_workers.closures(serial, queries, 1)
        parallel = self.observation()
        before = len(parallel.graph.nodes.nodes)
        actual = audit_workers.closures(parallel, queries, 2)
        self.assertEqual(actual, expected)
        self.assertTrue(parallel.dependency_projections)
        self.assertFalse(any((n['kind'] == 'Expr' for n in parallel.graph.nodes.nodes[before:])))
        self.assertFalse(multiprocessing.active_children())
        self.assertFalse(Path(f'/proc/self/task/{os.getpid()}/children').read_text().strip())

    def test_worker_crash_and_incomplete_results_fail_and_reap_the_pool(self):
        controls = [('import os; os._exit(7)', RuntimeError), ('import pickle,sys; pickle.load(sys.stdin.buffer); pickle.dump([],sys.stdout.buffer); sys.stdout.buffer.flush()', ValueError)]
        for code, exception in controls:
            with self.subTest(code=code), patch.object(audit_workers, 'worker_command', return_value=[sys.executable, '-c', code]):
                obs = self.observation()
                enabled = gc.isenabled()
                with self.assertRaises(exception):
                    audit_workers.closures(obs, list(obs.by_name)[:3], 2)
                self.assertEqual(gc.isenabled(), enabled)
                self.assertFalse(multiprocessing.active_children())
                self.assertFalse(Path(f'/proc/self/task/{os.getpid()}/children').read_text().strip())

    def test_sealed_inventory_keeps_closures_and_original_reference_parts(self):
        serial = self.observation()
        queries = list(serial.by_name)
        expected = audit_workers.closures(serial, queries, 1)
        sealed = self.observation()
        original = [(ref, ref.d.parts, ref.ptr, ref.key) for ref in sealed.constants.values()]
        sealed.seal_inventory()
        self.assertFalse(sealed.graph.nodes.nodes)
        for ref, parts, pointer, key in original:
            self.assertIs(ref.d.parts, parts)
            self.assertEqual((ref.ptr, ref.key), (pointer, key))
        with self.assertRaisesRegex(ValueError, 'sealed'):
            sealed.inventory('Init.Prelude')
        self.assertEqual(audit_workers.closures(sealed, queries, 2), expected)

    def test_invalid_core_count_is_rejected_before_work(self):
        with self.assertRaisesRegex(ValueError, 'positive'):
            audit_workers.closures(None, [], 0)

    def test_sigterm_cancels_workers_and_preserves_the_interruption(self):
        from scripts.paths import ROOT
        from scripts.verification.processes import process_record
        with tempfile.TemporaryDirectory(prefix='axiom-pool-cancel-') as temporary:
            directory = Path(temporary)
            control = 'import os,pickle,time; from pathlib import Path; from scripts.verification.processes import process_record; pickle.load(__import__("sys").stdin.buffer); Path(os.environ["AXIOM_POOL_CONTROL"],str(os.getpid())).write_text(str(process_record(os.getpid())[0])); time.sleep(60)'
            code = "import signal,sys\nfrom unittest.mock import patch\nfrom scripts.lean_module_data import audit_workers\nfrom scripts.test.axioms.test_parallel import ParallelQueryTests\nobs=ParallelQueryTests().observation()\nwith patch.object(audit_workers,'worker_command',return_value=[sys.executable,'-c',sys.argv[1]]), patch.object(audit_workers,'worker_count',return_value=2):\n    audit_workers.closures(obs,list(obs.by_name)[:256],2)\n"
            process = subprocess.Popen([sys.executable, '-c', code, control], cwd=ROOT, env=dict(os.environ, AXIOM_POOL_CONTROL=temporary), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                deadline = time.monotonic() + 15
                while len(list(directory.iterdir())) < 2 and time.monotonic() < deadline:
                    if process.poll() is not None:
                        break
                    time.sleep(0.02)
                identities = {int(path.name): int(path.read_text()) for path in directory.iterdir()}
                self.assertEqual(len(identities), 2)
                process.send_signal(signal.SIGTERM)
                _, error = process.communicate(timeout=20)
                self.assertNotEqual(process.returncode, 0, error)
                for pid, started in identities.items():
                    now = process_record(pid, live=True)
                    self.assertTrue(now is None or now[0] != started, (pid, now))
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate()

class WorkerBudgetTests(unittest.TestCase):

    def test_private_worker_memory_is_reserved_after_import_loading(self):
        with patch('scripts.verification.completion.available_memory', return_value=3 * 1024 ** 3), patch.dict(os.environ, {}, clear=True):
            self.assertEqual(audit_workers.worker_count(5), 5)
        for available in (None, 0, 512 * 1024 ** 2):
            with self.subTest(available=available), patch('scripts.verification.completion.available_memory', return_value=available), patch.dict(os.environ, {}, clear=True):
                self.assertEqual(audit_workers.worker_count(5), 1)

    def test_independent_import_environments_share_the_total_memory_budget(self):
        with patch('scripts.verification.completion.available_memory', return_value=6 * 1024 ** 3), patch.dict(os.environ, AXIOM_AUDIT_JOBS='2', CCL_CHECK_MEMORY_BYTES=str(8 * 1024 ** 3)), patch.object(Path, 'read_text', return_value='0 524288'), patch.object(os, 'sysconf', return_value=4096):
            self.assertEqual(audit_workers.worker_count(8), 4)
