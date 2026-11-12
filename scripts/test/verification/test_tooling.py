"""Check parallel coverage, resource bounds and cancellation of isolated workers."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from scripts.paths import ROOT
from scripts.verification import tooling
from scripts.verification.checkpoints import Checkpoints, Inputs


class ToolingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="tooling-pool-tests-")
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        # These fixtures test scheduling/control flow; native prerequisites
        # have their own real IPC and ABI integration controls.
        prerequisite = patch.object(tooling, 'preflight_tooling')
        self.preflight = prerequisite.start()
        self.addCleanup(prerequisite.stop)

    def job(self, name, body, cost=1):
        return name, [sys.executable, "-c", body], cost

    def report(self):
        return json.loads((self.directory / "summary.json").read_text())

    @staticmethod
    def completed_pool_fixture(jobs, directory, workers, memory, **kwargs):
        """Return a synthetic complete pool report for preparation control-flow tests."""
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'summary.json').write_text(json.dumps({
            'status': 'passed', 'inventory': [job[0] for job in jobs],
            'results': [{'name': job[0], 'exit_code': 0, 'raw_exit_code': 0,
                         'timed_out': False} for job in jobs]}))
        return 0

    def test_resume_preserves_success_before_an_unrelated_failure(self):
        counter, flag = self.directory / 'count', self.directory / 'ready'
        jobs = [self.job('already-passed', 'from pathlib import Path; '
                         f'p=Path({str(counter)!r}); p.write_text(str(int(p.read_text())+1 if p.exists() else 1))'),
                self.job('retry', f'from pathlib import Path; raise SystemExit(0 if Path({str(flag)!r}).exists() else 7)')]
        requests = {name: {'name': name, 'command': command, 'fixture_input': 'original'}
                    for name, command, _ in jobs}
        store = Checkpoints(self.directory / 'checkpoints')
        options = dict(checkpoints=store, requests=requests, validate=lambda name: None)
        self.assertEqual(tooling.run_jobs(jobs, self.directory, 1, 2, **options), 7)
        self.assertEqual(counter.read_text(), '1')
        flag.touch()
        requests['retry']['fixture_input'] = 'repaired'
        self.assertEqual(tooling.run_jobs(jobs, self.directory, 1, 2, **options), 0)
        self.assertEqual(counter.read_text(), '1')
        results = {row['name']: row for row in self.report()['results']}
        self.assertEqual(set(results), set(requests))
        self.assertTrue(results['already-passed']['reused'])
        self.assertEqual(self.report()['status'], 'passed')

    def test_changed_inputs_do_not_publish_a_completed_case(self):
        job = self.job('changed', 'pass')
        request = {'name': job[0], 'command': job[1]}
        store = Checkpoints(self.directory / 'checkpoints')
        def changed(name):
            raise ValueError('fixture inputs changed')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            tooling.run_jobs([job], self.directory, 1, 2, checkpoints=store,
                             requests={job[0]: request}, validate=changed)
        self.assertIsNone(store.lookup(request))
        self.assertEqual(self.report()['status'], 'failed')

    def test_resume_skips_horner_preparation_when_all_horner_cases_passed(self):
        # Cache protocol/control-flow fixture; this does not attest a Horner proof.
        from scripts.lean_module_data import supplied
        root = self.directory
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        (root / '.git/info/exclude').write_text('.lake/\n')
        horner = tooling.HORNER_CASE_PREFIX + 'test_actual_horner_supplied_body'
        names = [horner, 'unresolved-host-control']
        environment = dict(os.environ, CCL_COMPLETION_REPORT=str(root / '.git/run'),
                           LEAN_SYSROOT=str(root / 'SDK'))
        environment.pop('FC_SUPPLIED_SESSION_PATH', None)
        environment.pop('FC_SUPPLIED_SESSION_FD', None)
        for key in ('LEAN_PATH', 'CCL_CORE_PREFIX', 'CCL_TEST_CORE_PREFIX'):
            environment.pop(key, None)
        store = Checkpoints(root / '.lake/completion-checkpoints/tooling')
        command = [sys.executable, '-m', 'scripts.verification.tooling', '--case', horner]
        log = root / '.git/completed.log'
        log.write_text('synthetic completed-case control')
        with patch.dict(os.environ, environment, clear=True):
            request = Inputs(root, tooling.worker_environment(horner), store).request(horner, command)
        request['wall_timeout_seconds'] = tooling.TEST_TIMEOUT
        store.save(request, {'name': horner, 'command': command, 'log': str(log),
                            'exit_code': 0, 'raw_exit_code': 0, 'timed_out': False})
        environment[tooling.TIMEOUT_OVERRIDES_ENV] = json.dumps({'unresolved-host-control': 600})
        with patch.dict(os.environ, environment, clear=True), patch.object(tooling, 'ROOT', root), \
                patch.object(tooling, 'inventory', return_value=names), \
                patch.object(tooling, 'run_jobs', side_effect=self.completed_pool_fixture) as run, \
                patch.object(supplied, 'supervise_session', side_effect=AssertionError('must not prepare')) as prepare:
            self.assertEqual(tooling.main(['--resume']), 0)
        prepare.assert_not_called()
        self.assertEqual(self.preflight.call_args.args[0], ['unresolved-host-control'])
        self.assertEqual([job[0] for job in run.call_args.args[0]], names)
        self.assertEqual(set(run.call_args.kwargs['requests']), set(names))
        self.assertEqual(run.call_args.kwargs['requests'][horner]['wall_timeout_seconds'], 300)
        self.assertEqual(run.call_args.kwargs['requests']['unresolved-host-control']['wall_timeout_seconds'], 600)

    def test_resume_survives_launcher_and_pool_changes_but_binds_worker_configuration(self):
        root = self.directory
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        (root / '.git/info/exclude').write_text('.lake/\n')
        directory = root / '.git/run'
        counter = root / '.git/count'
        body = ("import os; from pathlib import Path; "
                "assert 'INVOCATION_ID' not in os.environ; "
                "assert 'CCL_CHECK_MEMORY_BYTES' not in os.environ; "
                "assert 'CCL_TOOLING_JOBS' not in os.environ; "
                "assert 'CCL_LINT_JOBS' not in os.environ; "
                "assert os.environ['CHECKER_FIXTURE_CONFIG']=='kept'; "
                f"p=Path({str(counter)!r}); p.write_text(str(int(p.read_text())+1 if p.exists() else 1))")
        job = self.job('case', body)
        store = Checkpoints(root / '.lake/checkpoints')
        for invocation, budget in (('first', '1024'), ('second', '2048')):
            environment = dict(PATH=os.environ['PATH'], INVOCATION_ID=invocation,
                               SYSTEMD_EXEC_PID=invocation, MEMORY_PRESSURE_WATCH='/unit/' + invocation,
                               CCL_CHECK_MEMORY_BYTES=budget, CCL_TOOLING_JOBS=budget,
                               CCL_LINT_JOBS=budget, CHECKER_FIXTURE_CONFIG='kept')
            with patch.dict(os.environ, environment, clear=True), patch.object(tooling, 'ROOT', root):
                inputs = Inputs(root, tooling.worker_environment('case'), store)
                def request():
                    value = inputs.request('case', job[1])
                    value['wall_timeout_seconds'] = tooling.TEST_TIMEOUT
                    return value
                expected = request()
                self.assertEqual(tooling.run_jobs([job], directory, 1, 1,
                    checkpoints=store, requests={'case': expected},
                    validate=lambda _: self.assertEqual(request(), expected)), 0)
        self.assertEqual(counter.read_text(), '1')
        self.assertTrue(json.loads((directory / 'summary.json').read_text())['results'][0]['reused'])
        environment['CHECKER_FIXTURE_CONFIG'] = 'changed'
        with patch.dict(os.environ, environment, clear=True):
            changed = Inputs(root, tooling.worker_environment('case'), store).request('case', job[1])
            changed['wall_timeout_seconds'] = tooling.TEST_TIMEOUT
        self.assertIsNone(store.lookup(changed))

    def test_case_timeout_override_preserves_the_other_case_deadline(self):
        extended = self.job('extended', 'import time; time.sleep(.1)')
        ordinary = self.job('ordinary', 'import time; time.sleep(2)')
        with patch.multiple(tooling, TEST_TIMEOUT=.05, TERMINATION_GRACE=.05):
            self.assertEqual(tooling.run_jobs([extended, ordinary], self.directory, 1, 1,
                                             case_timeouts={'extended': 1}), 124)
        first, second = self.report()['results']
        self.assertEqual(first['exit_code'], 0)
        self.assertEqual(first['wall_timeout_seconds'], 1)
        self.assertEqual(second['exit_code'], 124)
        self.assertEqual(second['wall_timeout_seconds'], .05)

    def test_timeout_overrides_reject_unknown_unbounded_and_invalid_cases(self):
        for values in ([], {'unknown': 600}, {'case': True}, {'case': 0},
                       {'case': float('nan')}, {'case': float('inf')}, {'case': 601}):
            with self.subTest(values=values), self.assertRaises(ValueError):
                tooling.timeout_overrides(['case'], {tooling.TIMEOUT_OVERRIDES_ENV: json.dumps(values)})
        self.assertEqual(tooling.timeout_overrides(['case'], {
            tooling.TIMEOUT_OVERRIDES_ENV: '{"case": 600}'}), {'case': 600})
        with patch.dict(os.environ, {tooling.TIMEOUT_OVERRIDES_ENV: '{"case": 600}'}):
            self.assertNotIn(tooling.TIMEOUT_OVERRIDES_ENV, tooling.worker_environment('case'))

    def test_only_horner_workers_receive_the_prepared_socket(self):
        body = ("import json,os; print(json.dumps({key:os.environ.get(key) for key in "
                "('FC_SUPPLIED_SESSION_PATH','FC_SUPPLIED_SESSION_FD')}))")
        horner = tooling.HORNER_CASE_PREFIX + "test_actual_horner_supplied_body"
        jobs = [self.job(horner, body), self.job("independent-native-crash-fixture", body)]
        with patch.dict(os.environ, FC_SUPPLIED_SESSION_PATH="owned-session.sock",
                        FC_SUPPLIED_SESSION_FD="123"):
            self.assertEqual(tooling.run_jobs(jobs, self.directory, 2, 2), 0)
        for row in self.report()["results"]:
            result = json.loads(Path(row["log"]).read_text())
            self.assertIsNone(result["FC_SUPPLIED_SESSION_FD"])
            self.assertEqual(result["FC_SUPPLIED_SESSION_PATH"],
                             "owned-session.sock" if row["name"] == horner else None)

    def test_resume_checks_independent_cases_before_preparing_the_live_producer(self):
        from scripts.lean_module_data import supplied
        root = self.directory
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        (root / '.git/info/exclude').write_text('.lake/\n')
        names = [tooling.HORNER_CASE_PREFIX + 'test_actual_horner_supplied_body',
                 'independent-control']
        environment = dict(CCL_COMPLETION_REPORT=str(root / '.git/run'),
                           LEAN_SYSROOT=str(root / 'SDK'))
        for independent_exit in (7, 0):
            with self.subTest(independent_exit=independent_exit):
                events = []
                def pool(jobs, directory, workers, memory, **options):
                    events.append([job[0] for job in jobs])
                    self.completed_pool_fixture(jobs, directory, workers, memory, **options)
                    if directory.name == 'independent':
                        self.assertEqual(set(options['requests']), {'independent-control'})
                        if independent_exit:
                            path = directory / 'summary.json'
                            report = json.loads(path.read_text())
                            report['status'] = 'failed'
                            report['results'][0]['exit_code'] = independent_exit
                            path.write_text(json.dumps(report))
                        return independent_exit
                    return 0
                def ready(*args, **options):
                    self.assertEqual(events, [['independent-control']])
                    options['on_ready']()
                    with patch.dict(os.environ, FC_SUPPLIED_SESSION_PATH='ready.sock'):
                        return tooling.main(['--resume'])
                with patch.dict(os.environ, environment, clear=True), \
                        patch.object(tooling, 'ROOT', root), \
                        patch.object(tooling, 'inventory', return_value=names), \
                        patch.object(tooling, 'run_jobs', side_effect=pool), \
                        patch.object(supplied, 'supervise_session', side_effect=ready) as prepare:
                    self.assertEqual(tooling.main(['--resume']), independent_exit)
                if independent_exit:
                    prepare.assert_not_called()
                    self.assertEqual(events, [['independent-control']])
                else:
                    prepare.assert_called_once()
                    self.assertEqual(events, [['independent-control'], names])

    def test_main_prepares_once_before_launching_the_complete_inventory(self):
        from scripts.lean_module_data import supplied
        names = [tooling.HORNER_CASE_PREFIX + name for name in (
            "test_actual_horner_supplied_body", "test_supplied_unresolved_constant_reaches_kernel",
            "test_supplied_metavariable_reaches_kernel", "test_supplied_loose_index_reaches_kernel",
            "test_supplied_wrong_type_reaches_kernel")]
        names.append("scripts.test.verification.test_tooling.ToolingTests.test_worker_affinity_is_inherited_by_grandchildren")
        environment = {"LEAN_SYSROOT": str(self.directory / "toolchain"),
                       "CCL_COMPLETION_REPORT": str(self.directory),
                       "CCL_TOOLING_JOBS": "3", "CCL_CHECK_MEMORY_BYTES": str(48 * tooling.GIB)}
        with patch.dict(os.environ, environment, clear=True), patch.object(tooling, "inventory", return_value=names), \
                patch.object(tooling, "run_jobs", side_effect=self.completed_pool_fixture) as pool:
            def ready(*args, **kwargs):
                pool.assert_not_called()
                self.assertEqual(args[-1], [sys.executable, "-m", "scripts.verification.tooling"])
                self.assertEqual(args[0], "Purelib.Approximation.Gaussian.Exponential.E")
                kwargs['on_ready']()
                with patch.dict(os.environ, FC_SUPPLIED_SESSION_PATH="ready-session.sock"):
                    return tooling.main([])
            with patch.object(supplied, "supervise_session", side_effect=ready) as prepare:
                self.assertEqual(tooling.main([]), 0)
            prepare.assert_called_once()
            pool.assert_called_once()
            jobs, directory, workers, memory = pool.call_args.args
            self.assertEqual([job[0] for job in jobs], names)
            self.assertEqual((directory, workers, memory),
                             (self.directory / "tooling-tests", 3, 48 * tooling.GIB))
            self.assertEqual((tooling.TEST_TIMEOUT, tooling.TERMINATION_GRACE), (300, 15))

    def test_failed_preparation_never_launches_isolated_cases(self):
        from scripts.lean_module_data import supplied
        names = [tooling.HORNER_CASE_PREFIX + "test_actual_horner_supplied_body"]
        with patch.dict(os.environ, {"LEAN_SYSROOT": str(self.directory),
                                    "CCL_COMPLETION_REPORT": str(self.directory)}, clear=True), \
                patch.object(tooling, "inventory", return_value=names), \
                patch.object(tooling, "run_jobs") as pool, \
                patch.object(supplied, "supervise_session", side_effect=RuntimeError("not ready")):
            with self.assertRaisesRegex(RuntimeError, "not ready"):
                tooling.main([])
            pool.assert_not_called()
        self.assertEqual(json.loads((self.directory / 'tooling-tests/summary.json').read_text())['status'], 'failed')

    def test_interrupted_preparation_is_recorded_before_any_test_starts(self):
        from scripts.lean_module_data import supplied
        names = [tooling.HORNER_CASE_PREFIX + 'test_actual_horner_supplied_body']
        with patch.dict(os.environ, {'LEAN_SYSROOT': str(self.directory),
                                    'CCL_COMPLETION_REPORT': str(self.directory)}, clear=True), \
                patch.object(tooling, 'inventory', return_value=names), \
                patch.object(tooling, 'run_jobs') as pool, \
                patch.object(supplied, 'supervise_session', side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                tooling.main([])
        pool.assert_not_called()
        self.assertEqual(json.loads((self.directory / 'tooling-tests/summary.json').read_text())['status'], 'interrupted')
        self.assertEqual(json.loads((self.directory / 'tooling-tests/setup.json').read_text())['status'], 'interrupted')

    def test_native_preflight_failure_prevents_expensive_producer_preparation(self):
        from scripts.lean_module_data import supplied
        names = [tooling.HORNER_CASE_PREFIX + 'test_actual_horner_supplied_body']
        self.preflight.side_effect = ValueError('native ABI mismatch')
        with patch.dict(os.environ, {'LEAN_SYSROOT': str(self.directory),
                                    'CCL_COMPLETION_REPORT': str(self.directory)}, clear=True), \
                patch.object(tooling, 'inventory', return_value=names), \
                patch.object(supplied, 'supervise_session') as producer:
            with self.assertRaisesRegex(ValueError, 'native ABI mismatch'):
                tooling.main([])
        producer.assert_not_called()
        saved = json.loads((self.directory / 'tooling-tests/summary.json').read_text())
        self.assertEqual(saved['status'], 'failed')
        self.assertIn('native ABI mismatch', saved['error'])
        setup = json.loads((self.directory / 'tooling-tests/setup.json').read_text())
        self.assertEqual((setup['status'], setup['phase']), ('failed', 'native-preflight'))

    def test_interruption_during_input_binding_records_its_phase(self):
        names = ['scripts.test.fixture.Case.test_one']
        with patch.dict(os.environ, {'CCL_COMPLETION_REPORT': str(self.directory)}, clear=True), \
                patch.object(tooling, 'inventory', return_value=names), \
                patch.object(tooling, 'Inputs') as inputs:
            inputs.return_value.request.side_effect = KeyboardInterrupt
            with self.assertRaises(KeyboardInterrupt):
                tooling.main(['--resume'])
        setup = json.loads((self.directory / 'tooling-tests/setup.json').read_text())
        self.assertEqual((setup['status'], setup['phase']), ('interrupted', 'input-binding'))
        self.assertEqual(json.loads((self.directory / 'tooling-tests/summary.json').read_text())['status'], 'interrupted')

    def test_isolated_horner_worker_requires_readiness_before_class_setup(self):
        name = tooling.HORNER_CASE_PREFIX + "test_actual_horner_supplied_body"
        with patch.dict(os.environ, {}, clear=True), \
                patch.object(unittest.defaultTestLoader, "loadTestsFromName") as load:
            with self.assertRaisesRegex(ValueError, "prepared production session"):
                tooling.main(["--case", name])
            load.assert_not_called()

    def test_workers_overlap_and_preserve_complete_logs_and_coverage(self):
        # Two cooperating processes prove overlap even on a single-core host.
        jobs = []
        for name, other in (("left", "right"), ("right", "left")):
            body = f"""import time
from pathlib import Path
p = Path({str(self.directory)!r})
(p / {name!r}).touch()
deadline = time.monotonic() + 5
while not (p / {other!r}).exists() and time.monotonic() < deadline: time.sleep(.01)
assert (p / {other!r}).exists(), 'workers did not overlap'
print({name!r})
"""
            jobs.append(self.job(name, body))
        affinity = list(os.sched_getaffinity(0))
        with patch.object(tooling.os, "sched_getaffinity", return_value=[affinity[0], affinity[0]]):
            self.assertEqual(tooling.run_jobs(jobs, self.directory, 2, 2), 0)
        report = self.report()
        self.assertEqual(report["peak_workers"], 2)
        self.assertEqual({r["name"] for r in report["results"]}, {"left", "right"})
        for row in report["results"]:
            self.assertEqual(Path(row["log"]).read_text().strip(), row["name"])

    def test_memory_reservations_serialize_heavy_jobs(self):
        jobs = [self.job(str(i), "import time; time.sleep(.05)", 2) for i in range(3)]
        self.assertEqual(tooling.run_jobs(jobs, self.directory, 3, 2), 0)
        self.assertEqual(self.report()["peak_workers"], 1)

    def test_worker_affinity_is_inherited_by_grandchildren(self):
        job = self.job("affinity", "import os,subprocess,sys; "
                       "assert len(os.sched_getaffinity(0)) == 1; "
                       "subprocess.run([sys.executable,'-c',"
                       "'import os; assert len(os.sched_getaffinity(0)) == 1'],check=True)")
        self.assertEqual(tooling.run_jobs([job], self.directory, 1, 1), 0)

    def test_timeout_rejects_zero_exit_and_stops_before_pending_job(self):
        slow = self.job("slow", "import os,signal,sys,time; "
                        "signal.signal(signal.SIGTERM, lambda *_: sys.exit(0)); "
                        "os.close(1); os.close(2); time.sleep(30)")
        later = self.directory / "later"
        pending = self.job("pending", f"from pathlib import Path; Path({str(later)!r}).touch()")
        with patch.multiple(tooling, TEST_TIMEOUT=.6, TERMINATION_GRACE=.05):
            self.assertEqual(tooling.run_jobs([slow, pending], self.directory, 1, 1), 124)
        report = self.report()
        self.assertEqual(report["status"], "failed")
        self.assertEqual(len(report["results"]), 1)
        result = report["results"][0]
        self.assertTrue(result["timed_out"])
        self.assertEqual(result["raw_exit_code"], 0)
        self.assertEqual(result["exit_code"], 124)
        self.assertFalse(later.exists())

    def test_timeout_kills_detached_term_resistant_descendant(self):
        ready = self.directory / "child"
        child = ("import os,signal,time; from pathlib import Path; "
                 "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                 f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(30)")
        parent = ("import signal,subprocess,sys,time; "
                  "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                  f"subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True); time.sleep(30)")
        with patch.multiple(tooling, TEST_TIMEOUT=1, TERMINATION_GRACE=.05):
            self.assertEqual(tooling.run_jobs([self.job("slow", parent)], self.directory, 1, 1), 124)
        self.assertEqual(self.report()["results"][0]["raw_exit_code"], -signal.SIGKILL)
        self.assertIsNone(tooling.process_record(int(ready.read_text()), live=True))

    def test_failure_cancels_owned_descendants_in_separate_sessions(self):
        ready = self.directory / "ready"
        sleeper = "import os,time; from pathlib import Path; " + f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(60)"
        helper = self.job("helper", f"import subprocess,sys,time; "
                          f"subprocess.Popen([sys.executable,'-c',{sleeper!r}],start_new_session=True); time.sleep(60)")
        failure = self.job("failure", f"import time; from pathlib import Path; p=Path({str(ready)!r}); "
                           "\ndeadline=time.monotonic()+5\n"
                           "while not p.exists() and time.monotonic()<deadline: time.sleep(.01)\n"
                           "time.sleep(.3)\nraise SystemExit(9)")
        affinity = list(os.sched_getaffinity(0))
        with patch.object(tooling.os, "sched_getaffinity", return_value=[affinity[0], affinity[0]]):
            self.assertEqual(tooling.run_jobs([helper, failure], self.directory, 2, 2), 9)
        self.assertEqual(self.report()["status"], "failed")
        self.assertIsNone(tooling.process_record(int(ready.read_text()), live=True))

    def test_interruption_retains_summary_and_reaps_workers(self):
        ready = self.directory / "ready"
        job = self.job("slow", f"import os,time; from pathlib import Path; "
                       f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(60)")
        harness = f"""import signal
from pathlib import Path
from scripts.verification.tooling import run_jobs
def interrupt(signum, frame): raise KeyboardInterrupt
signal.signal(signal.SIGTERM, interrupt)
try: run_jobs([{job!r}], Path({str(self.directory)!r}), 1, 1)
except KeyboardInterrupt: raise SystemExit(130)
"""
        process = subprocess.Popen([sys.executable, "-c", harness], cwd=ROOT,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            deadline = time.monotonic() + 10
            while not ready.exists() and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(ready.exists())
            process.send_signal(signal.SIGTERM)
            self.assertEqual(process.wait(timeout=10), 130)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
        self.assertEqual(self.report()["status"], "interrupted")
        self.assertIsNone(tooling.process_record(int(ready.read_text()), live=True))


if __name__ == "__main__":
    unittest.main()
