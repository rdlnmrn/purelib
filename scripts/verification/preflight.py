"""Check local IPC, native ABI and publication prerequisites before long work."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import tempfile
import time

from scripts.paths import ROOT
from scripts.verification.checkpoints import atomic_json


def sockets():
    """Exercise the actual local socket mechanisms used by supplied-body sessions."""
    try:
        with tempfile.TemporaryDirectory(prefix='supplied-listener-') as directory:
            left, right = socket.socketpair()
            with left, right:
                left.settimeout(2)
                right.settimeout(2)
                left.sendall(b'P')
                if right.recv(1) != b'P':
                    raise ValueError('invalid local socketpair response')
            path = Path(directory) / 'session.sock'
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener, \
                    socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                listener.settimeout(2)
                client.settimeout(2)
                listener.bind(str(path))
                os.chmod(path, 0o600)
                listener.listen(1)
                client.connect(str(path))
                connection, _ = listener.accept()
                with connection:
                    connection.settimeout(2)
                    client.sendall(b'P')
                    if connection.recv(1) != b'P':
                        raise ValueError('invalid local listener response')
                    connection.sendall(b'R')
                    if client.recv(1) != b'R':
                        raise ValueError('invalid local client response')
    except OSError as error:
        raise ValueError('local socket preflight failed before producer preparation: ' + str(error)) from error


def command(name, arguments, root, directory, environment):
    """Run a prerequisite under the existing watchdog and descendant supervision."""
    from scripts.verification.completion import run_stage
    result = run_stage(name, arguments, Path(directory), environment, Path(root))
    if result['exit_code']:
        raise ValueError(f"{name} failed; see {result['log']}")
    return result


def native_tools(root, directory, environment, *, kernel=False, nanoda=True):
    """Link real native adapters against the currently selected libraries and SDK."""
    Path(directory).mkdir(parents=True, exist_ok=True)
    results = []
    if nanoda:
        try:
            results.append(command('nanoda-preflight', ['scripts/build-nanoda-module-checker.sh'],
                                   root, directory, environment))
        except ValueError as error:
            raise ValueError(str(error) + '; build the pinned native library with '
                             'cargo build --release --locked in .external/nanoda') from error
    if kernel:
        results.append(command('kernel-preflight', [sys.executable, '-m',
                              'scripts.verification.preflight', '--kernel'], root, directory, environment))
    return results


def source(root, expected=None):
    """Require a clean tracked checkout of the intended private source commit."""
    root = Path(root)
    try:
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=root)
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    except subprocess.CalledProcessError as error:
        raise ValueError('cannot identify the private publication source') from error
    if dirty:
        raise ValueError('publication checking requires a clean tracked source checkout')
    if expected is not None and head != expected:
        raise ValueError('private release source changed during checks')
    return head


def publication(root, directory, environment, tag):
    """Check history/destination readiness and pin the exact clean private source."""
    root = Path(root)
    head = source(root)
    result = command('publication-preflight', ['scripts/maintenance/public-history.sh', 'preflight', tag],
                     root, directory, environment)
    pins = re.findall(r'^public-history: preflight source ([0-9a-f]{40})$',
                      Path(result['log']).read_text(), re.MULTILINE)
    if len(pins) != 1 or pins[0] != head:
        raise ValueError('check out the exact private release source before running its full checks')
    source(root, head)
    return dict(result, source_commit=head)


def tooling(names, root, directory, environment):
    """Prepare only the native prerequisites required by unresolved test cases."""
    kernel = any(name.startswith('scripts.test.lean_module_data.test_kernel_equivalence.') for name in names)
    nanoda = any(name.startswith('scripts.test.nanoda.') for name in names)
    if kernel:
        print('Checking local socket access before producer preparation', flush=True)
        sockets()
    if kernel or nanoda:
        print('Checking native tool compatibility before tooling execution', flush=True)
        native_tools(root, directory, environment, kernel=kernel, nanoda=nanoda)


def run(root, directory, environment, *, release=None):
    """Record preflight failure or interruption before any source gate is started."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    report = {'status': 'running', 'phase': 'preflight', 'steps': [], 'active_step': None}
    started = time.monotonic()
    atomic_json(directory / 'preflight.json', report)
    try:
        if release is not None:
            report['active_step'] = 'publication'
            atomic_json(directory / 'preflight.json', report)
            report['steps'].append(publication(root, directory, environment, release))
        report['active_step'] = 'sockets'
        atomic_json(directory / 'preflight.json', report)
        print('Checking local socket access', flush=True)
        sockets()
        report['steps'].append({'name': 'sockets', 'exit_code': 0})
        report['active_step'] = 'native-tools'
        atomic_json(directory / 'preflight.json', report)
        report['steps'].extend(native_tools(root, directory, environment))
        report['active_step'] = None
        report['status'] = 'passed'
        return report
    except KeyboardInterrupt:
        report['status'] = 'interrupted'
        raise
    except BaseException as error:
        report['status'] = 'failed'
        report['error'] = str(error)
        raise
    finally:
        report['seconds'] = time.monotonic() - started
        atomic_json(directory / 'preflight.json', report)
        if report['status'] != 'passed':
            atomic_json(directory / 'summary.json', dict(report, stages=[]))


def main(argv=None):
    """Build the C adapter without preparing any supplied Lean source witness."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel', action='store_true', required=True)
    parser.parse_args(argv)
    from scripts.lean_module_data.kernel import Bindings, native_build
    prefix = os.environ.get('LEAN_SYSROOT')
    if not prefix:
        raise ValueError('kernel preflight requires LEAN_SYSROOT; run through scripts/run-lake.sh env')
    print(native_build(Path(prefix), ROOT / '.lake/kernel-replay-tests', Bindings()))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
