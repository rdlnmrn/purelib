"""Own exporter/checker process sessions and cancel their retained descendants."""

import os
from pathlib import Path
import signal
import subprocess
import threading
import time


def process_record(pid, *, live=False):
    """Read Linux PID/start identity and session without relying on command strings."""
    try:
        value = (Path('/proc') / str(pid) / 'stat').read_text()
        fields = value[value.rindex(')') + 2:].split()
        if live and fields[0] == 'Z':
            return None
        return int(fields[19]), int(fields[2]), int(fields[3])
    except (FileNotFoundError, ProcessLookupError):
        return None


class ProcessSessions:
    """Launch owned sessions and preserve child identity after a leader exits."""

    def __init__(self):
        self.lock = threading.Lock()
        self.running = {}
        self.cancelled = False

    @staticmethod
    def observe(process, identities):
        """Retain exact identities of members of this process's original session."""
        leader = process_record(process.pid)
        if leader is not None and leader != identities.get(process.pid):
            return
        for folder in Path('/proc').iterdir():
            if not folder.name.isdecimal():
                continue
            record = process_record(int(folder.name))
            if record is not None and record[1:] == (process.pid, process.pid):
                identities[int(folder.name)] = record

    @staticmethod
    def stop(process, identities):
        """Signal only a session with a still-matching retained process identity."""
        with process.nanoda_stop_lock:
            ProcessSessions._stop(process, identities)

    @staticmethod
    def _stop(process, identities):
        """Give live descendants time to handle TERM before killing the whole group."""
        if not any(process_record(pid) == record for pid, record in identities.items()):
            process.poll()
            return
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            return
        deadline = time.monotonic() + 5
        while any(process_record(pid, live=True) == record for pid, record in identities.items()):
            if time.monotonic() >= deadline:
                break
            process.poll()
            time.sleep(.02)
        if any(process_record(pid, live=True) == record for pid, record in identities.items()):
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.wait()

    def run(self, command):
        """Capture worker protocol stdout while retaining live diagnostic stderr."""
        with self.lock:
            if self.cancelled:
                raise RuntimeError('nanoda pipeline cancelled')
            process = subprocess.Popen(command, stdout=subprocess.PIPE, text=True, start_new_session=True)
            process.nanoda_stop_lock = threading.Lock()
            identities = {process.pid: process_record(process.pid)}
            if identities[process.pid] is None:
                process.wait()
                raise RuntimeError('cannot bind worker process identity')
            self.running[process] = identities
        try:
            while True:
                with self.lock:
                    self.observe(process, identities)
                try:
                    output, _ = process.communicate(timeout=0.1)
                    break
                except subprocess.TimeoutExpired:
                    continue
            return subprocess.CompletedProcess(command, process.returncode, output)
        except BaseException:
            self.stop(process, identities)
            raise
        finally:
            with self.lock:
                self.observe(process, identities)
            # A successful helper can leave a child that closed its inherited
            # stdout. Reaping that helper alone does not finish its owned work.
            self.stop(process, identities)
            with self.lock:
                self.running.pop(process, None)

    def cancel(self):
        """Prevent new workers and stop every currently owned worker session."""
        with self.lock:
            self.cancelled = True
            running = [(process, dict(identities)) for process, identities in self.running.items()]
        for process, identities in running:
            self.stop(process, identities)
