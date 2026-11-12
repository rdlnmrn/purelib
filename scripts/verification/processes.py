"""Track and stop verification descendants, including independent sessions."""

import ctypes
import os
from pathlib import Path
import signal
import time

from scripts.nanoda.benchmark_pipeline import descendants, process_table
from scripts.nanoda.processes import process_record


class ChildScope:
    """Adopt a serialized stage's orphans in its dedicated calling process.

    The caller must have one kernel thread and no pre-existing children. This
    makes every subsequently adopted child part of this stage, rather than
    claiming unrelated work from an embedding application. Restore the prior
    subreaper setting only after the stage's owning wait and orphan reaping.
    """

    def __init__(self, *, grace=15.0):
        self.grace = grace

    def __enter__(self):
        self.pid = os.getpid()
        self.identity = process_record(self.pid)
        self.namespace = os.readlink("/proc/self/ns/pid")
        if (self.identity is None or
                int(Path("/proc/self/stat").read_text().split("(", 1)[0]) != self.pid):
            raise RuntimeError("stage supervision requires procfs in the caller's PID namespace")
        tasks = list(Path("/proc/self/task").iterdir())
        if len(tasks) != 1 or (tasks[0] / "children").read_text().strip():
            raise RuntimeError("stage supervision requires a dedicated process without other children or threads")
        self.libc = ctypes.CDLL(None, use_errno=True)
        previous = ctypes.c_int()
        if self.libc.prctl(37, ctypes.byref(previous), 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "cannot inspect child subreaper setting")
        self.previous = previous.value
        if self.libc.prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "cannot adopt stage descendants")
        return self

    def check(self):
        """Reject a changed caller identity or procfs namespace before claiming children."""
        if (os.getpid() != self.pid or process_record(self.pid) != self.identity or
                os.readlink("/proc/self/ns/pid") != self.namespace):
            raise RuntimeError("stage supervisor identity or PID namespace changed")

    def reap(self, *, terminate=False, deadline=None):
        """Reap adopted exits, terminating actual children on failed-stage cleanup.

        A supplied deadline shares the original TERM grace with ancestry-based
        cleanup. Kernel child ownership covers descendants omitted by sampling.
        """
        self.check()
        deadline = time.monotonic() + self.grace if deadline is None else deadline
        signalled = set()
        while True:
            expired = time.monotonic() >= deadline
            if terminate:
                self.check()
                # Reaping an intermediate child can expose deeper orphans.
                # Only the dedicated caller's actual kernel children qualify.
                for raw in Path(f"/proc/self/task/{self.pid}/children").read_text().split():
                    child = int(raw)
                    identity = process_record(child)
                    key = (child, identity[0] if identity else None)
                    if not expired and key in signalled:
                        continue
                    try:
                        os.kill(child, signal.SIGKILL if expired else signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    signalled.add(key)
            try:
                pid, _ = os.waitpid(-1, 0 if terminate and expired else os.WNOHANG)
            except ChildProcessError:
                return
            if pid == 0:
                if not terminate:
                    raise RuntimeError("stage supervisor still owns live descendants")
                time.sleep(.02)

    def __exit__(self, exc_type, *_):
        cleaned = False
        try:
            if exc_type is None:
                try:
                    self.reap()
                except BaseException:
                    self.reap(terminate=True)
                    cleaned = True
                    raise
            else:
                self.reap(terminate=True)
            cleaned = True
        finally:
            # Do not relinquish adoption while failed cleanup still owns work.
            if cleaned:
                self.check()
                if self.libc.prctl(36, self.previous, 0, 0, 0) != 0:
                    raise OSError(ctypes.get_errno(), "cannot restore child subreaper setting")


def observe(process, known, table):
    """Follow ancestry while the original leader identity still matches."""
    owner = getattr(process, "verification_owner", None)
    if owner is not None:
        owner.check()
        # The kernel reparents an exiting leader's detached children here even
        # if no earlier sample saw them. Keep the supervisor out of the set of
        # processes that stop_tree may signal.
        roots = dict(known)
        roots[owner.pid] = owner.identity[0]
        owned = descendants(table, owner.pid, roots) - {owner.pid}
        known.update({pid: roots[pid] for pid in owned})
        return owned
    leader = table.get(process.pid)
    parent = process.pid if leader and leader["started"] == known.get(process.pid) else -1
    return descendants(table, parent, known)


def live_owned(known):
    """Resolve only still-live processes with the retained creation identities."""
    return [pid for pid, started in known.items()
            if (record := process_record(pid, live=True)) is not None and record[0] == started]


def stop_tree(process, known, grace=5.0):
    """Stop retained descendants and return the leader's raw exit code."""
    def live():
        observe(process, known, process_table())
        return live_owned(known)

    for pid in live():
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + grace
    while live() and time.monotonic() < deadline:
        process.poll()
        time.sleep(.02)
    for pid in live():
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    return process.wait()
