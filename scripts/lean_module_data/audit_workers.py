"""Small decoding workers and shared immutable axiom-graph queries.

The parent retains the original import environment and validates the immutable
view. Private pipes carry trusted host-worker messages; workers execute no
target initializer, callback or supplied proof producer.
"""
from collections import OrderedDict, deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import contextmanager
from copy import copy
import os
from pathlib import Path
import pickle
import signal
import subprocess
import sys
import time
from scripts.verification.processes import ChildScope, observe, process_record, process_table, stop_tree
BATCH_SIZE = 32
QUERY_BATCH_SIZE = 512
PROGRESS_INTERVAL = 30.0
TERMINATION_GRACE = 15.0
PRIVATE_WORKER_BYTES = 512 * 1024 ** 2
_modules = OrderedDict()
_graph = None
_graph_binding = None

def worker_count(cores, private_bytes=PRIVATE_WORKER_BYTES):
    """Reserve private decoding memory in addition to the retained environment."""
    from scripts.verification.completion import available_memory
    memory = available_memory()
    environments = int(os.environ.get('AXIOM_AUDIT_JOBS', '1'))
    budget = os.environ.get('CCL_CHECK_MEMORY_BYTES')
    if environments > 1 and budget is not None:
        resident = int(Path('/proc/self/statm').read_text().split()[1]) * os.sysconf('SC_PAGE_SIZE')
        remaining = max(0, int(budget) // environments - resident)
        memory = remaining if memory is None else min(memory, remaining)
    return min(cores, max(1, memory // private_bytes)) if memory is not None else 1

def worker_command():
    """Start the decoder code without inheriting the parent's Python heap."""
    return [sys.executable, '-m', 'scripts.lean_module_data.audit_workers', '--worker']

def decode_batch(request):
    """Reconstruct original bound references and observe their ordered edges."""
    from .compact import InvalidArtifact, file_identity
    from .importer import Module, Ref
    from .observations import Observations, name_observer
    from .typed import TypedDecoder
    module_name, files, declarations = request
    key = (module_name, files)
    if key not in _modules:
        module = Module(module_name, Path(files[0][0]), {}, {}, data=len(files) > 1)
        actual = tuple(((str(r.path), r.sha256, r.data.identity) for r in module.roots))
        if actual != files:
            raise InvalidArtifact('decoder input parts changed')
        _modules[key] = module
        while len(_modules) > 2:
            _modules.popitem(last=False)
    _modules.move_to_end(key)
    module = _modules[key]
    observer = Observations.__new__(Observations)
    rows = []
    for pointer, expected in declarations:
        original = Ref(module, pointer)
        if name_observer(original.d, original.name) != expected:
            raise InvalidArtifact('decoder received a different declaration')
        view = copy(original)
        view.d = TypedDecoder([])
        view.d.parts = original.d.parts
        view.name = view.d.decode('Name', original.base[0])
        rows.append(observer.axiom_dependencies(view))
    if any((file_identity(r.path.stat()) != r.data.identity for r in module.roots)):
        raise InvalidArtifact('decoder input changed during checking')
    return rows

def query_batch(binding, roots):
    """Run the original traversal against shared read-only graph buffers."""
    global _graph, _graph_binding
    from .audit_graph import Graph
    if binding != _graph_binding:
        if _graph is not None:
            _graph.close()
        _graph = Graph(binding)
        _graph_binding = binding
        _modules.clear()
    result = [_graph.axioms(root) for root in roots]
    _graph.verify()
    return result

def worker_main():
    """Answer exclusive private-pipe requests without emitting a proof verdict."""
    try:
        while True:
            try:
                mode, request = pickle.load(sys.stdin.buffer)
            except EOFError:
                return
            if mode == 'decode':
                result = decode_batch(request)
            elif mode == 'query':
                result = query_batch(*request)
            else:
                raise ValueError('unknown audit worker request')
            pickle.dump(result, sys.stdout.buffer, protocol=5)
            sys.stdout.buffer.flush()
    finally:
        if _graph is not None:
            _graph.close()

def exchange(process, request):
    """Exchange one ordered batch on an exclusively owned worker pipe."""
    try:
        pickle.dump(request, process.stdin, protocol=5)
        process.stdin.flush()
        return pickle.load(process.stdout)
    except (EOFError, BrokenPipeError) as error:
        raise RuntimeError('audit worker exited without a complete reply; raw exit=' + str(process.poll())) from error

def prefetch(observation, queries, processes, pool):
    """Decode each reachable uncached declaration once in its original owner."""
    queued = OrderedDict()
    seen = set()

    def enqueue(name):
        if observation.persisted_axioms(name) is not None:
            return
        ref = observation.by_name.get(name)
        if ref is not None and ref not in seen and ((ref, 'axioms') not in observation.dependency_projections):
            queued.setdefault(ref.module, deque()).append(ref)
            seen.add(ref)
    for name in queries:
        enqueue(name)
    pending = {}

    def submit(process):
        if not queued:
            return
        module, refs = queued.popitem(last=False)
        batch = [refs.popleft() for _ in range(min(BATCH_SIZE, len(refs)))]
        if refs:
            queued[module] = refs
        files = tuple(((str(r.path), r.sha256, r.data.identity) for r in module.roots))
        request = (module.name, files, [(ref.ptr, observation.names[ref.key]) for ref in batch])
        pending[pool.submit(exchange, process, ('decode', request))] = (process, batch)
    for process in processes:
        submit(process)
    completed = 0
    next_progress = time.monotonic() + PROGRESS_INTERVAL
    while pending:
        done, _ = wait(pending, timeout=1, return_when=FIRST_COMPLETED)
        for future in done:
            process, batch = pending.pop(future)
            rows = future.result()
            if not isinstance(rows, list) or len(rows) != len(batch):
                raise ValueError('decoder omitted or duplicated declaration results')
            for ref, names in zip(batch, rows, strict=True):
                if not isinstance(names, list):
                    raise ValueError('decoder returned invalid dependencies')
                canonical = []
                for name in names:
                    selected = observation.by_name.get(name)
                    canonical.append(observation.names[selected.key] if selected is not None else name)
                    enqueue(name)
                observation.dependency_projections[ref, 'axioms'] = tuple(canonical)
                completed += 1
            submit(process)
        if time.monotonic() >= next_progress:
            print(f'axiom decoding: {completed} checked; {len(seen)} discovered', file=sys.stderr, flush=True)
            next_progress = time.monotonic() + PROGRESS_INTERVAL
    if queued or completed != len(seen):
        raise ValueError('decoder coverage is incomplete')

def query_all(binding, names, roots, processes, pool):
    """Retain exact root order and coverage when sharing the immutable graph."""
    pending = {}
    result = [None] * len(roots)
    batches = iter(range(0, len(roots), QUERY_BATCH_SIZE))

    def submit(process):
        start = next(batches, None)
        if start is None:
            return
        stop = min(len(roots), start + QUERY_BATCH_SIZE)
        pending[pool.submit(exchange, process, ('query', (binding, roots[start:stop])))] = (process, start, stop)
    for process in processes:
        submit(process)
    checked = 0
    next_progress = time.monotonic() + PROGRESS_INTERVAL
    while pending:
        done, _ = wait(pending, timeout=1, return_when=FIRST_COMPLETED)
        for future in done:
            process, start, stop = pending.pop(future)
            rows = future.result()
            if not isinstance(rows, list) or len(rows) != stop - start:
                raise ValueError('audit worker omitted or duplicated query results')
            for offset, row in enumerate(rows, start):
                if not isinstance(row, list) or any((type(i) is not int or not 0 <= i < len(names) for i in row)):
                    raise ValueError('audit worker returned an invalid closure')
                if result[offset] is not None:
                    raise ValueError('audit worker repeated a query')
                result[offset] = [names[i] for i in row]
            checked += stop - start
            submit(process)
        if time.monotonic() >= next_progress:
            print(f'axiom queries: {checked}/{len(roots)} checked', file=sys.stderr, flush=True)
            next_progress = time.monotonic() + PROGRESS_INTERVAL
    if checked != len(roots) or any((row is None for row in result)):
        raise ValueError('audit query coverage is incomplete')
    return result

@contextmanager
def workers(count, binding=None):
    """Own one bounded worker phase, including its exits, pipes and descendants."""
    children = []
    with ChildScope(grace=TERMINATION_GRACE) as owner:
        pool = ThreadPoolExecutor(max_workers=count)
        try:
            for _ in range(count):
                process = subprocess.Popen(worker_command(), stdin=subprocess.PIPE, stdout=subprocess.PIPE, start_new_session=True, pass_fds=(binding[0],) if binding else ())
                process.verification_owner = owner
                record = process_record(process.pid)
                known = {process.pid: record[0]} if record else {}
                children.append((process, known))
                if not record:
                    raise RuntimeError('cannot identify audit worker')
            processes = [process for process, _ in children]
            yield (processes, pool)
            for process in processes:
                process.stdin.close()
            for process in processes:
                if process.wait(timeout=TERMINATION_GRACE) != 0 or process.stdout.read(1):
                    raise RuntimeError('audit worker did not finish cleanly')
        finally:
            for process, known in children:
                observe(process, known, process_table())
                stop_tree(process, known, TERMINATION_GRACE)
            pool.shutdown(wait=True, cancel_futures=True)
            for process, _ in children:
                if not process.stdin.closed:
                    process.stdin.close()
                process.stdout.close()

def closures(observation, queries, cores=1):
    """Parallelize finite decoding and closure queries without copying the environment."""
    if cores < 1:
        raise ValueError('axiom query cores must be positive')
    if hasattr(os, 'sched_getaffinity'):
        cores = min(cores, len(os.sched_getaffinity(0)))
    count = min(worker_count(cores), len(queries)) if queries and cores > 1 else 1
    if count < 2:
        return [observation.axioms(name) for name in queries]
    from .audit_graph import build
    previous = signal.getsignal(signal.SIGTERM)

    def interrupt(*_):
        raise KeyboardInterrupt('audit worker pool interrupted')
    signal.signal(signal.SIGTERM, interrupt)
    try:
        with workers(count) as (processes, pool):
            print(f'axiom decoding: {count} workers within a {cores}-core budget', file=sys.stderr, flush=True)
            prefetch(observation, queries, processes, pool)
        print('axiom graph: building and checking immutable shared view', file=sys.stderr, flush=True)
        binding, names, roots = build(observation, queries)
        try:
            count = min(worker_count(cores, 128 * 1024 ** 2), len(roots))
            with workers(count, binding) as (processes, pool):
                print(f'axiom queries: {count} workers reading sealed shared buffers', file=sys.stderr, flush=True)
                return query_all(binding, names, roots, processes, pool)
        finally:
            os.close(binding[0])
    finally:
        signal.signal(signal.SIGTERM, previous)
if __name__ == '__main__':
    if sys.argv[1:] != ['--worker']:
        raise SystemExit('use --worker for the private audit protocol')
    worker_main()
