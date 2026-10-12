#!/usr/bin/env python3
"""Run ordinary Lake builtin lint in separate, resumable native module processes.

Lake still builds the complete selection once. Its unchanged builtin checker is
then invoked once per process, so imported environments cannot accumulate across
modules. Unsupported CLI forms are delegated verbatim to Lake.
"""

from __future__ import annotations

import concurrent.futures
import fcntl
import itertools
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import tomllib

from scripts.lean_module_data.compact import inventory
from scripts.lean_module_data.paths import parse_name

from scripts.paths import ROOT
SUPPORT = "Lake.CLI.BuiltinLint"
PROTOCOL = "lake-builtin-lint-native-one-module-v2"
PLAIN_GLOBALS = {"--wfail", "--no-build", "--quiet", "-q", "--verbose", "-v", "--no-ansi", "--ansi",
                 "--rehash", "--old", "--offline", "--keep-going"}
HELPER = """module
-- Compile the original checker; import all permits reduction of its retained private helpers.
import all Lake.CLI.BuiltinLint

/-- Run the unchanged builtin checker on exactly one already built module. -/
public unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  if args.length != 1 then
    IO.eprintln "builtin lint worker requires exactly one module"
    return 1
  Lake.BuiltinLint.run { mods := args.toArray.map String.toName }
"""


from scripts.nanoda import input_key as INPUTS


def sha(path: Path) -> str:
    return INPUTS.digest(path)


def identity(value) -> str:
    return INPUTS.identity(value)


def atomic(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def plain_request(args: list[str], config: dict, cwd: Path = ROOT):
    """Recognize only the ordinary builtin command whose exact semantics we retain."""
    if cwd != ROOT and ROOT not in cwd.parents:
        return None
    if config.get("builtinLint") is not True or config.get("lintDriver"):
        return None
    index = 0
    while index < len(args) and args[index] in PLAIN_GLOBALS:
        index += 1
    if index == len(args) or args[index] != "lint":
        return None
    modules = args[index + 1:]
    if not modules or len(modules) != len(set(modules)):
        return None
    if any(not parse_name(module) or module.startswith("-") or "/" in module for module in modules):
        return None
    return args[:index], modules


def signature(path: Path):
    stat = path.stat()
    return stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns


def checked_fingerprints(paths):
    """Keep each digest paired with the signatures checked around that read."""
    hashes, signatures = {}, {}
    for path in paths:
        path = Path(path)
        before = signature(path)
        value = sha(path)
        after = signature(path)
        if before != after:
            raise ValueError(f"lint input changed during fingerprinting: {path}")
        hashes[str(path)] = value
        signatures[path] = before
    return hashes, signatures


def worker_count(environ=None, cpus=None, available=None):
    """Use available CPUs and measured worker memory; explicit counts have no cap."""
    environ = os.environ if environ is None else environ
    requested = environ.get("CCL_LINT_JOBS", "auto")
    if requested != "auto":
        if not requested.isdecimal() or int(requested) < 1:
            raise ValueError("CCL_LINT_JOBS must be auto or a positive integer")
        return int(requested)
    if cpus is None:
        cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count() or 1
    if available is None:
        try:
            memory = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
            available = int(memory["MemAvailable"].split()[0]) * 1024
        except (OSError, KeyError, ValueError):
            # No memory measurement: keep the documented conservative pool.
            return min(cpus, 8)
    # The previous full pass peaked at 1.87 GiB/worker; native workers use less.
    return max(1, min(cpus, available // (2 * 1024**3)))


def completed_tasks(pool, check, tasks, jobs, idle=None):
    """Keep only one future per worker and deliver finished jobs without head-of-line waits."""
    tasks = iter(tasks)
    pending = {pool.submit(check, task): task for task in itertools.islice(tasks, jobs)}
    while pending:
        done, _ = concurrent.futures.wait(pending, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED)
        if not done and idle is not None:
            idle()
        for future in done:
            task = pending.pop(future)
            result = future.result()
            if (next_task := next(tasks, None)) is not None:
                pending[pool.submit(check, next_task)] = next_task
            yield task, result


def bind_inputs(modules: list[str], search: list[Path], cache: Path):
    """Reload a checked inventory, hashing every actual consumed artifact part."""
    roots = list(dict.fromkeys([*modules, SUPPORT]))
    namespace = identity({"roots": roots, "search": list(map(str, search)),
                          "reader": {str(p): sha(p) for p in
                                     sorted((ROOT / "scripts/lean_module_data").glob("*.py"))}})
    directory = cache / "inputs" / namespace
    pointer = directory / "current.json"
    saved = json.loads(pointer.read_text()) if pointer.exists() else None
    if saved:
        data = saved["inventory"]
        if identity(data) != saved["inventory_sha256"]:
            raise ValueError("corrupt lint import inventory checkpoint")
        try:
            paths = INPUTS.validate_inventory(data, roots, search)
            hashes, signatures = checked_fingerprints(paths)
            reusable = hashes == saved["files"]
        except (OSError, ValueError):
            reusable = False
    else:
        reusable = False
    if not reusable:
        data, _ = inventory(roots, search)
        paths = INPUTS.validate_inventory(data, roots, search)
        hashes, signatures = checked_fingerprints(paths)
    # Modern modules must retain private/server parts and executable IR.
    for node in data["modules"]:
        if len(node["files"]) == 3:
            ir = Path(node["files"][0]).with_suffix(".ir")
            if not ir.is_file() or str(ir.resolve()) not in hashes:
                raise ValueError(f"missing lint interpreter input: {ir}")
    atomic(pointer, {"inventory": data, "inventory_sha256": identity(data), "files": hashes})
    graph = {node["name"]: node for node in data["modules"]}
    return INPUTS.module_keys(data, hashes), signatures, graph


def native_compiler(sysroot, env):
    """Resolve the compiler selected by the pinned leanc wrapper, including LEAN_CC."""
    if "LEAN_CC" not in env:
        return (sysroot / "bin/clang").resolve()
    compiler = shutil.which(env["LEAN_CC"], path=env.get("PATH"))
    if compiler is None:
        raise ValueError("LEAN_CC does not resolve to an executable compiler")
    return Path(compiler).resolve()


def tool_identity(lake: str, lean: str, env: dict, search: list[Path], helper: Path, config: dict):
    """Bind the runner, compiler, native libraries, helper and configured options."""
    tools = {Path(lake).resolve(), Path(lean).resolve(), Path(__file__).resolve(),
             ROOT / "scripts/run-lake.sh", ROOT / "scripts/linting/lake_args.py",
             ROOT / "scripts/linting/providers.py", ROOT / "scripts/nanoda/input_key.py",
             ROOT / "lakefile.toml", ROOT / "lake-manifest.json", helper}
    for directory in search:
        tools.update(path.resolve() for path in directory.glob("*.so"))
    sysroot = Path(env.get("LEAN_SYSROOT") or Path(lean).resolve().parent.parent)
    tools.update(path.resolve() for path in (sysroot / "lib/lean").glob("*shared*.so"))
    tools.update(path.resolve() for path in (sysroot / "lib/lean").glob("*.a"))
    tools.update((sysroot / "bin" / name).resolve() for name in ("leanc", "clang"))
    tools.add(native_compiler(sysroot, env))
    # Native providers live both beside .oleans and in their package's lib directory.
    for directory in search:
        if directory.name == "lean":
            tools.update(path.resolve() for path in directory.parent.glob("*.so"))
    hashes, signatures = checked_fingerprints(sorted(tools))
    return {"protocol": PROTOCOL, "files": hashes, "leanOptions": config.get("leanOptions", []),
            "environment": {key: env.get(key, "") for key in
                            ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_GITHASH", "LD_LIBRARY_PATH",
                             "LEAN_CC", "MACOSX_DEPLOYMENT_TARGET")}}, \
        signatures


def build_native_worker(lean, env, helper, cache, support_key, tool, inputs):
    """Retain a fully initialized, interpreter-capable launcher bound to its compiler inputs."""
    sysroot = Path(env.get("LEAN_SYSROOT") or Path(lean).resolve().parent.parent)
    libraries = [sysroot / "lib/lean" / name for name in
                 ("libLake.a", "libLean.a", "libInit.a", "libStd.a", "libleancpp.a", "libleanrt.a")]
    native_paths = [Path(lean), sysroot / "bin/leanc", native_compiler(sysroot, env), *libraries]
    bindings = {"protocol": PROTOCOL, "helper": sha(helper), "support": support_key,
                "builder": tool["files"][str(Path(__file__).resolve())],
                "compiler": {str(p.resolve()): tool["files"][str(p.resolve())] for p in native_paths},
                "environment": {key: env.get(key) for key in ("LEAN_CC", "MACOSX_DEPLOYMENT_TARGET")},
                "link": ["-O3", "-Wl,--export-dynamic", "-Wl,--whole-archive",
                         *map(str, libraries), "-Wl,--no-whole-archive"]}
    directory = cache / "native" / identity(bindings)
    binary, receipt = directory / "worker", directory / "build.json"
    if receipt.exists():
        if json.loads(receipt.read_text()) != {"bindings": bindings, "binary_sha256": sha(binary)}:
            raise ValueError("corrupt native lint worker checkpoint")
        return binary
    directory.mkdir(parents=True, exist_ok=True)
    print("Builtin lint: compiling native worker (once per compiler/helper revision).", file=sys.stderr)
    with tempfile.TemporaryDirectory(prefix="pending-", dir=directory) as temporary:
        temporary = Path(temporary)
        c_source = temporary / "worker.c"
        subprocess.run([lean, "-R", str(helper.parent), "-DwarningAsError=true",
                        "-o", str(temporary / "RunBuiltinLint.olean"), "-c", str(c_source), str(helper)],
                       env=env, cwd=ROOT, check=True)
        # The runtime-only generated main omits meta registrations needed by imported extensions.
        source = c_source.read_text()
        old = "res = runtime_initialize_RunBuiltinLint(1 /* builtin */);"
        if source.count(old) != 1:
            raise ValueError("pinned native lint entrypoint initialization changed")
        c_source.write_text(source.replace(old, "res = initialize_RunBuiltinLint(1 /* builtin */);"))
        subprocess.run([str(sysroot / "bin/leanc"), "-o", str(temporary / "worker"),
                        str(c_source), *bindings["link"]], env=env, cwd=ROOT, check=True)
        if any(signature(path) != before for path, before in inputs.items()):
            raise ValueError("lint inputs changed during native worker build")
        os.replace(temporary / "worker", binary)
        atomic(receipt, {"bindings": bindings, "binary_sha256": sha(binary)})
    return binary


def terminate_group(process: subprocess.Popen) -> None:
    """Stop this owned group even after its leader exits; escalate survivors."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 1
    while time.monotonic() < deadline:
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.01)
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


class Workers:
    """Own and stop only this invocation's checker process groups."""
    def __init__(self, command: list[str], env: dict, cache: Path,
                 inputs: dict[Path, tuple], graph: dict, tools: set[Path], contexts: dict | None = None):
        self.command, self.env, self.cache = command, env, cache
        self.inputs, self.graph, self.tools = inputs, graph, tools
        self.contexts = contexts or {}
        self.node_inputs = {}
        for name, node in graph.items():
            paths = {Path(p).resolve() for p in node["files"]}
            if len(node["files"]) == 3:
                paths.add(Path(node["files"][0]).with_suffix(".ir").resolve())
            source = ROOT / (name.replace(".", "/") + ".lean")
            if source in inputs:
                paths.add(source)
            if not paths <= inputs.keys():
                raise ValueError(f"unbound lint input paths: {name}")
            self.node_inputs[name] = frozenset(paths)
        self.lock = threading.Lock()
        self.processes = set()
        self.cancelled = False

    def stop(self):
        with self.lock:
            self.cancelled = True
            processes = list(self.processes)
        for process in processes:
            terminate_group(process)

    def validate_completed_inputs(self, modules):
        """Check the union of completed closures once before publishing their passes."""
        paths, reached, pending = set(self.tools), set(), [*modules, SUPPORT]
        while pending:
            name = pending.pop()
            if name in reached:
                continue
            reached.add(name)
            paths.update(self.node_inputs[name])
            pending.extend(self.graph[name]["imports"])
        if any(signature(path) != self.inputs[path] for path in paths):
            raise ValueError(f"lint inputs changed during checking: {', '.join(modules)}")

    def publish(self, tasks):
        """Atomically checkpoint successful completed workers after one shared input check."""
        if not tasks:
            return
        self.validate_completed_inputs([module for module, _ in tasks])
        for module, key in tasks:
            directory = self.cache / "results" / key
            atomic(directory / "pass.json", {"protocol": PROTOCOL, "module": module, "key": key,
                   "inputs": self.contexts.get(module), "exit": 0,
                   "output_sha256": sha(directory / "output.log")})

    def check(self, task):
        module, key = task
        directory = self.cache / "results" / key
        receipt, output = directory / "pass.json", directory / "output.log"
        if receipt.exists():
            record = json.loads(receipt.read_text())
            if record != {"protocol": PROTOCOL, "module": module, "key": key,
                          "inputs": self.contexts.get(module), "exit": 0, "output_sha256": sha(output)}:
                raise ValueError(f"corrupt lint result checkpoint: {module}")
            return 0, output.read_bytes(), True
        directory.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=directory, delete=False) as log:
            temporary = Path(log.name)
            with self.lock:
                if self.cancelled:
                    temporary.unlink()
                    raise InterruptedError("lint run interrupted")
                process = subprocess.Popen([*self.command, module],
                                           cwd=ROOT, env=self.env, stdout=log,
                                           stderr=subprocess.STDOUT, start_new_session=True)
                self.processes.add(process)
            try:
                code = process.wait()
            finally:
                terminate_group(process)
                with self.lock:
                    self.processes.discard(process)
            log.flush()
            os.fsync(log.fileno())
        os.replace(temporary, output)
        return code, output.read_bytes(), False


def lint(lake: str, options: list[str], modules: list[str], config: dict) -> int:
    jobs = min(worker_count(), len(modules))
    start = time.monotonic()
    print(f"Builtin lint: {len(modules)} modules, {jobs} workers; checking build inputs.", file=sys.stderr)
    # One official build/currentness check, retaining --no-build when requested.
    built = subprocess.run([lake, *options, "build", *("+" + module for module in modules)], cwd=ROOT)
    if built.returncode:
        return built.returncode
    raw = subprocess.check_output([lake, *options, "env", sys.executable, "-c",
                                   "import json,os; print(json.dumps(dict(os.environ)))"], cwd=ROOT)
    env = json.loads(raw)
    lean = shutil.which("lean", path=env["PATH"])
    if lean is None:
        raise ValueError("Lake environment has no Lean executable")
    sysroot = subprocess.check_output([lean, "--print-prefix"], env=env, text=True).strip()
    search = [Path(p).resolve() for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    search.append(Path(sysroot) / "lib/lean")
    cache = ROOT / ".lake/builtin-lint"
    cache.mkdir(parents=True, exist_ok=True)
    # Serialize checkpoint writers, including interrupted-run recovery.
    with (cache / "lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        helper = cache / "RunBuiltinLint.lean"
        if not helper.exists() or helper.read_text() != HELPER:
            helper.write_text(HELPER)
        module_keys, inputs, graph = bind_inputs(modules, search, cache)
        tool, tools = tool_identity(lake, lean, env, search, helper, config)
        inputs.update(tools)
        binary = build_native_worker(lean, env, helper, cache, module_keys[SUPPORT], tool, inputs)
        binary = binary.resolve()
        binary_hashes, binary_inputs = checked_fingerprints([binary])
        if binary_hashes[str(binary)] != json.loads(binary.with_name("build.json").read_text())["binary_sha256"]:
            raise ValueError("native lint worker changed after build verification")
        tool["worker"] = {"path": str(binary), "sha256": binary_hashes[str(binary)]}
        inputs.update(binary_inputs)
        tools.update(binary_inputs)
        for name in graph:
            source = ROOT / (name.replace(".", "/") + ".lean")
            if source.is_file():
                inputs[source] = signature(source)
        tool_key = identity(tool)
        atomic(cache / "tools" / (tool_key + ".json"), tool)
        contexts = {module: {"module": module, "closure": module_keys[module], "support": module_keys[SUPPORT],
                             "tool": tool_key, "options": options,
                             "source": sha(ROOT / (module.replace(".", "/") + ".lean"))
                             if (ROOT / (module.replace(".", "/") + ".lean")).is_file() else None}
                    for module in modules}
        tasks = [(module, identity(contexts[module])) for module in modules]
        workers = Workers([str(binary)], env, cache, inputs, graph, set(tools), contexts)
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=jobs)
        failed, reused = False, 0
        ready = []
        checkpointed = time.monotonic()
        setup_seconds = checkpointed - start
        print(f"Builtin lint: inputs bound in {setup_seconds:.2f}s; starting checks.", file=sys.stderr)

        def checkpoint(force=False):
            """Retain a completed batch even while remaining workers are slow."""
            nonlocal checkpointed
            if ready and (force or len(ready) >= jobs or time.monotonic() - checkpointed >= 1):
                workers.publish(ready)
                ready.clear()
                checkpointed = time.monotonic()

        try:
            for task, (code, output, cached) in completed_tasks(pool, workers.check, tasks, jobs, checkpoint):
                sys.stdout.buffer.write(output)
                sys.stdout.buffer.flush()
                failed |= code != 0
                reused += cached
                if code == 0 and not cached:
                    ready.append(task)
                checkpoint()
            checkpoint(force=True)
        finally:
            workers.stop()
            pool.shutdown(wait=True, cancel_futures=True)
        if any(signature(path) != before for path, before in inputs.items()):
            raise ValueError("lint input changed during execution; rerun after writers stop")
        print(f"Builtin lint: {len(modules)} modules, {reused} checked checkpoints reused; "
              f"setup {setup_seconds:.2f}s, checks {time.monotonic() - start - setup_seconds:.2f}s.")
        return 1 if failed else 0


def main() -> int:
    lake, *args = sys.argv[1:]
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    request = plain_request(args, config, Path.cwd().resolve())
    if request is None:
        os.execvp(lake, [lake, *args])
    try:
        signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
        return lint(lake, *request, config)
    except KeyboardInterrupt:
        return 130
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"builtin lint runner failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
