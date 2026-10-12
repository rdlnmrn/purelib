"""Quiet timings and checked, isolated compilation diagnostics for project builds."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import threading
import time

BUILT = re.compile(r"^.*\] Built ([\w.]+) \((\d+(?:\.\d+)?)(ms|s)\)$")
FRAME = re.compile(r"^( *)\[([^]]+)\] \[(\d+(?:\.\d+)?)\] (.*)$")


def stop_owned(process: subprocess.Popen) -> None:
    """Stop only the still-live process group created for this owned command."""
    if process.poll() is not None:
        return
    if os.getpgid(process.pid) != process.pid:
        raise ValueError("owned compiler process-group identity changed")
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        if os.getpgid(process.pid) != process.pid:
            raise ValueError("owned compiler process-group identity changed")
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".partial")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def timings(log: str, modules: list[str]) -> dict[str, float]:
    """Select fresh project compilations; reject ambiguous repeated observations."""
    if not modules or len(modules) != len(set(modules)):
        raise ValueError("empty or duplicate project inventory")
    selected = set(modules)
    result = {}
    for line in log.splitlines():
        match = BUILT.match(line)
        if match and match[1] in selected:
            name = match[1]
            if name in result:
                raise ValueError(f"duplicate module timing: {name}")
            result[name] = float(match[2]) / (1000 if match[3] == "ms" else 1)
    return result


class Digests:
    """Share checked artifact hashes across the bounded diagnostic worker pool."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.cache = {}

    @staticmethod
    def signature(path: Path) -> tuple:
        st = path.stat()
        return st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns

    def sha(self, path: Path) -> str:
        with self.lock:
            before = self.signature(path)
            cached = self.cache.get(str(path))
            if cached and cached[0] == before:
                return cached[1]
            with path.open("rb") as stream:
                value = hashlib.file_digest(stream, "sha256").hexdigest()
            if before != self.signature(path):
                raise ValueError(f"input changed while hashing: {path}")
            self.cache[str(path)] = before, value
            return value


def compiler_command(trace: Path) -> tuple[list[str], dict[str, str]]:
    """Retain Lake's exact compiler, setup, native providers and option context."""
    rows = json.loads(trace.read_text())["log"]
    candidates = [row["message"] for row in rows
                  if row["message"].startswith(".> ") and " --setup " in row["message"]
                  and " -o " in row["message"]]
    if len(candidates) != 1:
        raise ValueError(f"expected exactly one compiler command: {trace}")
    command = shlex.split(candidates[0][3:])
    env = {}
    while command and "=" in command[0]:
        name, value = command.pop(0).split("=", 1)
        env[name] = value
    if not command:
        raise ValueError(f"missing compiler command: {trace}")
    return command, env


def import_header(source: Path) -> str:
    """Preserve the actual ordered imports, phase modifiers and module preamble."""
    content = source.read_text()
    matches = list(re.finditer(
        r"^(?:(?:public|private|meta)\s+)*import\s+[^\n]+(?:\n|$)", content, re.M))
    if not matches:
        raise ValueError(f"no explicit import header: {source}")
    return content[:matches[-1].end()]


class Probes:
    """Replay complete compilations without modifying any Lake-owned artifacts."""

    def __init__(self, root: Path, cache: Path, threads: int) -> None:
        self.root = root
        self.cache = cache
        self.threads = threads
        self.digests = Digests()
        self.stopping = threading.Event()
        self.process_lock = threading.Lock()
        self.processes = set()

    def stop(self) -> None:
        self.stopping.set()
        with self.process_lock:
            for process in self.processes:
                stop_owned(process)

    def run(self, module: str, mode: str) -> dict:
        relative = module.replace(".", "/")
        trace = self.root / ".lake/build/lib/lean" / (relative + ".trace")
        command, overrides = compiler_command(trace)
        # Lake's --wfail acts on JSON messages after Lean exits. Standalone
        # diagnostic compilers must enforce the same rule themselves.
        command.append("-DwarningAsError=true")
        source = self.root / (relative + ".lean")
        setup = Path(command[command.index("--setup") + 1])
        data = json.loads(setup.read_text())
        files = {source, setup, trace, Path(command[0])}
        for arts in data["importArts"].values():
            for filename in arts:
                artifact = Path(filename)
                files.add(artifact)
                if artifact.suffix == ".olean":
                    for suffix in (".olean.private", ".olean.server", ".ir"):
                        sibling = artifact.with_suffix(suffix)
                        if sibling.is_file():
                            files.add(sibling)
        files.update(Path(p["path"]) for p in data.get("plugins", []))
        files.update(Path(p) for p in data.get("dynlibs", []))
        prefix = Path(command[0]).parent.parent
        files.update((prefix / "lib/lean").glob("*shared*.so"))
        inputs = {"module": module, "mode": mode, "command": list(command),
                  "environment": {**overrides, "LEAN_NUM_THREADS": str(self.threads)},
                  "producer_sha256": self.digests.sha(Path(__file__)),
                  "files": {str(p): self.digests.sha(p) for p in sorted(files)}}
        key = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
        output = self.cache / module / mode / key
        receipt = output / "result.json"
        if receipt.exists():
            result = json.loads(receipt.read_text())
            if result["inputs"] != inputs or result["exit_code"] != 0:
                raise ValueError(f"invalid diagnostic checkpoint: {receipt}")
            for filename, expected in result["outputs"].items():
                if self.digests.sha(output / filename) != expected:
                    raise ValueError(f"corrupt diagnostic checkpoint: {output / filename}")
            return {**result, "reused": True, "receipt": str(receipt)}
        output.mkdir(parents=True, exist_ok=True)
        if mode == "header":
            header = output / "Header.lean"
            header.write_text(import_header(source))
            command[command.index(str(source))] = str(header)
        for option, suffix in (("-o", ".olean"), ("-i", ".ilean"), ("-c", ".c")):
            if option in command:
                index = command.index(option)
                if mode == "check":
                    del command[index:index + 2]
                else:
                    command[index + 1] = str(output / ("Module" + suffix))
        if mode == "profile":
            if "--json" in command:
                command.remove("--json")
            command += ["-Dtrace.profiler=true", "-Dtrace.profiler.threshold=100"]
        atomic(output / "inputs.json", inputs)
        atomic(output / "command.json", command)
        started = time.monotonic()
        with (output / "output.log").open("w") as log:
            with self.process_lock:
                if self.stopping.is_set():
                    raise KeyboardInterrupt("profiling interrupted; checkpoints retained")
                process = subprocess.Popen(command, cwd=self.root,
                                           env={**os.environ, **inputs["environment"]},
                                           stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                self.processes.add(process)
            try:
                code = process.wait()
            finally:
                with self.process_lock:
                    self.processes.discard(process)
        elapsed = time.monotonic() - started
        for filename, expected in inputs["files"].items():
            if self.digests.sha(Path(filename)) != expected:
                raise ValueError(f"diagnostic input changed: {filename}")
        if code == 0 and mode != "check":
            for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ilean", ".c"):
                if not (output / ("Module" + suffix)).is_file():
                    raise ValueError(f"missing emitted artifact: {output / ('Module' + suffix)}")
        frames = []
        if mode == "profile":
            for line in (output / "output.log").read_text().splitlines():
                match = FRAME.match(line)
                if match:
                    frames.append({"indent": len(match[1]), "kind": match[2],
                                   "seconds": float(match[3]), "label": match[4]})
        result = {"inputs": inputs, "exit_code": code, "wall_seconds": elapsed,
                  "frames": sorted(frames, key=lambda f: -f["seconds"])[:100],
                  "outputs": {p.name: self.digests.sha(p) for p in output.iterdir()
                              if p.is_file() and p != receipt}}
        # Failed profiler attempts can exhaust ordinary heartbeats through trace
        # overhead. Preserve them diagnostically, but never reuse them as successes.
        atomic(receipt if code == 0 else output / "failure.json", result)
        return {**result, "reused": False,
                "receipt": str(receipt if code == 0 else output / "failure.json")}

    def module(self, module: str) -> dict:
        results = {mode: self.run(module, mode) for mode in ("full", "header", "check", "profile")}
        valid = all(results[mode]["exit_code"] == 0 for mode in ("full", "header", "check"))
        full = results["full"]["wall_seconds"]
        header = results["header"]["wall_seconds"]
        check = results["check"]["wall_seconds"]
        return {"module": module, "valid_quiet_runs": valid, "runs": results,
                "estimated_import_setup_seconds": header if valid else None,
                "estimated_declaration_seconds": max(0, check - header) if valid else None,
                "estimated_emission_seconds": max(0, full - check) if valid else None,
                "note": "Differences between separate runs are estimates. Profiler frames overlap."}

    def selected(self, modules: list[str], jobs: int) -> list[dict]:
        pool = ThreadPoolExecutor(max_workers=jobs)
        try:
            return list(pool.map(self.module, modules))
        except BaseException:
            self.stop()
            raise
        finally:
            pool.shutdown(wait=True, cancel_futures=True)
