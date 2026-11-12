"""Restart individual original cubic arithmetic and root-comparison requests.

Receipts bind observed source bytes, executable bytes and the executable's own
case protocol separately from its native assertion outcome. They do not replace
kernel certificates or establish historical build provenance.
"""
from __future__ import annotations

import argparse
import codecs
import hashlib
import json
import os
import re
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

from scripts import paths
from scripts.profiling import branch_builds, build_costs

DIGESTS = build_costs.Digests()


def key(value: object) -> str:
    """Identify an exact finite request by canonical JSON bytes."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def source_revision(root: Path) -> dict:
    """Observe the actual project Lean revision and the retained execution tools."""
    files = {str(p.relative_to(root)): DIGESTS.sha(p)
             for name in ("Purelib", "TestPurelib", "scripts", "papers", "formalisations")
             if (root / name).exists() for p in sorted((root / name).rglob("*.lean"))}
    files.update({name: DIGESTS.sha(root / name)
                  for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")})
    tools = {str(p): DIGESTS.sha(p) for p in
             (Path(__file__), Path(branch_builds.__file__), Path(build_costs.__file__), Path(paths.__file__))}
    prefix = root / ".lake/core-toolchain/CORE-PREFIX.json"
    return {"revision": key(files), "files": files, "execution_tools": tools,
            "core_receipt_sha256": DIGESTS.sha(prefix) if prefix.is_file() else None,
            "python_sha256": DIGESTS.sha(Path(sys.executable)),
            "runtime_libraries": {str(p.resolve()): DIGESTS.sha(p) for p in
                sorted((root / ".lake/core-toolchain/lib/lean").glob("*shared*.so"))},
            "environment": {name: os.environ.get(name) for name in ("LEAN_NUM_THREADS", "LD_LIBRARY_PATH")},
            "scope": "Observed source content; compilation ancestry is separate build evidence."}


def worker_identity(pid: int) -> dict:
    """Retain the actual owned native worker's namespace, start and group."""
    data = (Path("/proc") / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
    return {"pid": pid, "start_ticks": data[19], "pgid": os.getpgid(pid),
            "namespace": os.stat("/proc/self/ns/pid").st_ino}


def group_members(pgid: int) -> list[int]:
    """Inspect live membership of this request's group; owners still reap zombies."""
    members = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if fields[0] != "Z" and int(fields[2]) == pgid:
                members.append(int(entry.name))
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return members


def stop_worker_group(owner: dict) -> None:
    """Stop the retained group, including children surviving its original leader."""
    if owner["namespace"] != os.stat("/proc/self/ns/pid").st_ino:
        raise RuntimeError("cannot stop a worker group from another PID namespace")
    if owner["start_ticks"] is not None:
        try:
            if worker_identity(owner["pid"]) != owner:
                raise RuntimeError("retained worker leader identity changed")
        except (FileNotFoundError, ProcessLookupError):
            pass
    members = []
    for pid in group_members(owner["pgid"]):
        try:
            member = worker_identity(pid)
        except (FileNotFoundError, ProcessLookupError):
            continue
        if member["pgid"] == owner["pgid"]:
            members.append(member)
    if not members:
        return
    # A surviving member retains the original process-group ID after the
    # leader exits. Verify its start identity before signalling that group.
    def remaining():
        retained = []
        for member in members:
            try:
                if worker_identity(member["pid"]) == member:
                    state = (Path("/proc") / str(member["pid"]) / "stat").read_text().rsplit(")", 1)[1].split()[0]
                    if state != "Z":
                        retained.append(member)
            except (FileNotFoundError, ProcessLookupError):
                pass
        return retained

    for requested in (signal.SIGTERM, signal.SIGKILL):
        if not remaining():
            return
        try:
            os.killpg(owner["pgid"], requested)
        except ProcessLookupError:
            return
        deadline = time.monotonic() + 5
        while remaining() and time.monotonic() < deadline:
            time.sleep(.02)
    if remaining():
        raise RuntimeError("retained worker group still has live members after stopping")


def preserve_incomplete(directory: Path) -> None:
    """Preserve an unfinished attempt after ruling out its recorded live worker."""
    if not directory.exists() or (directory / "result.json").exists():
        return
    state_path = directory / "state.json"
    if not state_path.exists():
        raise RuntimeError(f"unrecorded partial attempt requires review: {directory}")
    state = json.loads(state_path.read_text())
    if state["status"] == "RUNNING":
        owner = state["worker"]
        if owner["namespace"] != os.stat("/proc/self/ns/pid").st_ino:
            raise RuntimeError(f"cannot rule out an unfinished worker in another namespace: {state_path}")
        try:
            if worker_identity(owner["pid"]) == owner:
                raise RuntimeError(f"recorded worker is still live: {state_path}")
        except (FileNotFoundError, ProcessLookupError):
            pass
        if group_members(owner["pgid"]):
            raise RuntimeError(f"recorded worker group still has live members: {state_path}")
    elif state.get("live_handles"):
        raise RuntimeError(f"unfinished worker handles require review: {state_path}")
    directory.rename(directory.with_name(directory.name + ".interrupted." + str(time.time_ns())))


def forward_input_digests(process: subprocess.Popen, log, events) -> dict:
    """Hash each exact framed UTF8 input and retain its bytes before replying.

    The native comparison-case and winding-child CLI routes use this same
    transport. The log retains complete original stdout, including every
    payload; the event offsets identify those bytes without copying them into
    an aggregate. Closing input at EOF or failure releases the retained pipe.
    """
    if process.stdout is None or process.stdin is None:
        raise ValueError("digest transport requires both original process pipes")
    offset = count = 0
    prefix = b"CCL_WINDING_SHA256_V1 "
    try:
        while True:
            raw = process.stdout.readline()
            if not raw:
                break
            log.write(raw)
            log.flush()
            if not raw.startswith(prefix):
                offset += len(raw)
                continue
            if re.fullmatch(rb"CCL_WINDING_SHA256_V1 (0|[1-9][0-9]*)\n", raw) is None:
                raise ValueError("malformed digest frame length")
            length = int(raw[len(prefix):-1])
            remaining = length
            digest = hashlib.sha256()
            decoder = codecs.getincrementaldecoder("utf-8")("strict")
            while remaining:
                chunk = process.stdout.read(min(remaining, 65536))
                if not chunk:
                    raise EOFError("incomplete actual UTF8 digest payload")
                log.write(chunk)
                digest.update(chunk)
                decoder.decode(chunk, final=False)
                remaining -= len(chunk)
            decoder.decode(b"", final=True)
            log.flush()
            result = digest.hexdigest()
            events.write(json.dumps({"ordinal": count, "stdout_offset": offset,
                "header_bytes": len(raw), "payload_bytes": length, "sha256": result,
                "operation": "hashlib.sha256(actual retained UTF8 payload)"}) + "\n")
            events.flush()
            response = result.encode("ascii") + b"\n"
            if process.stdin.write(response) != len(response):
                raise OSError("short digest reply write")
            process.stdin.flush()
            offset += len(raw) + length
            count += 1
        return {"requests": count, "stdout_bytes": offset}
    finally:
        process.stdin.close()


def run_cases(binary: Path, root: Path, store: Path, selected: list[str] | None = None,
              after_case: int | None = None, *, root_request: tuple[Path, str] | None = None,
              input_digest_stdio: bool = False,
              case_protocol: tuple[str, str] | None = None) -> list[dict]:
    """Reuse exact completed compound or original-root requests with atomic native receipts."""
    if input_digest_stdio and root_request is None:
        raise ValueError("stdio input digests require an original root-comparison request")
    if case_protocol is not None:
        if len(case_protocol) != 2 or any(
                not re.fullmatch(r"--[a-z][a-z-]*", flag) for flag in case_protocol):
            raise ValueError("select two explicit case-protocol flags")
        protocol_flag, case_flag = case_protocol
    elif root_request is None:
        protocol_flag, case_flag = "--compound-cases", "--compound-case"
    else:
        protocol_flag, case_flag = "--comparison-cases", "--comparison-case"
    case_arguments = []
    if root_request is not None:
        directory, mode = root_request
        if mode not in ("resume", "replay", "interrupt"):
            raise ValueError("comparison checkpoint mode must be resume, replay or interrupt")
        case_arguments = [str(directory.resolve()), mode]
    binary = binary.resolve()
    binary_sha = DIGESTS.sha(binary)
    protocol = subprocess.run([str(binary), protocol_flag], check=True,
                              stdout=subprocess.PIPE, text=True).stdout.splitlines()
    if not protocol or len(protocol) != len(set(protocol)) or any(
            not re.fullmatch("[a-z][a-z0-9-]*", case) for case in protocol):
        raise ValueError("the executable returned an empty or duplicate case protocol")
    requested = protocol if selected is None else selected
    if not requested or len(requested) != len(set(requested)) or any(c not in protocol for c in requested):
        raise ValueError("select a nonempty ordered subset of the executable's actual case protocol")
    if after_case is not None and not 1 <= after_case <= len(requested):
        raise ValueError("the interruption hook must follow a requested completed case")
    sources = source_revision(root)
    identity = {"binary": str(binary), "binary_sha256": binary_sha, "protocol": protocol,
                "source_revision": sources, "time_tool_sha256": DIGESTS.sha(Path("/usr/bin/time"))}
    if case_protocol is not None:
        identity["case_protocol"] = list(case_protocol)
    if root_request is not None:
        identity["root_comparison_request"] = {"directory": case_arguments[0], "mode": case_arguments[1]}
    if input_digest_stdio:
        identity["input_digest_transport"] = "CCL_WINDING_SHA256_V1"
    identity_key = key(identity)
    manifests = store / "manifests"
    manifests.mkdir(parents=True, exist_ok=True)
    manifest = manifests / (identity_key + ".json")
    if manifest.exists():
        if json.loads(manifest.read_text()) != identity:
            raise RuntimeError(f"corrupt shared input manifest: {manifest}")
    else:
        branch_builds.atomic_json(manifest, identity)
    manifest_sha = DIGESTS.sha(manifest)
    invocation = store / "runs" / (str(time.time_ns()) + ".json")
    invocation.parent.mkdir(exist_ok=True)
    completed = []
    for case in requested:
        command = [str(binary), case_flag, case, *case_arguments]
        if input_digest_stdio:
            command.append("--input-digest-stdio-v1")
        request = {"manifest": str(manifest), "manifest_sha256": manifest_sha,
                   "identity": identity_key, "case": case, "command": command}
        directory = store / "cases" / identity_key / case
        directory.parent.mkdir(parents=True, exist_ok=True)
        preserve_incomplete(directory)
        reused = (directory / "result.json").exists()

        def execute(output: Path) -> dict:
            started = time.monotonic()
            interrupted = False
            errors = []
            with (output / "stdout.log").open("wb") as log:
                transport = {}
                reader = None
                # Open every output before spawning; all operations after a
                # successful spawn must remain inside its owning wait.
                events = (output / "digest-events.jsonl").open("w") if input_digest_stdio else None
                namespace = os.stat("/proc/self/ns/pid").st_ino
                if input_digest_stdio:
                    process = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(output / "time.txt"), *command],
                                               stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                               stderr=subprocess.STDOUT, start_new_session=True, bufsize=0)
                else:
                    process = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(output / "time.txt"), *command],
                                               stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                owner = {"pid": process.pid, "pgid": process.pid, "start_ticks": None,
                         "namespace": namespace}
                try:
                    owner = worker_identity(process.pid)
                    if input_digest_stdio:
                        def read_output():
                            try:
                                transport.update(forward_input_digests(process, log, events))
                            except Exception as error:
                                transport["failure"] = repr(error)
                                try:
                                    stop_worker_group(owner)
                                except Exception as stopping:
                                    transport["stop_failure"] = repr(stopping)

                        reader = threading.Thread(target=read_output, name="original-input-digest-reader")
                        reader.start()
                    branch_builds.atomic_json(output / "state.json", {"status": "RUNNING", "worker": owner})
                    code = process.wait()
                except BaseException as error:
                    interrupted = isinstance(error, (KeyboardInterrupt, SystemExit))
                    errors.append({"phase": "setup_or_wait", "failure": repr(error)})
                    try:
                        stop_worker_group(owner)
                    except Exception as stopping:
                        errors.append({"phase": "stop", "failure": repr(stopping)})
                    code = process.wait()
                # Persist the returned raw code before closing any stream or
                # reading process-group/log metadata. Later failures cannot
                # turn this attempt into a successful cache entry.
                try:
                    branch_builds.atomic_json(output / "exit.json", {"exit_code": code, "errors": list(errors)})
                except Exception as error:
                    errors.append({"phase": "raw_exit_receipt", "failure": repr(error)})
                live = None
                try:
                    live = group_members(owner["pgid"])
                    if live:
                        stop_worker_group(owner)
                        errors.append({"phase": "group", "failure": "worker group survived its leader"})
                        live = group_members(owner["pgid"])
                except Exception as error:
                    errors.append({"phase": "group", "failure": repr(error)})
                if reader is not None:
                    if reader.ident is not None:
                        reader.join()
                if events is not None:
                    events.close()
                if process.stdout is not None:
                    process.stdout.close()
                if process.stdin is not None and not process.stdin.closed:
                    process.stdin.close()
            state = {"status": "STOPPED" if interrupted else "TERMINAL", "worker": owner,
                     "exit_code": code, "live_handles": live, "errors": errors}
            branch_builds.atomic_json(output / "state.json", state)
            receipt = {"request": request, "worker": owner, "exit_code": code,
                       "seconds": time.monotonic() - started, "live_handles": live,
                       "errors": errors,
                       "outcome": "native-assertions-passed" if code == 0 and not interrupted and not errors
                                  and live == [] and not transport.get("failure")
                                  else "attempt-stopped-or-failed"}
            if input_digest_stdio:
                receipt["input_digest_transport"] = transport
            branch_builds.atomic_json(output / "native.json", receipt)
            if interrupted:
                raise KeyboardInterrupt("native attempt stopped; earlier completed cases remain reusable")
            if code != 0 or live != [] or errors or transport.get("failure"):
                raise RuntimeError(f"native request failed or left a worker: {output}")
            if DIGESTS.sha(binary) != binary_sha or source_revision(root) != sources:
                raise RuntimeError("execution inputs changed; no success checkpoint published")
            return {"outcome": "native-assertions-passed", "request": request}

        result = branch_builds.cached(directory, key(request), execute)
        expected_outputs = {"stdout.log", "time.txt", "state.json", "exit.json", "native.json"}
        if input_digest_stdio:
            expected_outputs.add("digest-events.jsonl")
        native = json.loads((directory / "native.json").read_text())
        state = json.loads((directory / "state.json").read_text())
        raw_exit = json.loads((directory / "exit.json").read_text())
        if (set(result) != {"outcome", "request", "key", "outputs"} or
                set(result["outputs"]) != expected_outputs or result["request"] != request or
                result["outcome"] != "native-assertions-passed" or native["request"] != request or
                native["exit_code"] != 0 or native["live_handles"] or native["errors"] or
                native["outcome"] != "native-assertions-passed" or state["status"] != "TERMINAL" or
                state["exit_code"] != 0 or state["live_handles"] or state["errors"] or
                state["worker"] != native["worker"] or raw_exit != {"exit_code": 0, "errors": []}):
            raise RuntimeError(f"invalid complete native checkpoint: {directory}")
        if input_digest_stdio and ("failure" in native.get("input_digest_transport", {}) or
                set(native.get("input_digest_transport", {})) != {"requests", "stdout_bytes"}):
            raise RuntimeError(f"invalid complete digest transport checkpoint: {directory}")
        completed.append({"case": case, "reused": reused, "receipt": str(directory / "result.json"),
                          "receipt_sha256": DIGESTS.sha(directory / "result.json"), "outcome": result["outcome"]})
        status = "STOPPED_AFTER_COMPLETED_CASE" if after_case == len(completed) else "RUNNING"
        branch_builds.atomic_json(invocation, {"manifest": str(manifest), "manifest_sha256": manifest_sha,
            "requested": requested, "completed": completed, "status": status,
            "invocation_hook": after_case, "native_outcome_is_not_a_kernel_certificate": True})
        if after_case == len(completed):
            raise SystemExit(17)
    if DIGESTS.sha(binary) != binary_sha or source_revision(root) != sources:
        raise RuntimeError("execution inputs changed before final receipt")
    branch_builds.atomic_json(invocation, {"manifest": str(manifest), "manifest_sha256": manifest_sha,
        "requested": requested, "completed": completed, "status": "COMPLETED",
        "invocation_hook": after_case, "native_outcome_is_not_a_kernel_certificate": True})
    return completed


def main() -> None:
    """Select real harness requests and retain checked atomic native checkpoints."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", type=Path, default=paths.ROOT / ".lake/build/bin/cubic_sheets_harness")
    parser.add_argument("--store", type=Path, required=True)
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--case-protocol", choices=("compound", "cubic-roots"), default="compound",
                        help="select the executable's compound or independent cubic-root case interface")
    parser.add_argument("--after-case", type=int, help="exit17 after this many atomically completed cases; recovery hook")
    parser.add_argument("--checkpoint-directory", type=Path,
                        help="retain original numerical checkpoints for the selected root-comparison protocol")
    parser.add_argument("--checkpoint-mode", choices=("resume", "replay", "interrupt"))
    parser.add_argument("--input-digest-stdio-v1", action="store_true",
                        help="hash exact framed root input bytes in the retained driver process")
    args = parser.parse_args()
    if args.checkpoint_mode is not None and args.checkpoint_directory is None:
        parser.error("--checkpoint-mode requires --checkpoint-directory")
    if args.input_digest_stdio_v1 and args.checkpoint_directory is None:
        parser.error("--input-digest-stdio-v1 requires --checkpoint-directory")
    def interrupt(_signal, _frame):
        raise KeyboardInterrupt("native driver interrupted")
    signal.signal(signal.SIGTERM, interrupt)
    root_request = ((args.checkpoint_directory, args.checkpoint_mode or "resume")
                    if args.checkpoint_directory is not None else None)
    run_cases(args.executable, paths.ROOT, args.store.resolve(), args.cases, args.after_case,
              root_request=root_request, input_digest_stdio=args.input_digest_stdio_v1,
              case_protocol=("--root-comparison-cases", "--root-comparison-case")
                  if args.case_protocol == "cubic-roots" else None)


if __name__ == "__main__":
    main()
