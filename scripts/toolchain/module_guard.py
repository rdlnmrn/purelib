"""Prepare a compiler guard beside the checked SDK without changing that SDK."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile

from scripts.paths import ROOT
from scripts.verification.module_process import selected_timeout


def record_binding(target, binding):
    """Atomically refresh the complete control binding without renaming the SDK."""
    with tempfile.NamedTemporaryFile(mode='w', dir=target, delete=False) as output:
        temporary = Path(output.name)
        try:
            json.dump(binding, output, sort_keys=True)
            output.write('\n')
            output.flush()
            os.fsync(output.fileno())
            os.replace(temporary, target / 'MODULE-GUARD.json')
        finally:
            temporary.unlink(missing_ok=True)


def validate_overlay(prefix, target, binding, shim):
    """Check the actual entry point, cloned Lake and every SDK link before reuse."""
    if (target / 'bin/lean').is_symlink() or (target / 'bin/lean').read_text() != shim:
        raise ValueError('invalid module guard compiler entry point')
    for entry in prefix.iterdir():
        if entry.name != 'bin' and (target / entry.name).resolve() != entry.resolve():
            raise ValueError('invalid module guard SDK link: ' + entry.name)
    for entry in (prefix / 'bin').iterdir():
        if entry.name == 'lake':
            if ((target / 'bin/lake').is_symlink() or
                    hashlib.sha256((target / 'bin/lake').read_bytes()).hexdigest() != binding['lake']):
                raise ValueError('invalid guarded Lake executable')
        elif entry.name != 'lean' and (target / 'bin' / entry.name).resolve() != entry.resolve():
            raise ValueError('invalid module guard SDK tool: ' + entry.name)


def prepare(prefix, cache):
    """Retain every SDK entry, replacing only the source-compiler entry point."""
    prefix, cache = Path(prefix).resolve(), Path(cache).resolve()
    compiler = prefix / "bin/lean"
    helpers = [Path(__file__), ROOT / "scripts/verification/module_process.py",
               ROOT / "scripts/verification/processes.py", ROOT / "scripts/nanoda/processes.py",
               ROOT / "scripts/nanoda/benchmark_pipeline.py"]
    binding = {"prefix": str(prefix), "compiler": hashlib.sha256(compiler.read_bytes()).hexdigest(),
               "helpers": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in helpers},
               "module_timeout_seconds": selected_timeout()}
    if (prefix / "bin/lake").exists():
        binding['lake'] = hashlib.sha256((prefix / 'bin/lake').read_bytes()).hexdigest()
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / "prepare.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        shim = ("#!/usr/bin/env python3\nimport sys\n"
                f"sys.path.insert(0, {str(ROOT)!r})\n"
                "from scripts.verification.module_process import lean\n"
                f"raise SystemExit(lean({str(compiler)!r}, sys.argv[1:], "
                f"{str(ROOT / '.lake/module-times/lean')!r}))\n")
        # Paths in compiler and C commands must remain stable when only host
        # supervision changes. The complete helpers and deadline remain bound
        # in MODULE-GUARD.json, which audit/checkpoint consumers hash normally.
        sdk = {name: binding.get(name) for name in ('prefix', 'compiler', 'lake')}
        key = hashlib.sha256(json.dumps(dict(sdk, shim=shim), sort_keys=True).encode()).hexdigest()
        target = cache / key
        if not target.exists():
            for candidate in sorted(cache.iterdir()):
                manifest = candidate / 'MODULE-GUARD.json'
                if not candidate.is_dir() or not manifest.is_file():
                    continue
                try:
                    previous = json.loads(manifest.read_text())
                except (OSError, ValueError):
                    continue
                if (isinstance(previous, dict) and
                        str(ROOT / 'scripts/verification/module_process.py') in previous.get('helpers', {}) and
                        {name: previous.get(name) for name in sdk} == sdk):
                    target = candidate
                    break
        if target.exists():
            previous = json.loads((target / 'MODULE-GUARD.json').read_text())
            if not isinstance(previous, dict) or {name: previous.get(name) for name in sdk} != sdk:
                raise ValueError("invalid module guard compiler entry point")
            validate_overlay(prefix, target, binding, shim)
            if previous != binding:
                record_binding(target, binding)
            return target
        temporary = Path(tempfile.mkdtemp(prefix="prepare-", dir=cache))
        try:
            for entry in prefix.iterdir():
                if entry.name != "bin":
                    (temporary / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
            (temporary / "bin").mkdir()
            for entry in (prefix / "bin").iterdir():
                if entry.name == "lake":
                    # Lake prepends its own binary directory to `lake env`.
                    # A copy retains that directory here; a symlink resolves
                    # IO.appPath back to the unguarded installation.
                    shutil.copy2(entry, temporary / "bin/lake")
                elif entry.name != "lean":
                    (temporary / "bin" / entry.name).symlink_to(entry)
            (temporary / "bin/lean").write_text(shim)
            (temporary / "bin/lean").chmod(0o755)
            (temporary / "MODULE-GUARD.json").write_text(json.dumps(binding, sort_keys=True) + "\n")
            os.rename(temporary, target)
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)
        return target


def main():
    """Print the guarded sysroot selected for Lake's compiler resolution."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", required=True, type=Path)
    parser.add_argument("--cache", required=True, type=Path)
    args = parser.parse_args()
    print(prepare(args.prefix, args.cache))


if __name__ == "__main__":
    main()
