"""Manage nested task checkouts using Git's current worktree inventory."""

from __future__ import annotations

import argparse
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

from scripts.paths import ROOT
from scripts.profiling.build_costs import atomic


def git(root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    """Run Git against the selected checkout without optional index writes."""
    env = dict(os.environ, GIT_OPTIONAL_LOCKS="0")
    for key in ("GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE"):
        env.pop(key, None)
    result = subprocess.run(["git", "-C", str(root), *args], env=env,
                            capture_output=True, text=True, errors="surrogateescape")
    if check and result.returncode:
        raise ValueError(result.stderr.strip() or result.stdout.strip() or "Git command failed")
    return result


def original_root(path: Path) -> Path:
    """Find the outermost containing checkout belonging to this same repository."""
    root = Path(git(path, "rev-parse", "--show-toplevel").stdout.strip()).resolve()
    common = git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").stdout.strip()
    for parent in root.parents:
        if (parent / ".git").exists():
            found = git(parent, "rev-parse", "--path-format=absolute", "--git-common-dir", check=False)
            if found.returncode == 0 and found.stdout.strip() == common:
                root = parent
    return root


def inventory(root: Path) -> list[dict]:
    """Read NUL-delimited paths and ownership directly from Git."""
    output = git(root, "worktree", "list", "--porcelain", "-z").stdout
    rows = []
    for block in output.strip("\0").split("\0\0"):
        fields = dict(field.partition(" ")[::2] for field in block.split("\0") if field)
        if "worktree" in fields:
            rows.append(fields)
    return rows


def commit(root: Path, revision: str) -> str:
    """Resolve an explicit commit without accepting revision options."""
    return git(root, "rev-parse", "--verify", "--end-of-options", revision + "^{commit}").stdout.strip()


def merged(root: Path, head: str, base: str) -> bool:
    """Require ancestry in the chosen integration base, rather than a clean diff."""
    result = git(root, "merge-base", "--is-ancestor", head, base, check=False)
    if result.returncode not in (0, 1):
        raise ValueError(result.stderr.strip())
    return result.returncode == 0


def slug(topic: str) -> str:
    """Give a branch one readable directory component without traversal."""
    value = re.sub(r"[^A-Za-z0-9._-]+", "-", topic).strip(".-")
    if not value:
        raise ValueError("the topic has no usable directory name")
    return value


def task_directory(root: Path) -> Path:
    """Require the original checkout's ignored, nonsymlink worktree directory."""
    directory = root / ".worktrees"
    if directory.is_symlink():
        raise ValueError(".worktrees must not be a symlink")
    if git(root, "check-ignore", "--quiet", "--no-index", "--", ".worktrees/.policy-probe",
           check=False).returncode != 0:
        raise ValueError("ignore /.worktrees/ in the original checkout before creating or archiving worktrees")
    directory.mkdir(exist_ok=True)
    return directory


def create(root: Path, topic: str, base: str = "master") -> Path:
    """Create or check out a topic branch beneath the original task root."""
    git(root, "check-ref-format", "--branch", topic)
    if topic == "master":
        raise ValueError("task worktrees require a topic branch")
    destination = task_directory(root) / slug(topic)
    if destination.exists() or destination.is_symlink():
        raise ValueError(f"destination already exists: {destination}")
    if any(row.get("branch") == "refs/heads/" + topic for row in inventory(root)):
        raise ValueError(f"branch is already checked out: {topic}")
    exists = git(root, "show-ref", "--verify", "--quiet", "refs/heads/" + topic, check=False)
    if exists.returncode not in (0, 1):
        raise ValueError(exists.stderr.strip())
    if exists.returncode == 0:
        git(root, "worktree", "add", str(destination), topic)
    else:
        git(root, "worktree", "add", "-b", topic, str(destination), commit(root, base))
    return destination


def ignored_paths(path: Path) -> list[str]:
    """Inventory every ignored file or opaque directory that removal would discard."""
    output = git(path, "ls-files", "--others", "--ignored", "--exclude-standard",
                 "--directory", "-z").stdout
    return [name.rstrip("/") for name in output.split("\0") if name]


def active_processes(path: Path) -> list[int]:
    """Find visible processes with a working directory, executable or open file here."""
    if not Path("/proc").is_dir():
        raise ValueError("retirement's process-use check requires Linux /proc")
    result = []
    for folder in Path("/proc").iterdir():
        if not folder.name.isdecimal():
            continue
        links = [folder / "cwd", folder / "exe"]
        try:
            links.extend((folder / "fd").iterdir())
        except OSError:
            pass
        for link in links:
            try:
                target = Path(os.readlink(link).removesuffix(" (deleted)"))
            except OSError:
                continue
            if target == path or path in target.parents:
                result.append(int(folder.name))
                break
    return result


def selected_worktree(root: Path, target: str, rows: list[dict]) -> dict:
    """Select one registered worktree by topic, task slug or explicit path."""
    for row in rows:
        if row.get("branch") == "refs/heads/" + target:
            return row
    paths = {(Path.cwd() / target).resolve(), (root / ".worktrees" / target).resolve()}
    matches = [row for row in rows if Path(row["worktree"]).resolve() in paths]
    if len(matches) != 1:
        raise ValueError(f"target does not identify one registered worktree: {target}")
    return matches[0]


def retire(root: Path, target: str, base: str = "master") -> dict:
    """Retire a clean, merged checkout, preserving all ignored data and its branch."""
    rows = inventory(root)
    row = selected_worktree(root, target, rows)
    path = Path(row["worktree"]).resolve()
    if path in (root, Path(rows[0]["worktree"]).resolve()):
        raise ValueError("cannot retire the original task root or main worktree")
    if "locked" in row:
        raise ValueError(f"worktree is locked: {row['locked']}")
    if not path.is_dir():
        raise ValueError("missing checkout: preserve detached tips before pruning stale registrations")
    if any(path in Path(other["worktree"]).resolve().parents for other in rows if other is not row):
        raise ValueError("retire or relocate registered child worktrees first")
    if git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all").stdout:
        raise ValueError("worktree has tracked changes or untracked files")
    head, base_head = commit(path, "HEAD"), commit(root, base)
    if not merged(root, head, base_head):
        raise ValueError(f"worktree has commits not contained in {base}")
    if busy := active_processes(path):
        raise ValueError(f"worktree is in use by visible processes: {busy}")
    ignored = ignored_paths(path)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    topic = row.get("branch", "").removeprefix("refs/heads/") or path.name
    retained = task_directory(root) / ".retired"
    if retained.is_symlink():
        raise ValueError(".worktrees/.retired must not be a symlink")
    archive = retained / (slug(topic) + "-" + stamp + "-" + uuid.uuid4().hex[:8])
    archive.mkdir(parents=True)
    receipt = {"worktree": str(path), "head": head, "branch": row.get("branch"),
               "base": base_head, "ignored": ignored, "archive": str(archive), "status": "preserving"}
    atomic(archive / "retirement.json", receipt)
    moved = []
    try:
        for name in ignored:
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError("unsafe ignored path: " + name)
            destination = archive / "ignored" / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            # Require an atomic same-filesystem rename: never copy then discard
            # a partly preserved checkpoint store after a failed cross-device move.
            (path / relative).rename(destination)
            moved.append(relative)
        if commit(path, "HEAD") != head or git(path, "status", "--porcelain=v1", "-z",
                                              "--untracked-files=all").stdout:
            raise ValueError("worktree changed during retirement")
        if ignored_paths(path):
            raise ValueError("new ignored data appeared during retirement")
        current = selected_worktree(root, str(path), inventory(root))
        if "locked" in current or current.get("branch") != row.get("branch"):
            raise ValueError("worktree ownership or lock changed during retirement")
        if any(path in Path(other["worktree"]).resolve().parents for other in inventory(root)
               if Path(other["worktree"]).resolve() != path):
            raise ValueError("a registered child worktree appeared during retirement")
        if busy := active_processes(path):
            raise ValueError(f"worktree became busy during retirement: {busy}")
        git(root, "worktree", "remove", str(path))
    except BaseException as error:
        # Restore retained data when the checkout still exists. If Git partly
        # removed it, retain the archive and identify exactly what remains there.
        remaining = []
        for relative in reversed(moved):
            try:
                destination = path / relative
                if not path.is_dir() or destination.exists() or destination.is_symlink():
                    raise OSError("original path unavailable")
                destination.parent.mkdir(parents=True, exist_ok=True)
                (archive / "ignored" / relative).rename(destination)
            except OSError:
                remaining.append(str(relative))
        receipt.update(status="failed", error=str(error), retained_ignored=remaining)
        atomic(archive / "retirement.json", receipt)
        raise ValueError(f"retirement failed: {error}; recovery receipt: {archive / 'retirement.json'}") from error
    receipt["status"] = "retired"
    atomic(archive / "retirement.json", receipt)
    return receipt


def listing(root: Path, base: str) -> list[dict]:
    """Describe current checkouts without trusting a separately maintained registry."""
    base_head = commit(root, base)
    rows = inventory(root)
    for row in rows:
        path = Path(row["worktree"])
        row["exists"] = path.is_dir()
        row["merged"] = merged(root, row["HEAD"], base_head)
        row["dirty"] = (bool(git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all").stdout)
                        if path.is_dir() else None)
        row["ignored"] = ignored_paths(path) if path.is_dir() else []
    return rows


def main(argv=None) -> int:
    """Dispatch explicit worktree creation, inspection and retirement."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="original task checkout (default: this repository)")
    commands = parser.add_subparsers(dest="command", required=True)
    show = commands.add_parser("list", help="show Git's current worktrees, changes and retained stores")
    show.add_argument("--base", default="master")
    show.add_argument("--json", action="store_true")
    add = commands.add_parser("create", help="create a nested topic worktree")
    add.add_argument("topic")
    add.add_argument("--base", default="master")
    remove = commands.add_parser("retire", help="remove a clean merged worktree, archiving ignored data")
    remove.add_argument("target", help="topic branch, task slug or registered absolute path")
    remove.add_argument("--base", default="master")
    args = parser.parse_args(argv)
    try:
        root = original_root(args.root)
        if args.command == "create":
            print(create(root, args.topic, args.base))
        elif args.command == "retire":
            result = retire(root, args.target, args.base)
            print(f"Retired {result['worktree']}; branch retained; ignored data and receipt: {result['archive']}")
        else:
            rows = listing(root, args.base)
            if args.json:
                print(json.dumps({"root": str(root), "worktrees": rows}, indent=2))
            else:
                for row in rows:
                    topic = row.get("branch", "detached").removeprefix("refs/heads/")
                    state = ["merged" if row["merged"] else "unmerged"]
                    state += [key for key in ("locked", "prunable") if key in row]
                    if row["dirty"]:
                        state.append("dirty")
                    if row["ignored"]:
                        state.append(f"{len(row['ignored'])} ignored entries")
                    print(f"{topic}\t{', '.join(state)}\t{row['worktree']}")
        return 0
    except (OSError, ValueError) as error:
        print(f"worktrees: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
