"""Keep failed Lean inputs and diagnostics before temporary files are removed."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import sys
import tempfile
import traceback


class FailureArchive:
    """An exception-transparent context; nested uses save the failure only once."""

    def __init__(self, tool_dir, operation, sources, metadata=None, *, directory=None):
        self.tool_dir = Path(tool_dir)
        self.directory = Path(directory) if directory is not None else self.tool_dir / "failures"
        self.operation = operation
        self.sources = dict(sources)
        self.metadata = metadata or {}
        self.files = {}

    def __enter__(self):
        return self

    def __exit__(self, exc_type, error, tb):
        if os.environ.get("LEAN_TOOL_FAILURE_ARCHIVE") == "0":
            return False
        if error is None or not isinstance(error, Exception):
            return False
        if getattr(error, "failure_directory", None):
            return False
        try:
            parent = self.directory
            parent.mkdir(parents=True, exist_ok=True)
            stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ-")
            directory = Path(tempfile.mkdtemp(prefix=stamp, dir=parent))
            saved, copy_errors = {}, {}
            for name, source in {**self.sources, **self.files}.items():
                try:
                    if isinstance(source, Path):
                        # Do not follow files replaced by a Lean worker with symlinks.
                        if name in self.files and source.is_symlink():
                            raise OSError("refusing to archive a symbolic link")
                        if name in self.files and not source.exists():
                            continue
                        content = source.read_bytes()
                    else:
                        content = source.encode("utf-8")
                    (directory / name).write_bytes(content)
                    saved[name] = str(source) if isinstance(source, Path) else "inline"
                except (OSError, ValueError) as copy_error:
                    copy_errors[name] = str(copy_error)
            report = {
                "tool": self.tool_dir.name, "operation": self.operation,
                "created_at": datetime.now(timezone.utc).isoformat(),
                "cwd": str(Path.cwd()), "parameters": self.metadata,
                "error_type": exc_type.__name__, "error": str(error),
                "files": saved, "copy_errors": copy_errors,
            }
            # TimeoutExpired may contain bytes even when text=True.
            for field in ("cmd", "timeout", "stdout", "stderr"):
                value = getattr(error, field, None)
                if value is not None:
                    report[field] = value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value
            (directory / "failure.json").write_text(
                json.dumps(report, ensure_ascii=False, indent=2, default=str) + "\n", encoding="utf-8")
            (directory / "error.txt").write_text(
                "".join(traceback.format_exception(exc_type, error, tb)), encoding="utf-8")
            error.failure_directory = str(directory)
            print(f"{self.tool_dir.name}: failure saved to {directory}", file=sys.stderr)
        except Exception as archive_error:
            # Archiving must never replace the original failure.
            print(f"{self.tool_dir.name}: could not save failure: {archive_error}", file=sys.stderr)
        return False
