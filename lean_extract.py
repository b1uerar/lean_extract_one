"""Extract one theorem using Lean's frontend and byte ranges from its parser."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile


FailureArchive = runpy.run_path(str(Path(__file__).with_name("failure_archive.py")))["FailureArchive"]


WORKER = Path(__file__).resolve().with_name("LeanExtract.lean")


class ExtractionError(Exception):
    pass


def run_command(args: list[str], cwd: Path, env: dict[str, str]) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        if result.stdout:
            print(result.stdout, end="", file=sys.stderr)
        raise ExtractionError(f"command failed ({result.returncode}): {args[0]}\n"
                              f"{result.stdout}{result.stderr}".rstrip())
    return result.stdout


def find_project(source: Path) -> Path | None:
    for directory in source.parents:
        if any((directory / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
            return directory
    return None


def module_name(path: Path, project: Path | None) -> str:
    relative = path.relative_to(project) if project and path.is_relative_to(project) else Path(path.name)
    return ".".join(relative.with_suffix("").parts)


def environment(args: argparse.Namespace, source: Path) -> tuple[Path, str, dict[str, str], dict | None]:
    project = Path(args.project).expanduser().resolve() if args.project else find_project(source)
    if project and not any((project / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        raise ExtractionError(f"no Lake project at {project}")
    cwd = project or source.parent
    env = dict(os.environ)
    if args.lean:
        lean = shutil.which(args.lean)
        if lean is None:
            raise ExtractionError(f"Lean executable not found: {args.lean}")
        lean = os.path.abspath(lean)
    else:
        lean = shutil.which("lean")
        if lean is None:
            raise ExtractionError("Lean is not on PATH; use --lean /path/to/lean")
    prefix = Path(run_command([lean, "--print-prefix"], cwd, env).strip())
    lean = str(prefix / "bin" / "lean")
    version = run_command([lean, "--version"], cwd, env).strip()
    print(version, file=sys.stderr)
    if "version 4.26.0," not in version:
        print("lean-extract: this Lean version is unverified; tested with 4.26.0", file=sys.stderr)
    # Use the selected toolchain's Lake, even when the project pins another version.
    env["PATH"] = str(prefix / "bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_SYSROOT"] = str(prefix)
    setup = None
    if project:
        lake = str(prefix / "bin" / "lake")
        setup = json.loads(run_command([lake, "setup-file", str(source)], cwd, env))
        env = json.loads(run_command(
            [lake, "env", sys.executable, "-c", "import json, os; print(json.dumps(dict(os.environ)))"],
            cwd, env,
        ))
    return cwd, lean, env, setup


def extract(args: argparse.Namespace) -> dict:
    with FailureArchive(WORKER.parent, "extract",
                        {"input.lean": Path(args.input).expanduser().absolute()}, vars(args),
                        directory=getattr(args, "failure_dir", None)) as archive:
        return _extract(args, archive)


def _extract(args: argparse.Namespace, archive: FailureArchive) -> dict:
    source = Path(args.input).expanduser().resolve(strict=True)
    output = Path(args.output).expanduser().absolute()
    if not source.is_file() or source.suffix != ".lean":
        raise ExtractionError("input must be a .lean file")
    if output.suffix != ".lean":
        raise ExtractionError("output must have a .lean extension")
    if output.resolve() == source or (output.exists() and os.path.samefile(source, output)):
        raise ExtractionError("output must differ from input, including with --force")
    if output.is_symlink():
        raise ExtractionError("output must not be a symbolic link")
    if output.exists() and not args.force:
        raise ExtractionError(f"output exists: {output}; use --force to replace it")
    if not output.parent.is_dir():
        raise ExtractionError(f"output directory does not exist: {output.parent}")
    cwd, lean, env, setup = environment(args, source)
    original_module = setup["name"] if setup else module_name(source, None)
    output_module = module_name(output, cwd if args.project or find_project(source) else None)
    with tempfile.TemporaryDirectory(prefix="lean-extract-") as work, archive:
        workdir = Path(work)
        archive.files.update({name: workdir / name for name in
                              ("candidate.lean", "plan.json", "verified.json", "request.json")})
        candidate = workdir / "candidate.lean"
        plan_path = workdir / "plan.json"
        result_path = workdir / "verified.json"
        request_path = workdir / "request.json"
        request = {
            "mode": "extract", "input": str(source), "moduleName": original_module,
            "theoremName": args.theorem, "candidate": str(candidate),
            "result": str(plan_path), "setup": setup, "plan": "", "logicalFile": "",
        }
        print("lean-extract: analyzing input", file=sys.stderr)
        request_path.write_text(json.dumps(request), encoding="utf-8")
        diagnostics = run_command([lean, "--run", str(WORKER), str(request_path)], cwd, env)
        if diagnostics:
            print(diagnostics, end="", file=sys.stderr)
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
        request.update(mode="verify", input=str(candidate), moduleName=output_module,
                       plan=str(plan_path), result=str(result_path), logicalFile=str(output))
        request_path.write_text(json.dumps(request), encoding="utf-8")
        print("lean-extract: checking extracted source and theorem type", file=sys.stderr)
        diagnostics = run_command([lean, "--run", str(WORKER), str(request_path)], cwd, env)
        if diagnostics:
            print(diagnostics, end="", file=sys.stderr)
        if json.loads(result_path.read_text(encoding="utf-8")) != {"verified": True}:
            raise ExtractionError("Lean worker did not confirm verification")
        # Publish only a verified result; a failed run leaves existing output untouched.
        with tempfile.NamedTemporaryFile(dir=output.parent, prefix=".lean-extract-", delete=False) as staged:
            staging = Path(staged.name)
            staged.write(candidate.read_bytes())
        try:
            if args.force:
                os.replace(staging, output)
            else:
                os.link(staging, output)
        finally:
            staging.unlink(missing_ok=True)
    return plan


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Extract a Lean theorem and its local dependencies without rewriting proofs.")
    parser.add_argument("input", help="input .lean file")
    parser.add_argument("--theorem", required=True, help="full theorem name or an unambiguous short name")
    parser.add_argument("--output", required=True, help="output .lean file")
    parser.add_argument("--lean", help="Lean executable; defaults to the project's toolchain")
    parser.add_argument("--project", help="Lake project directory; discovered from input by default")
    parser.add_argument("--force", action="store_true", help="replace an existing output after verification")
    parser.add_argument("--failure-dir", type=Path,
                        help="failure archive directory; defaults to failures/ beside this tool")
    args = parser.parse_args(argv)
    try:
        plan = extract(args)
    except (ExtractionError, OSError, ValueError) as error:
        print(f"lean-extract: {error}", file=sys.stderr)
        return 1
    print(f"{args.output}: kept {plan['keptCommands']} commands, removed {plan['removedCommands']}; type verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
