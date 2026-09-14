"""Run extraction against versioned upstream Lean sources and retain evidence."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
LEAN_REV = "d8204c9fd894f91bbb2cdfec5912ec8196fd8562"
MATHLIB_REV = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
CASES = [
    {
        "id": "hashmap", "suite": "std", "repo": "leanprover/lean4", "commit": LEAN_REV,
        "path": "src/Std/Data/HashMap/Lemmas.lean", "local": "HashMapLemmas.lean",
        "theorem": "Std.HashMap.getElem!_map'",
    },
    {
        "id": "treemap", "suite": "std", "repo": "leanprover/lean4", "commit": LEAN_REV,
        "path": "src/Std/Data/TreeMap/Lemmas.lean", "local": "TreeMapLemmas.lean",
        "theorem": "Std.TreeMap.equiv_iff_toList_eq",
    },
    {
        "id": "list", "suite": "mathlib", "repo": "leanprover-community/mathlib4", "commit": MATHLIB_REV,
        "path": "Mathlib/Data/List/Basic.lean", "theorem": "List.foldl_assoc_comm_cons",
    },
    {
        "id": "finset", "suite": "mathlib", "repo": "leanprover-community/mathlib4", "commit": MATHLIB_REV,
        "path": "Mathlib/Data/Finset/Card.lean", "theorem": "Finset.card_eq_four",
    },
    {
        "id": "trigonometric", "suite": "mathlib", "repo": "leanprover-community/mathlib4", "commit": MATHLIB_REV,
        "path": "Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean", "theorem": "Real.cos_pi_div_five",
    },
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def measure(path: Path) -> dict:
    data = path.read_bytes()
    return {
        "bytes": len(data), "lines": len(data.splitlines()),
        "nonempty_lines": sum(bool(line.strip()) for line in data.splitlines()),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def run_stage(command: list[str], cwd: Path, log: Path, timeout: int) -> dict:
    started = time.perf_counter()
    with log.open("wb") as stream:
        try:
            proc = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
            code = proc.returncode
        except subprocess.TimeoutExpired:
            stream.write(b"\nBENCHMARK TIMEOUT\n")
            code = 124
    return {"command": command, "cwd": str(cwd), "exit_code": code,
            "seconds": round(time.perf_counter() - started, 3), "log": str(log)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=["std", "mathlib", "all"], default="all")
    parser.add_argument("--case", action="append", help="run only the named case IDs")
    parser.add_argument("--lean", default=shutil.which("lean") or "lean")
    parser.add_argument("--mathlib", type=Path, default=ROOT / ".real-world/mathlib4")
    parser.add_argument("--results", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    results = (args.results or ROOT / ".real-world/results" / timestamp).resolve()
    results.mkdir(parents=True, exist_ok=False)
    prefix = Path(subprocess.check_output([args.lean, "--print-prefix"], cwd=ROOT, text=True).strip())
    lean = str(prefix / "bin/lean")
    lake = str(prefix / "bin/lake")
    report = {
        "started_utc": timestamp,
        "lean": subprocess.check_output([lean, "--version"], text=True).strip(),
        "worker_sha256": digest(ROOT / "LeanExtract.lean"),
        "launcher_sha256": digest(ROOT / "lean_extract.py"),
        "cases": [],
    }
    sources = ROOT / ".real-world/sources"
    sources.mkdir(parents=True, exist_ok=True)
    for case in CASES:
        if args.suite != "all" and case["suite"] != args.suite:
            continue
        if args.case and case["id"] not in args.case:
            continue
        item = dict(case)
        item["source_url"] = f"https://github.com/{case['repo']}/blob/{case['commit']}/{case['path']}"
        directory = results / case["id"]
        directory.mkdir()
        if case["suite"] == "std":
            source = sources / case["local"]
            if not source.exists():
                url = f"https://raw.githubusercontent.com/{case['repo']}/{case['commit']}/{case['path']}"
                subprocess.run(["curl", "--http1.1", "-fsSL", "--retry", "3", "--retry-all-errors", "--max-time", "60", url, "-o", str(source)], check=True)
            # Compare the downloaded bytes with the selected toolchain's exact source version.
            installed = prefix / "src/lean" / case["path"].removeprefix("src/")
            if source.read_bytes() != installed.read_bytes():
                raise RuntimeError(f"upstream source differs from selected toolchain: {source}")
            cwd = source.parent
            # Core's Std namespace enables this option implicitly when building upstream.
            # Renamed standalone copies need the same option explicitly.
            checker = [lean, "-Dexperimental.module=true"]
            output_checker = checker
            extra = []
        else:
            project = args.mathlib.resolve()
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
            if revision != MATHLIB_REV:
                raise RuntimeError(f"expected Mathlib {MATHLIB_REV}, got {revision}")
            source = project / case["path"]
            cwd = project
            checker = [lake, "lean"]
            extra = ["--project", str(project)]
            setup = json.loads(subprocess.check_output([lake, "setup-file", str(source)], cwd=cwd, text=True))
            if setup["name"] in setup["importArts"]:
                raise RuntimeError("input module must not be an import of the output")
            # Library-level options do not follow a file moved outside Mathlib/.
            # Independently run Lean with the original module's complete setup.
            setup["name"] = "Extracted"
            setup_path = directory / "output.setup.json"
            setup_path.write_text(json.dumps(setup, indent=2) + "\n", encoding="utf-8")
            output_checker = [lake, "env", lean, "--setup", str(setup_path)]
        item["source"] = str(source)
        item["input"] = measure(source)
        output = directory / "Extracted.lean"
        print(f"{case['id']}: checking {item['input']['lines']} source lines", flush=True)
        item["original_check"] = run_stage(checker + [str(source)], cwd, directory / "original.log", args.timeout)
        if item["original_check"]["exit_code"] == 0:
            print(f"{case['id']}: extracting {case['theorem']}", flush=True)
            command = [sys.executable, str(ROOT / "lean-extract"), str(source), "--theorem", case["theorem"],
                       "--output", str(output), "--lean", lean, *extra]
            item["extraction"] = run_stage(command, cwd, directory / "extract.log", args.timeout)
            if item["extraction"]["exit_code"] == 0:
                item["output"] = measure(output)
                print(f"{case['id']}: independently checking {item['output']['lines']} output lines", flush=True)
                item["output_check"] = run_stage(output_checker + [str(output)], cwd, directory / "output.log", args.timeout)
        item["passed"] = item.get("output_check", {}).get("exit_code") == 0
        report["cases"].append(item)
        (results / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"{case['id']}: {'PASS' if item['passed'] else 'FAIL'}", flush=True)
    print(f"Evidence: {results / 'results.json'}", flush=True)
    return 0 if report["cases"] and all(item["passed"] for item in report["cases"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
