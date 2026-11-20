#!/usr/bin/env python3
"""Run trusted semantic fixtures through the genuine, isolated Comparator launcher.

This driver never invokes Lean or Lake directly. Each case gets a fresh source
copy with no prebuilt .lake directory. The launcher owns sandbox prerequisites
and must return the actual Comparator exit status, preserving its combined log.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time

FILES = (
    "Challenge.lean", "Solution.lean", "comparator.json", "lakefile.toml",
    "lake-manifest.json", "lean-toolchain",
)
CASES = ("positive", "sorry", "forbidden_axiom", "statement_mismatch")
MAX_CONTROL_LOG_BYTES = 8 * 1024 * 1024


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--launcher", required=True, type=Path)
    parser.add_argument("--logs", required=True, type=Path)
    parser.add_argument("--work-root", type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    launcher = args.launcher.resolve(strict=True)
    if not launcher.is_file() or not os.access(launcher, os.X_OK):
        parser.error("--launcher must name an executable regular file")
    root = Path(__file__).resolve().parent
    expected = json.loads((root / "expected.json").read_text())
    if tuple(expected) != CASES:
        parser.error("expected.json must name the four fixed controls in order")
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    work_root = (args.work_root or logs / "work").resolve()
    work_root.mkdir(parents=True, exist_ok=True)
    report = {
        "schema_version": 1,
        "scope": "Four semantic controls, not the RH proof or an isolation attestation",
        "comparator_source_commit": "c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809",
        "exporter_source_commit": "15f6055e299ad5b89345e533cc2192f4cc00f659",
        "lean_toolchain": "leanprover/lean4:v4.33.1",
        "launcher": str(launcher),
        "launcher_sha256": hashlib.sha256(launcher.read_bytes()).hexdigest(),
        "started_at_unix": time.time(),
        "controls": [],
    }
    for case in CASES:
        source = root / "projects" / case
        work = Path(tempfile.mkdtemp(prefix=f"{case}-", dir=work_root))
        hashes = {}
        for name in FILES:
            original = source / name
            if original.is_symlink() or not original.is_file():
                raise RuntimeError(f"Control input is not a regular file: {original}")
            body = original.read_bytes()
            (work / name).write_bytes(body)
            hashes[name] = hashlib.sha256(body).hexdigest()
        log = logs / f"{case}.log"
        launch_log = logs / f"{case}.launcher.log"
        if log.exists() or launch_log.exists():
            raise RuntimeError(f"Use a fresh evidence directory; log already exists for {case}")
        started = time.monotonic()
        timed_out = False
        with launch_log.open("wb") as launcher_output:
            proc = subprocess.Popen(
                [str(launcher), str(work), str(work / "comparator.json"), str(log)],
                stdout=launcher_output, stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            try:
                code = proc.wait(timeout=args.timeout_seconds)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    code = proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    code = proc.wait()
        issues = []
        output = ""
        if timed_out:
            issues.append("launcher/control timed out")
        if not log.is_file():
            issues.append("launcher did not preserve a Comparator log")
        elif log.stat().st_size > MAX_CONTROL_LOG_BYTES:
            issues.append("control log exceeded 8 MiB; retained on disk, not parsed")
        else:
            output = log.read_text(encoding="utf-8", errors="replace")
        if code != expected[case]["exit_code"]:
            issues.append(f"exit {code}; expected {expected[case]['exit_code']}")
        for marker in expected[case]["required"]:
            if marker not in output:
                issues.append(f"missing expected upstream diagnostic: {marker}")
        if case != "positive" and "Your solution is okay!" in output:
            issues.append("negative control printed Comparator success")
        # A bootstrap, build, exporter, or sandbox failure is never a successful
        # negative control, even if a diagnostic was copied into an earlier log.
        if case != "positive" and "Child exited with" in output:
            issues.append("negative control failed in a child build/export/checker")
        result = {
            "name": case, "passed": not issues, "exit_code": code,
            "timed_out": timed_out, "elapsed_seconds": time.monotonic() - started,
            "input_sha256": hashes, "work_directory": str(work),
            "comparator_log": str(log), "launcher_log": str(launch_log),
            "issues": issues,
        }
        report["controls"].append(result)
        print(f"{case}: {'PASS' if result['passed'] else 'FAIL'} (exit {code})", flush=True)
        for issue in issues:
            print(f"  {issue}", flush=True)
        (logs / "controls-report.json").write_text(json.dumps(report, indent=2) + "\n")
    report["passed"] = all(item["passed"] for item in report["controls"])
    report["finished_at_unix"] = time.time()
    (logs / "controls-report.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
