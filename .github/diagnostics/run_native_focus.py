#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# SPDX-FileCopyrightText: 2026 Krema Contributors
"""Run the finite native focus diagnostic cohort inside the historical image tag.

The source mount stays read-only. Only the diagnostic fixture/header are copied
onto a writable source copy; CMake, all production sources and CTest selection
stay unchanged. Configure/build logs precede tracing; runtime console streams
are discarded. The fixture wrapper owns typed, bounded failure detail; exported
JUnit owns test identities, outcomes and durations, not arbitrary captured output.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import xml.etree.ElementTree as ET


SOURCE_BASE = "28717c0809f6ea0e46505ec801efde2f6087e847"
IMAGE_TAG = "ghcr.io/isac322/krema-ci:ctest-fedora-43-079cb5b8d969"
EXPECTED_TESTS = 70


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_quiet(
    command: list[str], *, env: dict[str, str], cwd: Path, log: Path | None = None,
) -> int:
    # Configure/build logs are safe before tracing, with WAYLAND_DEBUG absent.
    # Runtime console output is discarded: only the fixture's typed, sanitizing
    # wrapper may retain native failure detail.
    with (log or Path(os.devnull)).open("wb") as output:
        return subprocess.run(
            command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
            stdout=output, stderr=output, check=False,
        ).returncode


def package_versions(env: dict[str, str]) -> list[dict[str, str]]:
    result = subprocess.run(
        ["rpm", "-qa", "--qf", "%{NAME}\t%{VERSION}-%{RELEASE}.%{ARCH}\n"],
        env=env, capture_output=True, text=True, check=True,
    )
    packages = []
    for line in result.stdout.splitlines():
        name, separator, version = line.partition("\t")
        if (separator and re.fullmatch(r"[A-Za-z0-9_.+~-]+", name)
                and re.fullmatch(r"[A-Za-z0-9_.+:~^-]+", version)
                and re.match(r"^(kwin|qt6|kf6-kio|wayland|libwayland|layer-shell-qt|layershellqt|plasma-wayland-protocols)(?:-|$)", name)):
            packages.append({"name": name, "version": version})
    return sorted(packages, key=lambda package: package["name"])


def test_name(value: str) -> str:
    # CTest names come from the immutable CMake test registry, including the
    # existing "panels' band" case. Reject protocol syntax and control characters.
    if re.fullmatch(r"[A-Za-z0-9_ .:/()=+,'-]{1,400}", value):
        return value
    raise ValueError("unrecognized JUnit test identity")


def export_junit(raw: Path, destination: Path) -> dict[str, object]:
    counts = {"total": 0, "passed": 0, "failed": 0, "skipped": 0}
    failed_names: list[str] = []
    skipped_names: list[str] = []
    suite = ET.Element("testsuite", name="native-focus-full-suite")
    for original in ET.parse(raw).getroot().iter("testcase"):
        name = test_name(original.get("name", ""))
        attributes = {"name": name}
        duration = original.get("time", "")
        if re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", duration):
            attributes["time"] = duration
        case = ET.SubElement(suite, "testcase", attributes)
        counts["total"] += 1
        if original.find("failure") is not None or original.find("error") is not None:
            counts["failed"] += 1
            failed_names.append(name)
            ET.SubElement(case, "failure", message="CTest reported failure; see typed focus trace if applicable")
        elif original.find("skipped") is not None:
            counts["skipped"] += 1
            skipped_names.append(name)
            ET.SubElement(case, "skipped", message="CTest reported skipped/not-run")
        else:
            counts["passed"] += 1
    suite.set("tests", str(counts["total"]))
    suite.set("failures", str(counts["failed"]))
    suite.set("skipped", str(counts["skipped"]))
    ET.ElementTree(suite).write(destination, encoding="utf-8", xml_declaration=True)
    return {**counts, "failed_names": failed_names, "skipped_names": skipped_names}


def fixture_observer_health(prefix: Path, mode: str) -> dict[str, object]:
    result: dict[str, object] = {"diagnostic_valid": False}
    summary_path = Path(str(prefix) + ".summary.json")
    result["fixture_summary_present"] = summary_path.is_file()
    if not summary_path.is_file():
        result["diagnostic_invalid_reasons"] = ["fixture-summary-missing"]
        return result
    try:
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        result["diagnostic_invalid_reasons"] = ["fixture-summary-unreadable"]
        return result
    if not isinstance(summary, dict):
        result["diagnostic_invalid_reasons"] = ["fixture-summary-invalid-schema"]
        return result
    reasons = []
    returncode = summary.get("returncode")
    if (summary.get("schema_version") != 1 or summary.get("mode") != mode
            or type(returncode) is not int):
        reasons.append("fixture-summary-invalid-schema")
    else:
        result["fixture_returncode"] = returncode
        result["fixture_signal"] = -returncode if returncode < 0 else None
    if summary.get("supervisor_error") is not False:
        reasons.append("fixture-supervisor-error")
    if "launch_errno" not in summary or summary["launch_errno"] is not None:
        reasons.append("fixture-launch-error")
    interrupted = summary.get("interrupted")
    result["fixture_interrupted"] = interrupted if type(interrupted) is int else None
    if type(interrupted) is not int or interrupted != 0:
        reasons.append("fixture-observer-interrupted-or-invalid")
    # A failed fixture can legitimately fail before post-gesture events arrive:
    # retain its evidence without rejecting it for the very absence under study.
    health_required = mode == "on" and type(returncode) is int and returncode == 0
    result["native_observer_health_required"] = health_required
    if health_required:
        native = summary.get("native_event_counts", {})
        after = summary.get("native_events_after_first_fake_input_button", {})
        native = native if isinstance(native, dict) else {}
        after = after if isinstance(after, dict) else {}
        button_count = native.get("org_kde_kwin_fake_input.button", 0)
        button_count = button_count if type(button_count) is int else 0
        first_button = summary.get("first_fake_input_button_seq")
        result["native_fake_input_button_count"] = button_count
        result["native_first_fake_input_button_seq"] = (
            first_button if type(first_button) is int else None
        )
        if button_count < 1 or type(first_button) is not int or first_button < 1:
            reasons.append("no-typed-fake-input-button")
        for interface in ("wl_keyboard", "wl_pointer"):
            count = sum(value for key, value in after.items()
                        if isinstance(key, str) and key.startswith(interface + ".")
                        and type(value) is int and value > 0)
            result[f"native_{interface}_events_after_first_button"] = count
            if count < 1:
                reasons.append(f"no-{interface}-events-after-first-fake-button")
    result["diagnostic_invalid_reasons"] = reasons
    result["diagnostic_valid"] = not reasons
    return result


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path("/src"))
    parser.add_argument("--work", type=Path, default=Path("/work"))
    parser.add_argument("--build", type=Path, default=Path("/tmp/build"))
    parser.add_argument("--results", type=Path, default=Path("/results"))
    parser.add_argument("--baseline-runs", type=int, default=3)
    parser.add_argument("--off-runs", type=int, default=6)
    parser.add_argument("--on-runs", type=int, default=3)
    args = parser.parse_args()
    if min(args.baseline_runs, args.off_runs, args.on_runs) < 0 or args.baseline_runs + args.off_runs + args.on_runs == 0:
        parser.error("cohort counts must be nonnegative with at least one run")
    for name in ("source", "work", "build", "results"):
        setattr(args, name, getattr(args, name).resolve())
    paths = [args.source, args.work, args.build, args.results]
    if any(left == right or left in right.parents or right in left.parents
           for index, left in enumerate(paths) for right in paths[index + 1:]):
        parser.error("source, work, build and results paths must not overlap")
    return args


def main() -> int:
    args = arguments()
    args.results.mkdir(parents=True, exist_ok=True)
    if any(args.results.iterdir()):
        print("native focus diagnostic: results directory must be empty", file=sys.stderr)
        return 1
    env = os.environ.copy()
    for key in ("WAYLAND_DEBUG", "KREMA_FOCUS_TRACE_MODE", "KREMA_FOCUS_TRACE_OUTPUT",
                "KREMA_FOCUS_BASELINE_CAPTURE"):
        env.pop(key, None)
    metadata: dict[str, object] = {
        "started_at": utc_now(), "source_base_commit": SOURCE_BASE,
        "diagnostic_commit": os.environ.get("KREMA_DIAGNOSTIC_COMMIT", "not-recorded"),
        "image_tag": IMAGE_TAG,
        "resolved_image_digest": os.environ.get("KREMA_IMAGE_DIGEST", "not-recorded"),
        "historical_run_id": "39904941810",
        "historical_image_digest_known": False,
        "image_limit": "The historical log recorded only the tag; this resolved digest is not proof of identical historical image contents.",
        "runner_arch": os.uname().machine,
        "observer_limit": "A passing traced run does not refute the native failure; zero Qt counts are inconclusive.",
        "baseline_evidence_limit": "Original CPP has no observer. The mode-off sanitizer starts before scratch/KWin startup, not between KWin readiness and fixture execution; this can still shift global workload timing. Baseline retains only allowlisted output and no native protocol events.",
        "cohort": {"baseline": args.baseline_runs, "off": args.off_runs, "on": args.on_runs},
        "expected_test_count": EXPECTED_TESTS,
        "runs": [], "phases": [], "overall_exit_code": 1,
    }
    summary_path = args.results / "cohort.summary.json"
    write_json(summary_path, metadata)
    overall = 0
    try:
        args.work.mkdir(parents=True, exist_ok=True)
        args.build.mkdir(parents=True, exist_ok=True)
        processors = int(subprocess.check_output(["nproc"], env=env, text=True).strip())
        metadata["nproc"] = processors
        metadata["installed_packages"] = package_versions(env)
        # Exclude both directory- and file-form .git (worktree .git is a file).
        # Do not mutate the read-only source or patch any source text at runtime.
        phases = [
            ("source-copy", ["rsync", "-a", "--exclude", "/.git", "--exclude", "/.ccache",
                             str(args.source) + "/", str(args.work) + "/"]),
        ]
        for name, command in phases:
            status = run_quiet(command, env=env, cwd=args.work)
            metadata["phases"].append({"name": name, "exit_code": status})
            if status:
                return 1
        # Copy the pinned original CPP explicitly before the first full build.
        # copyfile refreshes mtime even in a parent's reused smoke build tree,
        # so a previously instrumented object cannot masquerade as baseline.
        original_cpp = args.source / "tests/kwin/test_launch_in_place.cpp"
        metadata["baseline_cpp_sha256"] = hashlib.sha256(original_cpp.read_bytes()).hexdigest()
        shutil.copyfile(original_cpp, args.work / "tests/kwin/test_launch_in_place.cpp")
        commands = [
            ("configure", ["cmake", "-S", str(args.work), "-B", str(args.build), "-G", "Ninja",
                           "-DCMAKE_BUILD_TYPE=RelWithDebInfo", "-DBUILD_TESTING=ON",
                           "-DCMAKE_C_COMPILER_LAUNCHER=ccache", "-DCMAKE_CXX_COMPILER_LAUNCHER=ccache"]),
            ("build", ["cmake", "--build", str(args.build)]),
        ]
        for name, command in commands:
            started = time.monotonic()
            log = args.results / f"{name}.log"
            status = run_quiet(command, env=env, cwd=args.work, log=log)
            metadata["phases"].append({"name": name, "exit_code": status, "log": log.name,
                                       "elapsed_seconds": round(time.monotonic() - started, 3)})
            write_json(summary_path, metadata)
            print(f"native focus diagnostic: {name} exit={status}", flush=True)
            if status:
                return 1
        def execute_suite(mode: str) -> None:
            nonlocal overall
            index = len(metadata["runs"]) + 1
            baseline = mode == "baseline"
            prefix = args.results / f"run{index:02d}-{mode}"
            raw_junit = args.build / f"native-focus-run{index:02d}.xml"
            run_env = env.copy()
            if baseline:
                run_env.update({"KREMA_FOCUS_BASELINE_CAPTURE": "1",
                                "KREMA_FOCUS_TRACE_OUTPUT": str(prefix)})
                run_env.pop("KREMA_FOCUS_TRACE_MODE", None)
            else:
                run_env.pop("KREMA_FOCUS_BASELINE_CAPTURE", None)
                run_env.update({"KREMA_FOCUS_TRACE_MODE": mode,
                                "KREMA_FOCUS_TRACE_OUTPUT": str(prefix)})
            # Archive rather than delete owned scheduler data, so each member
            # starts with fresh costs while retaining the prior observations.
            for filename in ("CTestCostData.txt", "LastTestsFailed.log"):
                scheduler_file = args.build / "Testing/Temporary" / filename
                if scheduler_file.exists():
                    shutil.move(scheduler_file, Path(str(prefix) + f".{filename}.scheduler.txt"))
            command = ["ctest", "--test-dir", str(args.build), "-LE", "e2e",
                       "--output-on-failure", "--no-tests=error", f"-j{processors}",
                       "--output-junit", str(raw_junit)]
            # Baseline sanitizes the whole wrapper before scratch/KWin startup.
            # Its nested wrapper executes the original CPP directly after KWin
            # readiness, avoiding instrumentation or a new pre-gesture process.
            record: dict[str, object] = {
                "index": index, "mode": mode, "started_at": utc_now(),
                "command": command,
                "trace_prefix": str(prefix), "fresh_cost": True,
                "summary_source": "wrapper-pre-session-observer" if baseline else "fixture-observer",
                "observer_returncode_kind": "wrapper-exit" if baseline else "fixture-exit",
                "fixture_wrapper_mode_set": not baseline,
                "baseline_capture_set": baseline, "diagnostic_valid": False,
            }
            started = time.monotonic()
            try:
                status = run_quiet(command, env=run_env, cwd=args.work)
                record["ctest_exit_code"] = status
                health = fixture_observer_health(prefix, "off" if baseline else mode)
                if baseline:
                    health = {
                        key.replace("fixture_", "wrapper_", 1) if key.startswith("fixture_") else key: value
                        for key, value in health.items()
                    }
                record.update(health)
                observer_returncode = record.get(
                    "wrapper_returncode" if baseline else "fixture_returncode"
                )
                counts = export_junit(raw_junit, Path(str(prefix) + ".junit.xml"))
                record["junit"] = counts
                passed = (status == 0 and record["ctest_exit_code"] == 0
                          and counts["total"] == EXPECTED_TESTS and counts["failed"] == 0
                          and counts["skipped"] == 0 and record["diagnostic_valid"]
                          and observer_returncode == 0)
                record["passed"] = passed
                if not passed:
                    overall = 1
            except (OSError, ValueError, ET.ParseError, subprocess.SubprocessError) as error:
                # Never print exception text: an XML parse error can quote input.
                record["harness_error_type"] = type(error).__name__
                record["passed"] = False
                overall = 1
            finally:
                raw_junit.unlink(missing_ok=True)
                record["elapsed_seconds"] = round(time.monotonic() - started, 3)
                metadata["runs"].append(record)
                write_json(Path(str(prefix) + ".run.summary.json"), record)
                write_json(summary_path, metadata)
                print(f"native focus diagnostic: run={index} mode={mode} passed={record['passed']}", flush=True)

        for _ in range(args.baseline_runs):
            execute_suite("baseline")
        payloads = {
            "focus-failure-diagnostic.cpp": "test_launch_in_place.cpp",
            "focus-failure-fakepointer.h": "focus-failure-fakepointer.h",
        }
        metadata["payload_sha256"] = {}
        for payload, target in payloads.items():
            source = args.work / ".github/diagnostics" / payload
            metadata["payload_sha256"][payload] = hashlib.sha256(source.read_bytes()).hexdigest()
            shutil.copyfile(source, args.work / "tests/kwin" / target)
        command = ["cmake", "--build", str(args.build), "--target", "krema_launch_in_place_tests"]
        started = time.monotonic()
        status = run_quiet(command, env=env, cwd=args.work, log=args.results / "diagnostic-build.log")
        metadata["phases"].append({"name": "diagnostic-build", "exit_code": status,
                                   "log": "diagnostic-build.log",
                                   "elapsed_seconds": round(time.monotonic() - started, 3)})
        write_json(summary_path, metadata)
        print(f"native focus diagnostic: diagnostic-build exit={status}", flush=True)
        if status:
            overall = 1
            return 1
        for mode in ["off"] * args.off_runs + ["on"] * args.on_runs:
            execute_suite(mode)
        metadata["all_cohort_members_completed"] = len(metadata["runs"]) == args.baseline_runs + args.off_runs + args.on_runs
        return overall
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        metadata["harness_error_type"] = type(error).__name__
        overall = 1
        return 1
    finally:
        # Early configure/build returns are failures even before cohort execution.
        complete = len(metadata["runs"]) == args.baseline_runs + args.off_runs + args.on_runs
        metadata["overall_exit_code"] = overall if complete else 1
        metadata["finished_at"] = utc_now()
        write_json(summary_path, metadata)


if __name__ == "__main__":
    sys.exit(main())
