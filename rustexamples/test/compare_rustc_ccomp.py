#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parents[2]
TEST_ROOT = Path(__file__).resolve().parent
CCOMP = REPO_ROOT / "ccomp"
DEFAULT_RUSTC_COMMAND = ["rustup", "run", "nightly", "rustc"]
DEFAULT_POLONIUS_MODE = "next"


@dataclass
class CompileResult:
    ok: bool
    returncode: int
    message: str
    summary: str
    category: str
    command: list[str]


@dataclass
class TestResult:
    test: str
    ccomp: CompileResult
    rustc: CompileResult
    outcome: str
    note: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare rustc and ccomp on rustexamples/test cases."
    )
    parser.add_argument(
        "--report",
        default=str(TEST_ROOT / "rustc_ccomp_comparison.md"),
        help="Where to write the markdown report.",
    )
    parser.add_argument(
        "--json",
        default=str(TEST_ROOT / "rustc_ccomp_comparison.json"),
        help="Where to write the JSON result dump.",
    )
    parser.add_argument(
        "--rustc-command",
        nargs="+",
        default=DEFAULT_RUSTC_COMMAND,
        help="Rust compiler command prefix, for example: rustup run nightly rustc",
    )
    parser.add_argument(
        "--polonius",
        default=DEFAULT_POLONIUS_MODE,
        help="Value passed to -Z polonius=<mode>.",
    )
    parser.add_argument(
        "--ccomp",
        default=str(CCOMP),
        help="Path to ccomp.",
    )
    return parser.parse_args()


def list_tests() -> list[Path]:
    tests = sorted(p for p in TEST_ROOT.rglob("*.rs") if p.name != ".DS_Store")
    return tests


def run_command(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(
        list(cmd),
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=60,
    )
    output = (proc.stdout or "") + (proc.stderr or "")
    return proc.returncode, output.strip()


def normalize_message(text: str) -> str:
    text = text.replace("\r\n", "\n").replace("\r", "\n").strip()
    lines = [line.rstrip() for line in text.splitlines()]
    return "\n".join(lines).strip()


def first_interesting_line(text: str) -> str:
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if "error" in stripped.lower():
            return stripped
    for line in text.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped
    return "(no diagnostic text)"


def classify_message(text: str) -> str:
    lower = text.lower()
    categories = [
        ("syntax", [r"syntax", r"expected", r"unexpected", r"parse", r"macro"]),
        ("borrow", [r"\bborrow", r"borrowed", r"reborrow"]),
        ("lifetime", [r"lifetime", r"does not live long enough", r"dangl", r"return.*reference"]),
        ("move", [r"\bmoved", r"use of moved", r"move out", r"after move"]),
        ("mutability", [r"cannot assign", r"immutable", r"mutable", r"mutably"]),
        ("type", [r"type mismatch", r"mismatched types", r"expected .* found", r"not found in this scope"]),
        ("unsupported", [r"unsupported", r"not support"]),
        ("pattern", [r"pattern", r"constructor", r"match"]),
    ]
    for category, patterns in categories:
        if any(re.search(pattern, lower) for pattern in patterns):
            return category
    return "other"


def compare_error_messages(ccomp: CompileResult, rustc: CompileResult) -> str:
    if ccomp.category == rustc.category and ccomp.category != "other":
        return f"Both reject it for roughly the same reason ({ccomp.category})."
    return "Both reject it, but the diagnostics look different."


def mismatch_note(ccomp: CompileResult, rustc: CompileResult) -> str:
    if ccomp.ok and not rustc.ok:
        if rustc.category == "syntax":
            return "ccomp accepts it, but rustc rejects the source as non-standard Rust syntax."
        return "ccomp accepts it, but rustc rejects it."
    if rustc.ok and not ccomp.ok:
        if ccomp.category == "unsupported":
            return "rustc accepts it; ccomp rejects it due to an unsupported feature."
        return "rustc accepts it, but ccomp rejects it."
    return ""


def crate_name_for(test: Path) -> str:
    base = str(test.relative_to(TEST_ROOT).with_suffix(""))
    base = re.sub(r"[^A-Za-z0-9_]", "_", base)
    base = re.sub(r"_+", "_", base).strip("_")
    if not base:
        base = "compare_test"
    if base[0].isdigit():
        base = "test_" + base
    return base


def compile_with_ccomp(test: Path, ccomp_path: str) -> CompileResult:
    with tempfile.TemporaryDirectory(prefix="ccomp-compare-") as tmp:
        tmpdir = Path(tmp)
        output = tmpdir / (test.stem + ".s")
        cmd = [ccomp_path, "-dclight", "-S", str(test)]
        cmd.extend(["-o", str(output)])
        returncode, message = run_command(cmd, tmpdir)
    normalized = normalize_message(message)
    return CompileResult(
        ok=returncode == 0,
        returncode=returncode,
        message=normalized,
        summary=first_interesting_line(normalized),
        category=classify_message(normalized),
        command=list(cmd),
    )


def compile_with_rustc(
    test: Path, rustc_command: Sequence[str], polonius_mode: str
) -> CompileResult:
    with tempfile.TemporaryDirectory(prefix="rustc-compare-") as tmp:
        tmpdir = Path(tmp)
        output = tmpdir / (test.stem + ".rmeta")
        cmd = list(rustc_command) + [
            "--edition=2021",
            f"-Zpolonius={polonius_mode}",
            "--crate-name",
            crate_name_for(test),
            "--emit=metadata",
            str(test),
            "-o",
            str(output),
        ]
        returncode, message = run_command(cmd, tmpdir)
    normalized = normalize_message(message)
    return CompileResult(
        ok=returncode == 0,
        returncode=returncode,
        message=normalized,
        summary=first_interesting_line(normalized),
        category=classify_message(normalized),
        command=list(cmd),
    )


def compare_test(
    test: Path, rustc_command: Sequence[str], polonius_mode: str, ccomp_path: str
) -> TestResult:
    ccomp = compile_with_ccomp(test, ccomp_path)
    rustc = compile_with_rustc(test, rustc_command, polonius_mode)
    if ccomp.ok and rustc.ok:
        return TestResult(
            test=str(test.relative_to(TEST_ROOT)),
            ccomp=ccomp,
            rustc=rustc,
            outcome="ok",
            note="Both compilers accept the test.",
        )
    if ccomp.ok != rustc.ok:
        return TestResult(
            test=str(test.relative_to(TEST_ROOT)),
            ccomp=ccomp,
            rustc=rustc,
            outcome="different",
            note=mismatch_note(ccomp, rustc),
        )
    return TestResult(
        test=str(test.relative_to(TEST_ROOT)),
        ccomp=ccomp,
        rustc=rustc,
        outcome="both_error",
        note=compare_error_messages(ccomp, rustc),
    )


def markdown_escape(text: str) -> str:
    return text.replace("|", "\\|")


def summarize(results: list[TestResult]) -> dict[str, int]:
    counts = {"ok": 0, "different": 0, "both_error": 0}
    for result in results:
        counts[result.outcome] += 1
    return counts


def format_report(
    results: list[TestResult],
    rustc_command: Sequence[str],
    polonius_mode: str,
    ccomp_path: str,
    rustc_version: str,
) -> str:
    counts = summarize(results)
    lines: list[str] = []
    lines.append("# rustc vs ccomp comparison")
    lines.append("")
    lines.append("## Setup")
    lines.append("")
    lines.append(f"- Test root: `{TEST_ROOT}`")
    lines.append(f"- `rustc` command: `{' '.join(rustc_command)}`")
    lines.append(f"- `rustc --version`: `{rustc_version}`")
    lines.append(f"- Polonius mode: `-Z polonius={polonius_mode}`")
    lines.append(f"- `ccomp`: `{ccomp_path}`")
    lines.append("- `rustc` is run with `--edition=2021 -Z polonius=... --emit=metadata` to compare front-end acceptance without linker noise.")
    lines.append("- `ccomp` is run with `-dclight -S` for the same reason.")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- Total tests: `{len(results)}`")
    lines.append(f"- Both accept: `{counts['ok']}`")
    lines.append(f"- Different result: `{counts['different']}`")
    lines.append(f"- Both reject: `{counts['both_error']}`")
    lines.append("")
    lines.append("## Per-test Summary")
    lines.append("")
    lines.append("| Test | Outcome | ccomp | rustc | Note |")
    lines.append("| --- | --- | --- | --- | --- |")
    for result in results:
        ccomp_status = "ok" if result.ccomp.ok else f"error: {markdown_escape(result.ccomp.summary)}"
        rustc_status = "ok" if result.rustc.ok else f"error: {markdown_escape(result.rustc.summary)}"
        lines.append(
            f"| `{result.test}` | `{result.outcome}` | {ccomp_status} | {rustc_status} | {markdown_escape(result.note)} |"
        )
    lines.append("")
    lines.append("## Detailed Results")
    lines.append("")
    for result in results:
        lines.append(f"### `{result.test}`")
        lines.append("")
        lines.append(f"- Outcome: `{result.outcome}`")
        lines.append(f"- Note: {result.note}")
        lines.append(f"- ccomp: `{'ok' if result.ccomp.ok else 'error'}`")
        if result.ccomp.message:
            lines.append("```text")
            lines.append(result.ccomp.message)
            lines.append("```")
        lines.append(f"- rustc: `{'ok' if result.rustc.ok else 'error'}`")
        if result.rustc.message:
            lines.append("```text")
            lines.append(result.rustc.message)
            lines.append("```")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    rustc_version = subprocess.run(
        list(args.rustc_command) + ["--version"],
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    if not Path(args.ccomp).exists():
        raise SystemExit(f"ccomp not found at {args.ccomp}")

    results = [
        compare_test(test, args.rustc_command, args.polonius, args.ccomp)
        for test in list_tests()
    ]

    report_path = Path(args.report)
    report_path.write_text(
        format_report(results, args.rustc_command, args.polonius, args.ccomp, rustc_version),
        encoding="utf-8",
    )

    json_path = Path(args.json)
    json_path.write_text(
        json.dumps([asdict(result) for result in results], indent=2),
        encoding="utf-8",
    )

    counts = summarize(results)
    print(
        f"Compared {len(results)} tests: "
        f"{counts['ok']} both ok, "
        f"{counts['different']} different, "
        f"{counts['both_error']} both error."
    )
    print(f"Report: {report_path}")
    print(f"JSON: {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
