#!/usr/bin/env python3
import argparse
import json
import os
import shlex
import subprocess
import sys
import textwrap
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


DEFAULT_GCC_FLAGS = ["-O2", "-Wno-return-type", "-Wno-implicit-int"]
DEFAULT_GCC_LIBS = ["-lm"]
DEFAULT_RUST_FLAGS = ["-O", "--cap-lints=allow"]


@dataclass
class CommandResult:
    ok: bool
    stdout: str
    stderr: str
    returncode: int
    duration: float
    timed_out: bool = False


@dataclass
class TestCase:
    name: str
    args: List[str] = field(default_factory=list)
    stdin: str = ""
    timeout: float = 5.0


@dataclass
class DiffOutcome:
    ok: bool
    case: Optional[TestCase]
    detail: str
    c_stdout: str = ""
    rust_stdout: str = ""
    c_stderr: str = ""
    rust_stderr: str = ""
    c_exit: int = 0
    rust_exit: int = 0


def shell_quote(value: Path) -> str:
    return shlex.quote(str(value))


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def parse_env_file(path: Path) -> Dict[str, str]:
    env: Dict[str, str] = {}
    if not path.exists():
        return env
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()
        if not key:
            continue
        if len(value) >= 2 and ((value[0] == value[-1]) and value[0] in {"'", '"'}):
            value = value[1:-1]
        env[key] = value
    return env


def run_command(
    command: Sequence[str],
    *,
    cwd: Optional[Path] = None,
    timeout: Optional[float] = None,
    env: Optional[Dict[str, str]] = None,
) -> CommandResult:
    start = time.time()
    try:
        completed = subprocess.run(
            list(command),
            cwd=str(cwd) if cwd is not None else None,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
        )
        return CommandResult(
            ok=completed.returncode == 0,
            stdout=completed.stdout,
            stderr=completed.stderr,
            returncode=completed.returncode,
            duration=time.time() - start,
        )
    except subprocess.TimeoutExpired as exc:
        return CommandResult(
            ok=False,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "TIMEOUT",
            returncode=124,
            duration=time.time() - start,
            timed_out=True,
        )


def run_shell(
    command: str,
    *,
    cwd: Optional[Path] = None,
    timeout: Optional[float] = None,
    env: Optional[Dict[str, str]] = None,
) -> CommandResult:
    return run_command(["bash", "-lc", command], cwd=cwd, timeout=timeout, env=env)


def compact_output(text: str, limit: int = 4000) -> str:
    text = text.strip()
    if len(text) <= limit:
        return text
    return text[:limit] + "\n...[truncated]..."


def find_generated_rust_file(workdir: Path, c_file: Path) -> Path:
    return workdir / f"{c_file.stem}.rs"


def translate_c_to_rust(ccomp: Path, c_file: Path, workdir: Path, timeout: float) -> Tuple[bool, Path, CommandResult]:
    rust_file = find_generated_rust_file(workdir, c_file)
    if rust_file.exists():
        rust_file.unlink()
    result = run_command([str(ccomp), str(c_file), "-drustlight"], cwd=workdir, timeout=timeout)
    return rust_file.exists(), rust_file, result


def compile_c(
    cc: str,
    c_file: Path,
    output: Path,
    cflags: Sequence[str],
    clibs: Sequence[str],
    timeout: float,
) -> CommandResult:
    cmd = [cc] + list(cflags) + [str(c_file), "-o", str(output)] + list(clibs)
    return run_command(cmd, timeout=timeout)


def compile_rust(rustc: str, rust_file: Path, output: Path, rust_flags: Sequence[str], timeout: float) -> CommandResult:
    cmd = [rustc] + list(rust_flags) + [str(rust_file), "-o", str(output)]
    return run_command(cmd, timeout=timeout)


def run_program(binary: Path, case: TestCase) -> CommandResult:
    start = time.time()
    try:
        completed = subprocess.run(
            [str(binary)] + case.args,
            input=case.stdin,
            capture_output=True,
            text=True,
            timeout=case.timeout,
        )
        return CommandResult(
            ok=completed.returncode == 0,
            stdout=completed.stdout,
            stderr=completed.stderr,
            returncode=completed.returncode,
            duration=time.time() - start,
        )
    except subprocess.TimeoutExpired as exc:
        return CommandResult(
            ok=False,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "TIMEOUT",
            returncode=124,
            duration=time.time() - start,
            timed_out=True,
        )


def outputs_equal(a: str, b: str) -> bool:
    return a == b


def parse_test_cases(path: Path, default_timeout: float) -> List[TestCase]:
    try:
        raw = json.loads(read_text(path))
    except Exception:
        return [TestCase(name="default", timeout=default_timeout)]

    cases = raw.get("cases", [])
    if not isinstance(cases, list) or not cases:
        return [TestCase(name="default", timeout=default_timeout)]

    parsed: List[TestCase] = []
    for idx, case in enumerate(cases):
        if not isinstance(case, dict):
            continue
        name = str(case.get("name", f"case_{idx}"))
        args = case.get("args", [])
        stdin = case.get("stdin", "")
        timeout = case.get("timeout", default_timeout)
        if not isinstance(args, list):
            args = []
        parsed.append(
            TestCase(
                name=name,
                args=[str(arg) for arg in args],
                stdin=str(stdin),
                timeout=float(timeout),
            )
        )
    return parsed or [TestCase(name="default", timeout=default_timeout)]


def write_default_test_spec(path: Path, timeout: float) -> None:
    payload = {
        "cases": [
            {
                "name": "default",
                "args": [],
                "stdin": "",
                "timeout": timeout,
            }
        ]
    }
    write_text(path, json.dumps(payload, indent=2, ensure_ascii=True) + "\n")


class LLMCommandBackend:
    def __init__(self, command_template: Optional[str], timeout: float, env: Optional[Dict[str, str]] = None):
        self.command_template = command_template
        self.timeout = timeout
        self.env = env

    def enabled(self) -> bool:
        return bool(self.command_template)

    def invoke(
        self,
        *,
        phase: str,
        workspace: Path,
        prompt_file: Path,
        c_file: Path,
        rust_file: Path,
        test_spec_file: Path,
        target_files: Sequence[Path],
        extra: Optional[Dict[str, str]] = None,
    ) -> CommandResult:
        if not self.command_template:
            return CommandResult(
                ok=False,
                stdout="",
                stderr="No LLM command template configured.",
                returncode=2,
                duration=0.0,
            )
        ctx: Dict[str, str] = {
            "phase": shlex.quote(phase),
            "workspace": shell_quote(workspace),
            "prompt_file": shell_quote(prompt_file),
            "c_file": shell_quote(c_file),
            "rust_file": shell_quote(rust_file),
            "test_spec_file": shell_quote(test_spec_file),
            "target_files": " ".join(shell_quote(path) for path in target_files),
        }
        if extra:
            for key, value in extra.items():
                ctx[key] = shlex.quote(value)
        command = self.command_template.format(**ctx)
        return run_shell(command, cwd=workspace, timeout=self.timeout, env=self.env)


class AiderBackend:
    def __init__(
        self,
        *,
        aider_command: str,
        model: str,
        timeout: float,
        extra_args: Sequence[str],
        env: Optional[Dict[str, str]] = None,
        env_file: Optional[Path] = None,
    ):
        self.aider_command = aider_command
        self.model = model
        self.timeout = timeout
        self.extra_args = list(extra_args)
        self.env = env
        self.env_file = env_file

    def enabled(self) -> bool:
        return bool(self.model)

    def invoke(
        self,
        *,
        phase: str,
        workspace: Path,
        prompt_file: Path,
        c_file: Path,
        rust_file: Path,
        test_spec_file: Path,
        target_files: Sequence[Path],
        extra: Optional[Dict[str, str]] = None,
    ) -> CommandResult:
        if not self.enabled():
            return CommandResult(
                ok=False,
                stdout="",
                stderr="Aider backend requires --aider-model.",
                returncode=2,
                duration=0.0,
            )

        command = [
            self.aider_command,
            "--model",
            self.model,
            "--yes",
            "--no-auto-commits",
            "--no-dirty-commits",
            "--message-file",
            str(prompt_file),
        ]
        if self.env_file is not None and self.env_file.exists():
            command.extend(["--env-file", str(self.env_file)])
        command.extend(self.extra_args)
        command.extend(str(path) for path in target_files)
        return run_command(command, cwd=workspace, timeout=self.timeout, env=self.env)


def build_compile_repair_prompt(c_file: Path, rust_file: Path, compile_result: CommandResult) -> str:
    return textwrap.dedent(
        f"""
        你现在负责修复一次 C->Rust 转换后生成的 Rust 代码，使其能够通过 rustc 编译。

        目标约束：
        1. 优先只修改生成的 Rust 文件。
        2. 尽量保持与原始 C 程序语义一致，不要为了通过编译随意删除逻辑。
        3. 如果必须改动接口或包装，请保持改动最小。
        4. 不要输出解释文字，直接修改目标文件。

        原始 C 文件：
        {c_file}

        待修复 Rust 文件：
        {rust_file}

        当前 rustc 报错：
        {compact_output(compile_result.stderr)}
        """
    ).strip() + "\n"


def build_test_generation_prompt(c_file: Path, rust_file: Path, test_spec_file: Path, max_cases: int) -> str:
    schema = {
        "cases": [
            {
                "name": "default",
                "args": [],
                "stdin": "",
                "timeout": 5.0,
            }
        ]
    }
    return textwrap.dedent(
        f"""
        你现在负责为一个由 C 转换得到的 Rust 程序生成简单的差分测试用例。

        任务：
        1. 阅读原始 C 文件和当前 Rust 文件。
        2. 生成最多 {max_cases} 个简单测试用例。
        3. 只编辑测试规范文件，不要修改其它文件。
        4. 测试规范文件必须是合法 JSON，格式如下：

        {json.dumps(schema, indent=2, ensure_ascii=True)}

        说明：
        - args: 命令行参数数组
        - stdin: 传给程序标准输入的字符串
        - timeout: 单个测试用例超时时间（秒）
        - 如果程序看起来不依赖输入，至少保留一个默认空输入用例

        原始 C 文件：
        {c_file}

        当前 Rust 文件：
        {rust_file}

        只编辑这个文件：
        {test_spec_file}
        """
    ).strip() + "\n"


def build_mismatch_repair_prompt(
    c_file: Path,
    rust_file: Path,
    outcome: DiffOutcome,
) -> str:
    case = outcome.case or TestCase(name="unknown")
    return textwrap.dedent(
        f"""
        你现在负责修复一次 C->Rust 转换后生成的 Rust 代码，使其与原始 C 程序在差分测试中的行为一致。

        目标约束：
        1. 优先只修改生成的 Rust 文件。
        2. 保持程序语义尽量贴近原始 C。
        3. 不要删除主要逻辑，不要仅仅为了通过测试而硬编码输出。
        4. 不要输出解释文字，直接修改目标文件。

        原始 C 文件：
        {c_file}

        当前 Rust 文件：
        {rust_file}

        失败的测试用例：
        - name: {case.name}
        - args: {case.args}
        - stdin: {case.stdin!r}

        C 程序：
        - exit code: {outcome.c_exit}
        - stdout:
        {compact_output(outcome.c_stdout)}
        - stderr:
        {compact_output(outcome.c_stderr)}

        Rust 程序：
        - exit code: {outcome.rust_exit}
        - stdout:
        {compact_output(outcome.rust_stdout)}
        - stderr:
        {compact_output(outcome.rust_stderr)}

        不一致摘要：
        {outcome.detail}
        """
    ).strip() + "\n"


def run_diff_tests(c_bin: Path, rust_bin: Path, cases: Sequence[TestCase]) -> DiffOutcome:
    for case in cases:
        c_run = run_program(c_bin, case)
        rust_run = run_program(rust_bin, case)

        if c_run.returncode != rust_run.returncode:
            return DiffOutcome(
                ok=False,
                case=case,
                detail="exit code mismatch",
                c_stdout=c_run.stdout,
                rust_stdout=rust_run.stdout,
                c_stderr=c_run.stderr,
                rust_stderr=rust_run.stderr,
                c_exit=c_run.returncode,
                rust_exit=rust_run.returncode,
            )
        if not outputs_equal(c_run.stdout, rust_run.stdout):
            return DiffOutcome(
                ok=False,
                case=case,
                detail="stdout mismatch",
                c_stdout=c_run.stdout,
                rust_stdout=rust_run.stdout,
                c_stderr=c_run.stderr,
                rust_stderr=rust_run.stderr,
                c_exit=c_run.returncode,
                rust_exit=rust_run.returncode,
            )
        if not outputs_equal(c_run.stderr, rust_run.stderr):
            return DiffOutcome(
                ok=False,
                case=case,
                detail="stderr mismatch",
                c_stdout=c_run.stdout,
                rust_stdout=rust_run.stdout,
                c_stderr=c_run.stderr,
                rust_stderr=rust_run.stderr,
                c_exit=c_run.returncode,
                rust_exit=rust_run.returncode,
            )

    return DiffOutcome(ok=True, case=None, detail="all differential tests passed")


def run_compile_repair_loop(
    *,
    backend: LLMCommandBackend,
    c_file: Path,
    rust_file: Path,
    test_spec_file: Path,
    workspace: Path,
    rustc: str,
    rust_flags: Sequence[str],
    rust_bin: Path,
    compile_timeout: float,
    max_attempts: int,
    target_files: Sequence[Path],
    logs_dir: Path,
) -> Tuple[bool, CommandResult, int]:
    last_compile = compile_rust(rustc, rust_file, rust_bin, rust_flags, compile_timeout)
    if last_compile.ok:
        return True, last_compile, 0

    for attempt in range(1, max_attempts + 1):
        prompt = build_compile_repair_prompt(c_file, rust_file, last_compile)
        prompt_file = logs_dir / f"compile_repair_prompt_{attempt}.txt"
        write_text(prompt_file, prompt)
        backend_result = backend.invoke(
            phase="compile_repair",
            workspace=workspace,
            prompt_file=prompt_file,
            c_file=c_file,
            rust_file=rust_file,
            test_spec_file=test_spec_file,
            target_files=target_files,
        )
        write_text(logs_dir / f"compile_repair_backend_{attempt}.log", backend_result.stdout + "\n" + backend_result.stderr)
        if not backend_result.ok:
            return False, last_compile, attempt
        last_compile = compile_rust(rustc, rust_file, rust_bin, rust_flags, compile_timeout)
        write_text(
            logs_dir / f"compile_rust_{attempt}.log",
            "STDOUT:\n" + last_compile.stdout + "\nSTDERR:\n" + last_compile.stderr,
        )
        if last_compile.ok:
            return True, last_compile, attempt
    return False, last_compile, max_attempts


def generate_test_cases(
    *,
    backend: LLMCommandBackend,
    c_file: Path,
    rust_file: Path,
    test_spec_file: Path,
    workspace: Path,
    max_cases: int,
    default_timeout: float,
    logs_dir: Path,
) -> List[TestCase]:
    write_default_test_spec(test_spec_file, default_timeout)
    if backend.enabled():
        prompt = build_test_generation_prompt(c_file, rust_file, test_spec_file, max_cases)
        prompt_file = logs_dir / "test_generation_prompt.txt"
        write_text(prompt_file, prompt)
        backend_result = backend.invoke(
            phase="test_generation",
            workspace=workspace,
            prompt_file=prompt_file,
            c_file=c_file,
            rust_file=rust_file,
            test_spec_file=test_spec_file,
            target_files=[test_spec_file],
        )
        write_text(logs_dir / "test_generation_backend.log", backend_result.stdout + "\n" + backend_result.stderr)
    return parse_test_cases(test_spec_file, default_timeout)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="C -> Rust + LLM repair + differential testing pipeline")
    parser.add_argument("c_file", help="Path to the input C file")
    parser.add_argument("--ccomp", default="./ccomp", help="Path to ccomp executable")
    parser.add_argument("--cc", default="gcc", help="C compiler command")
    parser.add_argument("--rustc", default="rustc", help="Rust compiler command")
    parser.add_argument("--workspace", default="test/ai_pipeline_run", help="Workspace directory")
    parser.add_argument("--gcc-flag", action="append", default=[], help="Extra GCC flags")
    parser.add_argument("--gcc-lib", action="append", default=[], help="Extra GCC link libraries")
    parser.add_argument("--rust-flag", action="append", default=[], help="Extra rustc flags")
    parser.add_argument("--translation-timeout", type=float, default=120.0)
    parser.add_argument("--compile-timeout", type=float, default=120.0)
    parser.add_argument("--run-timeout", type=float, default=5.0)
    parser.add_argument("--max-compile-repairs", type=int, default=5)
    parser.add_argument("--max-mismatch-repairs", type=int, default=3)
    parser.add_argument("--max-test-cases", type=int, default=3)
    parser.add_argument(
        "--llm-backend",
        choices=["none", "generic", "aider"],
        default="none",
        help="LLM backend to use. 'aider' is recommended for local code editing.",
    )
    parser.add_argument(
        "--llm-command-template",
        default="",
        help="Shell command template used to invoke an external LLM tool.",
    )
    parser.add_argument("--aider-command", default="aider", help="Aider executable name or path")
    parser.add_argument("--aider-model", default="", help="Aider model name, e.g. sonnet or openai/gpt-4.1")
    parser.add_argument(
        "--aider-env-file",
        default=".env.aider.deepseek",
        help="Env file used by the aider backend. Defaults to .env.aider.deepseek in repo root.",
    )
    parser.add_argument(
        "--aider-arg",
        action="append",
        default=[],
        help="Extra argument passed through to aider. Can be repeated.",
    )
    parser.add_argument(
        "--editable-file",
        action="append",
        default=[],
        help="Extra files the LLM is allowed to edit, e.g. runtime/ptr.rs",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path.cwd().resolve()
    c_file = Path(args.c_file).resolve()
    ccomp = Path(args.ccomp).resolve()
    workspace = Path(args.workspace).resolve()
    logs_dir = workspace / "logs"
    aider_env_file = Path(args.aider_env_file)
    if not aider_env_file.is_absolute():
        aider_env_file = (repo_root / aider_env_file).resolve()

    ensure_dir(workspace)
    ensure_dir(logs_dir)

    rust_file = find_generated_rust_file(workspace, c_file)
    rust_bin = workspace / f"{c_file.stem}_rust_bin"
    c_bin = workspace / f"{c_file.stem}_c_bin"
    test_spec_file = workspace / "test_cases.json"
    report_file = workspace / "report.json"

    for path in [rust_bin, c_bin]:
        if path.exists():
            path.unlink()

    editable_files = [rust_file]
    editable_files.extend(Path(item).resolve() for item in args.editable_file)

    aider_file_env = parse_env_file(aider_env_file)
    aider_process_env = os.environ.copy()
    aider_process_env.update(aider_file_env)

    if args.llm_backend == "aider":
        aider_command = args.aider_command
        if aider_command == "aider" and aider_file_env.get("AIDER_BIN"):
            aider_command = aider_file_env["AIDER_BIN"]
        aider_model = args.aider_model.strip() or aider_file_env.get("AIDER_MODEL", "").strip()
        backend: Any = AiderBackend(
            aider_command=aider_command,
            model=aider_model,
            timeout=max(args.compile_timeout, 300.0),
            extra_args=args.aider_arg,
            env=aider_process_env,
            env_file=aider_env_file,
        )
    elif args.llm_backend == "generic":
        backend = LLMCommandBackend(
            args.llm_command_template.strip() or None,
            timeout=max(args.compile_timeout, 300.0),
            env=os.environ.copy(),
        )
    else:
        backend = LLMCommandBackend(None, timeout=max(args.compile_timeout, 300.0))

    report: Dict[str, Any] = {
        "c_file": str(c_file),
        "workspace": str(workspace),
        "rust_file": str(rust_file),
        "status": "INIT",
        "compile_repairs_used": 0,
        "mismatch_repairs_used": 0,
        "llm_backend_enabled": backend.enabled(),
        "aider_env_file": str(aider_env_file),
    }

    translated, rust_file, translate_result = translate_c_to_rust(ccomp, c_file, workspace, args.translation_timeout)
    write_text(
        logs_dir / "translate.log",
        "STDOUT:\n" + translate_result.stdout + "\nSTDERR:\n" + translate_result.stderr,
    )
    report["translation_returncode"] = translate_result.returncode
    report["translation_stderr"] = compact_output(translate_result.stderr)

    if not translated:
        report["status"] = "FAIL_TRANSLATION"
        write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
        print("FAIL_TRANSLATION")
        print(compact_output(translate_result.stderr))
        return 1

    compile_ok, last_compile, compile_attempts = run_compile_repair_loop(
        backend=backend,
        c_file=c_file,
        rust_file=rust_file,
        test_spec_file=test_spec_file,
        workspace=workspace,
        rustc=args.rustc,
        rust_flags=DEFAULT_RUST_FLAGS + list(args.rust_flag),
        rust_bin=rust_bin,
        compile_timeout=args.compile_timeout,
        max_attempts=args.max_compile_repairs,
        target_files=editable_files,
        logs_dir=logs_dir,
    )
    report["compile_repairs_used"] = compile_attempts
    report["last_compile_stderr"] = compact_output(last_compile.stderr)

    if not compile_ok:
        report["status"] = "FAIL_COMPILE"
        write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
        print("FAIL_COMPILE")
        print(compact_output(last_compile.stderr))
        return 1

    c_compile = compile_c(
        args.cc,
        c_file,
        c_bin,
        DEFAULT_GCC_FLAGS + list(args.gcc_flag),
        DEFAULT_GCC_LIBS + list(args.gcc_lib),
        args.compile_timeout,
    )
    write_text(
        logs_dir / "compile_c.log",
        "STDOUT:\n" + c_compile.stdout + "\nSTDERR:\n" + c_compile.stderr,
    )
    if not c_compile.ok:
        report["status"] = "FAIL_C_BASELINE"
        report["c_compile_stderr"] = compact_output(c_compile.stderr)
        write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
        print("FAIL_C_BASELINE")
        print(compact_output(c_compile.stderr))
        return 1

    test_cases = generate_test_cases(
        backend=backend,
        c_file=c_file,
        rust_file=rust_file,
        test_spec_file=test_spec_file,
        workspace=workspace,
        max_cases=args.max_test_cases,
        default_timeout=args.run_timeout,
        logs_dir=logs_dir,
    )

    final_outcome = run_diff_tests(c_bin, rust_bin, test_cases)
    mismatch_repairs = 0
    while not final_outcome.ok and mismatch_repairs < args.max_mismatch_repairs:
        mismatch_repairs += 1
        prompt = build_mismatch_repair_prompt(c_file, rust_file, final_outcome)
        prompt_file = logs_dir / f"mismatch_repair_prompt_{mismatch_repairs}.txt"
        write_text(prompt_file, prompt)
        backend_result = backend.invoke(
            phase="mismatch_repair",
            workspace=workspace,
            prompt_file=prompt_file,
            c_file=c_file,
            rust_file=rust_file,
            test_spec_file=test_spec_file,
            target_files=editable_files,
        )
        write_text(
            logs_dir / f"mismatch_repair_backend_{mismatch_repairs}.log",
            backend_result.stdout + "\n" + backend_result.stderr,
        )
        if not backend_result.ok:
            break

        compile_ok, last_compile, extra_compile_attempts = run_compile_repair_loop(
            backend=backend,
            c_file=c_file,
            rust_file=rust_file,
            test_spec_file=test_spec_file,
            workspace=workspace,
            rustc=args.rustc,
            rust_flags=DEFAULT_RUST_FLAGS + list(args.rust_flag),
            rust_bin=rust_bin,
            compile_timeout=args.compile_timeout,
            max_attempts=args.max_compile_repairs,
            target_files=editable_files,
            logs_dir=logs_dir,
        )
        report["compile_repairs_used"] += extra_compile_attempts
        if not compile_ok:
            report["status"] = "FAIL_COMPILE"
            report["last_compile_stderr"] = compact_output(last_compile.stderr)
            write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
            print("FAIL_COMPILE")
            print(compact_output(last_compile.stderr))
            return 1

        test_cases = generate_test_cases(
            backend=backend,
            c_file=c_file,
            rust_file=rust_file,
            test_spec_file=test_spec_file,
            workspace=workspace,
            max_cases=args.max_test_cases,
            default_timeout=args.run_timeout,
            logs_dir=logs_dir,
        )
        final_outcome = run_diff_tests(c_bin, rust_bin, test_cases)

    report["mismatch_repairs_used"] = mismatch_repairs
    report["test_cases"] = [asdict(case) for case in test_cases]

    if final_outcome.ok:
        report["status"] = "SUCCESS"
        write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
        print("SUCCESS")
        print(f"Rust file: {rust_file}")
        print(f"Report: {report_file}")
        return 0

    report["status"] = "FAIL_MISMATCH"
    report["mismatch_detail"] = {
        "detail": final_outcome.detail,
        "case": asdict(final_outcome.case) if final_outcome.case else None,
        "c_stdout": final_outcome.c_stdout,
        "rust_stdout": final_outcome.rust_stdout,
        "c_stderr": final_outcome.c_stderr,
        "rust_stderr": final_outcome.rust_stderr,
        "c_exit": final_outcome.c_exit,
        "rust_exit": final_outcome.rust_exit,
    }
    write_text(report_file, json.dumps(report, indent=2, ensure_ascii=True) + "\n")
    print("FAIL_MISMATCH")
    print(final_outcome.detail)
    return 1


if __name__ == "__main__":
    sys.exit(main())
