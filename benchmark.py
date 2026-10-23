"""Correctness-first, single-run Clight2Rust benchmark (standard library only)."""
import argparse
import base64
from collections import Counter
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
GCC_FLAGS = ['-O3', '-Wno-return-type', '-Wno-implicit-int']
RUST_FLAGS = ['-O', '--cap-lints=allow']
CSV_FIELDS = ['Benchmark', 'Status', 'C_Time', 'Rust_Time', 'Overhead', 'Note',
              'Source', 'Failure_Stage', 'Stdout_Equal', 'Exit_Code_Equal',
              'Translation_Success', 'Rust_Generated', 'Rust_Compile_Success']
STAGES = ('c_compile', 'c_run', 'translation', 'rust_compile', 'rust_run')


def outputs_equal(c_out, rs_out, mode='exact'):
    """Explicit comparison extension point; no implicit decoding/normalization."""
    if mode != 'exact':
        raise ValueError('Unsupported stdout comparison mode: ' + mode)
    return c_out == rs_out


def run_command(command, timeout=10.0, cwd=None, stdin=b''):
    start = time.perf_counter()
    result = dict(command=[str(x) for x in command], cwd=str(cwd or Path.cwd()),
                  returncode=None, error_kind=None, error=None, stdout=b'', stderr=b'')
    try:
        with subprocess.Popen(result['command'], cwd=cwd, stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              start_new_session=(os.name == 'posix')) as proc:
            try:
                result['stdout'], result['stderr'] = proc.communicate(stdin, timeout=timeout)
            except subprocess.TimeoutExpired:
                if os.name == 'posix':
                    os.killpg(proc.pid, signal.SIGKILL)
                else:
                    proc.kill()
                result['stdout'], result['stderr'] = proc.communicate()
                result.update(error_kind='timeout', error=f'Exceeded {timeout} seconds')
            result['returncode'] = proc.returncode
    except OSError as exc:
        result.update(error_kind='launch', error=str(exc))
    result['duration_seconds'] = time.perf_counter() - start
    return result


def serial_stage(stage, directory, name):
    """JSON retains lossless logs even if the temporary workspace is removed."""
    record = dict(stage)
    for stream in ('stdout', 'stderr'):
        data = record.pop(stream)
        (directory / f'{name}.{stream}').write_bytes(data)
        record[stream + '_base64'] = base64.b64encode(data).decode('ascii')
        record[stream + '_preview'] = data[:4096].decode('utf-8', errors='replace')
    return record


def relative_path(value):
    path = Path(value)
    if path.is_absolute() or '..' in path.parts or str(path) == '.':
        raise ValueError(f'Expected a relative path without ..: {value}')
    return path


def benchmark_single_file(c_file_path, ccomp_bin, runtime_path, temp_dir,
                          *, gcc='gcc', rustc='rustc', timeout=10.0,
                          compile_timeout=60.0, keep_failures=False,
                          continue_translation_failure=False, config=None):
    source = Path(c_file_path).resolve()
    config = config or {}
    mode = config.get('stdout_mode', 'exact')
    outputs_equal(b'', b'', mode)  # Reject unsupported policies before execution.
    work = Path(tempfile.mkdtemp(prefix=source.stem + '-', dir=temp_dir))
    cdir, rdir = work / 'c_run', work / 'rust_run'
    cdir.mkdir()
    rdir.mkdir()
    # Existing knucleotide fixture; each side gets an independent copy.
    inputs = list(config.get('inputs', []))
    if source.stem == 'knucleotide' and not inputs:
        inputs = ['Results/knucleotide-input.txt']
    rs = work / (source.stem + '.rs')
    exe_c, exe_rs = work / 'program_c', work / 'program_rust'
    commands = {
        'c_compile': [gcc, *GCC_FLAGS, str(source), '-o', str(exe_c), '-lm'],
        'c_run': [str(exe_c), *config.get('args', [])],
        'translation': [str(Path(ccomp_bin).resolve()), '-drustlight', str(source)],
        'rust_compile': [rustc, *RUST_FLAGS, '-L', str(Path(runtime_path).resolve()),
                         str(rs), '-o', str(exe_rs)],
        'rust_run': [str(exe_rs), *config.get('args', [])],
    }
    result = dict(Benchmark=source.stem, Source=str(source), Status=None,
                  C_Time=0.0, Rust_Time=0.0, Overhead=0.0, Note='',
                  Failure_Stage=None, Stdout_Equal=None, Exit_Code_Equal=None,
                  Translation_Success=None, Rust_Generated=False,
                  Rust_Compile_Success=None, stages={s: None for s in STAGES},
                  commands=commands, comparison=dict(stdout_mode=mode,
                  stderr_compared=False, config=config, inputs=inputs), workspace=str(work),
                  artifacts_retained=False, compatibility_used=False,
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  started_at=datetime.now(timezone.utc).isoformat(), files=[])

    def finish(status, stage=None, note=''):
        result.update(Status=status, Failure_Stage=stage, Note=note)
        result['artifacts_retained'] = keep_failures and status != 'PASS'
        if result['artifacts_retained']:
            (work / 'result.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
        else:
            shutil.rmtree(work)  # Only the directory created by this invocation.
        return result

    def run(name):
        directory = cdir if name == 'c_run' else rdir if name == 'rust_run' else work
        stage = run_command(commands[name], timeout if name.endswith('_run') else compile_timeout,
                            directory, config.get('stdin', '').encode('utf-8'))
        result['stages'][name] = serial_stage(stage, work, name)
        return stage

    def exceptional(stage, name):
        if stage['error_kind']:
            return finish('TIMEOUT' if stage['error_kind'] == 'timeout' else 'LAUNCH_FAIL',
                          name, stage['error'])
        return None

    def reason(stage):
        return f"exit {stage['returncode']}: " + stage['stderr'][:4096].decode('utf-8', 'replace')

    try:
        for runtime_file in ('ptr.rs', 'callback.rs', 'stdio.rs'):
            shutil.copyfile(Path(runtime_path).resolve() / runtime_file,
                            work / runtime_file)
        for item in inputs:
            path = relative_path(item)
            for directory in (cdir, rdir):
                target = directory / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source.parent / path, target)
        for item in config.get('output_files', []):
            relative_path(item)
    except (OSError, ValueError) as exc:
        return finish('SETUP_FAIL', 'setup', str(exc))

    stage = run('c_compile')
    failure = exceptional(stage, 'c_compile')
    if failure:
        return failure
    if stage['returncode'] != 0:
        return finish('C_COMPILE_FAIL', 'c_compile', reason(stage))
    c = run('c_run')
    result['C_Time'] = c['duration_seconds']
    failure = exceptional(c, 'c_run')
    if failure:
        return failure
    if c['returncode'] < 0:
        return finish('C_RUNTIME_FAIL', 'c_run', reason(c))
    stage = run('translation')
    result['Rust_Generated'] = rs.is_file()
    result['Translation_Success'] = stage['returncode'] == 0 and not stage['error_kind']
    failure = exceptional(stage, 'translation')
    if failure:
        return failure
    translation_failed = not result['Translation_Success']
    if not rs.is_file() or (translation_failed and not continue_translation_failure):
        return finish('TRANSLATION_FAIL', 'translation', reason(stage) +
                      ('; Rust artifact missing' if not rs.is_file() else '; Rust artifact exists'))
    result['compatibility_used'] = translation_failed
    stage = run('rust_compile')
    result['Rust_Compile_Success'] = stage['returncode'] == 0 and not stage['error_kind']
    failure = exceptional(stage, 'rust_compile')
    if failure:
        return failure
    if stage['returncode'] != 0:
        return finish('RUST_COMPILE_FAIL', 'rust_compile', reason(stage))
    r = run('rust_run')
    result['Rust_Time'] = r['duration_seconds']
    failure = exceptional(r, 'rust_run')
    if failure:
        return failure
    result['Stdout_Equal'] = outputs_equal(c['stdout'], r['stdout'], mode)
    result['Exit_Code_Equal'] = c['returncode'] == r['returncode']
    if r['returncode'] < 0:
        return finish('RUST_RUNTIME_FAIL', 'rust_run', reason(r))
    if not result['Exit_Code_Equal']:
        return finish('EXIT_CODE_MISMATCH', 'comparison',
                      f"C exit {c['returncode']}, Rust exit {r['returncode']}")
    if c['returncode'] != 0:
        return finish('C_RUNTIME_FAIL', 'c_run', 'Both programs returned nonzero; ' + reason(c))
    if not result['Stdout_Equal']:
        return finish('OUTPUT_MISMATCH', 'comparison', 'stdout bytes differ')
    for item in config.get('output_files', []):
        record = dict(path=item, equal=False)
        try:
            a, b = (cdir / item).read_bytes(), (rdir / item).read_bytes()
            record.update(equal=a == b, c_sha256=hashlib.sha256(a).hexdigest(),
                          rust_sha256=hashlib.sha256(b).hexdigest())
        except OSError as exc:
            record['error'] = str(exc)
        result['files'].append(record)
    if any(not f['equal'] for f in result['files']):
        return finish('FILE_MISMATCH', 'comparison', 'Declared output files differ or are missing')
    if translation_failed:
        return finish('TRANSLATION_FAIL', 'translation',
                      'Diagnostic continuation matched behavior, but translation command failed')
    result['Overhead'] = r['duration_seconds'] / c['duration_seconds'] if c['duration_seconds'] else 0.0
    return finish('PASS')


def tool_info(command, cwd=None):
    stage = run_command(command, timeout=10, cwd=cwd)
    return {k: (v.decode('utf-8', 'replace') if isinstance(v, bytes) else v)
            for k, v in stage.items()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ccomp', default=str(ROOT / 'ccomp'))
    parser.add_argument('--test-dir', default=str(ROOT / 'test/c'), help='Scan top-level *.c (legacy scope)')
    parser.add_argument('--only', action='append', help='Run only this benchmark stem (repeatable)')
    parser.add_argument('--runtime', default=str(ROOT / 'runtime'), help='rustc -L search directory')
    parser.add_argument('--gcc', default='gcc')
    parser.add_argument('--rustc', default='rustc')
    parser.add_argument('--timeout', type=float, default=10, help='Seconds per program run (default: 10)')
    parser.add_argument('--compile-timeout', type=float, default=60, help='Seconds per compilation/translation')
    parser.add_argument('--keep-failures', action='store_true', help='Keep failed case workspaces and raw logs')
    parser.add_argument('--continue-translation-failure', action='store_true',
                        help='Diagnose Rust artifact after nonzero ccomp exit; never converts failure to PASS')
    parser.add_argument('--config', type=Path, help='JSON mapping benchmark stems to explicit input/output policies')
    parser.add_argument('--results', type=Path, default=Path('benchmark_results.csv'), help='CSV path; sibling .json is also written')
    args = parser.parse_args(argv)
    if args.timeout <= 0 or args.compile_timeout <= 0:
        parser.error('timeouts must be positive')
    if args.results.suffix.lower() != '.csv':
        parser.error('--results must end in .csv')
    sources = sorted(Path(args.test_dir).resolve().glob('*.c'))
    if args.only:
        missing = set(args.only) - {p.stem for p in sources}
        if missing:
            parser.error(f'Unknown benchmarks: {sorted(missing)}')
        sources = [p for p in sources if p.stem in args.only]
    if not sources:
        parser.error('No C benchmarks found')
    config = json.loads(args.config.read_text()) if args.config else {}
    for policy in config.values():
        unknown = set(policy) - {'args', 'stdin', 'inputs', 'output_files', 'stdout_mode'}
        if unknown:
            parser.error(f'Unknown policy keys: {sorted(unknown)}')
        outputs_equal(b'', b'', policy.get('stdout_mode', 'exact'))
    args.results.parent.mkdir(parents=True, exist_ok=True)
    # Unique sibling directory for every experiment, including concurrent runs.
    experiment = Path(tempfile.mkdtemp(prefix='benchmark-', dir=args.results.parent.resolve()))
    metadata = dict(started_at=datetime.now(timezone.utc).isoformat(),
                    platform=platform.platform(), architecture=platform.machine(),
                    gcc=tool_info([args.gcc, '--version'], experiment),
                    rustc=tool_info([args.rustc, '--version'], experiment),
                    ccomp=tool_info([str(Path(args.ccomp).resolve()), '-version'], experiment),
                    git=tool_info(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], experiment),
                    git_status=tool_info(['git', '-C', str(ROOT), 'status', '--porcelain'], experiment),
                    options={k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()})
    try:
        metadata['ccomp_sha256'] = hashlib.sha256(Path(args.ccomp).read_bytes()).hexdigest()
    except OSError:
        metadata['ccomp_sha256'] = None
    results = []
    for source in sources:
        result = benchmark_single_file(source, args.ccomp, args.runtime, experiment,
            gcc=args.gcc, rustc=args.rustc, timeout=args.timeout, compile_timeout=args.compile_timeout,
            keep_failures=args.keep_failures,
            continue_translation_failure=args.continue_translation_failure,
            config=config.get(source.stem))
        results.append(result)
        print(f"{source.stem}: {result['Status']}", flush=True)
    summary = dict(Counter(r['Status'] for r in results))
    metadata['finished_at'] = datetime.now(timezone.utc).isoformat()
    payload = dict(schema_version=1, metadata=metadata, summary=summary, results=results)
    # Exclusive creation: existing experiment reports are never overwritten.
    # The traditional paths are refreshed copies; the unique archive always survives.
    archive_csv = experiment / 'results.csv'
    with archive_csv.open('x', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fieldnames=CSV_FIELDS, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(results)
    archive_json = experiment / 'results.json'
    archive_json.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding='utf-8')
    shutil.copyfile(archive_csv, args.results)
    shutil.copyfile(archive_json, args.results.with_suffix('.json'))
    print(json.dumps(summary), '\nArchived results:', experiment)
    return 0 if all(r['Status'] == 'PASS' for r in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
