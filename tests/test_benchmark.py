import base64
import csv
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import benchmark as b


class BenchmarkTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / 'sample.c'
        self.source.write_text('int main(void) { return 0; }')
        for runtime_file in ('ptr.rs', 'callback.rs', 'stdio.rs'):
            (self.root / runtime_file).write_text('// test runtime module\n')

    def scenario(self, *, codes=None, output=None, artifact=True, keep=False,
                 continuation=False, error=None, config=None):
        codes, output = codes or {}, output or {}
        calls = []

        def fake(command, timeout, cwd, stdin):
            name = b.STAGES[len(calls)]
            calls.append(name)
            if name == 'translation' and artifact:
                (Path(cwd) / 'sample.rs').write_text('fn main() {}')
            return dict(command=command, cwd=str(cwd), returncode=codes.get(name, 0),
                        stdout=output.get(name, b'hello\n'), stderr=b'diagnostic\xff',
                        duration_seconds=0.01, error_kind=error[1] if error and error[0] == name else None,
                        error='injected failure' if error and error[0] == name else None)

        with patch.object(b, 'run_command', side_effect=fake):
            result = b.benchmark_single_file(self.source, self.root / 'ccomp', self.root,
                self.root, keep_failures=keep, continue_translation_failure=continuation,
                config=config)
        return result, calls

    def test_exact(self):
        self.assertTrue(b.outputs_equal(b'hello\n', b'hello\n'))
        self.assertEqual(self.scenario()[0]['Status'], 'PASS')

    def test_trailing_whitespace(self):
        for value in (b'hello', b'hello \n', b'hello\r\n'):
            self.assertFalse(b.outputs_equal(b'hello\n', value))
        r, _ = self.scenario(output={'rust_run': b'hello'})
        self.assertEqual(r['Status'], 'OUTPUT_MISMATCH')

    def test_binary(self):
        r, _ = self.scenario(output={'c_run': b'\xff\x00', 'rust_run': b'\xff\x00'})
        self.assertEqual(r['Status'], 'PASS')
        self.assertEqual(base64.b64decode(r['stages']['c_run']['stdout_base64']), b'\xff\x00')
        self.assertFalse(b.outputs_equal(b'\xff ', b'\xff'))

    def test_exit_mismatch(self):
        for codes in ({'c_run': 2}, {'rust_run': 2}):
            r, _ = self.scenario(codes=codes)
            self.assertEqual(r['Status'], 'EXIT_CODE_MISMATCH')
            self.assertFalse(r['Exit_Code_Equal'])

    def test_both_nonzero(self):
        self.assertEqual(self.scenario(codes={'c_run': 2, 'rust_run': 2})[0]['Status'], 'C_RUNTIME_FAIL')

    def test_translation_failure_with_artifact(self):
        r, calls = self.scenario(codes={'translation': 1}, keep=True)
        self.assertEqual(r['Status'], 'TRANSLATION_FAIL')
        self.assertTrue(r['Rust_Generated'])
        self.assertFalse(r['Translation_Success'])
        self.assertNotIn('rust_compile', calls)
        self.assertTrue((Path(r['workspace']) / 'sample.rs').exists())
        self.assertTrue((Path(r['workspace']) / 'translation.stderr').exists())

    def test_diagnostic_continuation_never_passes(self):
        r, calls = self.scenario(codes={'translation': 1}, continuation=True)
        self.assertIn('rust_run', calls)
        self.assertEqual(r['Status'], 'TRANSLATION_FAIL')
        self.assertTrue(r['compatibility_used'])

    def test_stale_artifact(self):
        old = self.root / 'sample.rs'
        old.write_text('stale')
        previous, _ = self.scenario(codes={'translation': 1}, keep=True)
        r, _ = self.scenario(artifact=False)
        self.assertEqual(r['Status'], 'TRANSLATION_FAIL')
        self.assertFalse(r['Rust_Generated'])
        self.assertEqual(old.read_text(), 'stale')
        self.assertTrue(Path(previous['workspace']).exists())

    def test_timeout(self):
        r = b.run_command([sys.executable, '-c',
                           'import time; print("partial", flush=True); time.sleep(5)'], timeout=0.2)
        self.assertEqual(r['error_kind'], 'timeout')
        self.assertIn(b'partial', r['stdout'])
        self.assertGreaterEqual(r['duration_seconds'], 0.2)
        self.assertEqual(self.scenario(error=('translation', 'timeout'))[0]['Status'], 'TIMEOUT')

    def test_compiler_launch_failure(self):
        r = b.run_command([str(self.root / 'missing-compiler')])
        self.assertEqual(r['error_kind'], 'launch')
        self.assertIsNone(r['returncode'])
        for stage in ('c_compile', 'rust_compile'):
            r, _ = self.scenario(error=(stage, 'launch'))
            self.assertEqual(r['Status'], 'LAUNCH_FAIL')
            self.assertEqual(r['Failure_Stage'], stage)

    def test_compile_error(self):
        for stage, expected in [('c_compile', 'C_COMPILE_FAIL'), ('rust_compile', 'RUST_COMPILE_FAIL')]:
            r, _ = self.scenario(codes={stage: 1})
            self.assertEqual(r['Status'], expected)
            self.assertEqual(r['stages'][stage]['returncode'], 1)

    def test_signal(self):
        for stage, expected in [('c_run', 'C_RUNTIME_FAIL'), ('rust_run', 'RUST_RUNTIME_FAIL')]:
            self.assertEqual(self.scenario(codes={stage: -11})[0]['Status'], expected)

    def test_missing_output_file(self):
        self.assertEqual(self.scenario(config={'output_files': ['out.bin']})[0]['Status'], 'FILE_MISMATCH')

    def test_unknown_normalization(self):
        with self.assertRaises(ValueError):
            b.outputs_equal(b'a', b'a', 'strip')

    def test_cli_reports(self):
        report = self.root / 'report.csv'
        # Real subprocess launch failure: no CompCert environment required.
        code = b.main(['--test-dir', str(self.root), '--gcc', str(self.root / 'absent'),
                       '--results', str(report)])
        self.assertEqual(code, 1)
        with report.open() as stream:
            rows = list(csv.DictReader(stream))
        payload = json.loads(report.with_suffix('.json').read_text())
        self.assertEqual(rows[0]['Status'], payload['results'][0]['Status'])
        self.assertEqual(payload['summary'], {'LAUNCH_FAIL': 1})
        self.assertIn('git', payload['metadata'])
        self.assertTrue(set(b.CSV_FIELDS).issubset(rows[0]))


if __name__ == '__main__':
    unittest.main()
