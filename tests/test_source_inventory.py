"""Run the real source-inventory CLI on copies of the locked source fixture."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CHECKOUT = Path('csrc/upstream/v2.93.01/checkout')


class SourceInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='ucos-source-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = os.environ.copy()
        for name in ['scripts/inventory-v293-source.py', 'csrc/UPSTREAM.lock.json',
                     'csrc/config/v29301-profile.json', 'csrc/analysis-port/os_cpu.h',
                     'csrc/analysis-port/app_cfg.h']:
            self.copy(Path(name))
        lock = json.loads((ROOT / 'csrc/UPSTREAM.lock.json').read_text())
        for name in [*lock['files'], lock['config_template'], 'os_cfg.h']:
            self.copy(CHECKOUT / name)
        (self.root / 'audit').mkdir()

    def copy(self, rel):
        dest = self.root / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dest)

    def run_inventory(self, expected=0, check=False):
        cmd = ['python3', str(self.root / 'scripts/inventory-v293-source.py')]
        if check:
            cmd.append('--check')
        result = subprocess.run(cmd, cwd=self.root, capture_output=True, text=True, env=self.env)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result.stdout + result.stderr

    def change(self, rel, old, new):
        p = self.root / rel
        text = p.read_text()
        self.assertEqual(text.count(old), 1, old)
        p.write_text(text.replace(old, new))

    def test_real_fixed_profile_and_check_mode(self):
        self.run_inventory()
        path = self.root / 'audit/source-inventory.json'
        before = path.read_bytes()
        self.run_inventory(check=True)
        self.assertEqual(before, path.read_bytes())
        result = json.loads(before)
        self.assertFalse(result['proof_coverage_credit'])
        self.assertEqual(result['summary']['configured_c_definitions'], 92)
        self.assertEqual(result['summary']['excluded_definitions'], 34)
        self.assertEqual(result['summary']['declaration_only_boundaries'], 16)
        functions = {f['name']: f for f in result['functions']}
        self.assertIn('OS_StrLen', functions)  # Do not remove syntactically active unused helpers.
        self.assertEqual(functions['OSVersion']['category'], 'public')
        self.assertIn('V293_EnterCritical', functions['OSTaskDel']['direct_calls'])
        self.assertIn('OSCtxSw', functions['OS_Sched']['direct_calls'])
        self.assertTrue(all(f['first_line'] <= f['last_line'] for f in functions.values()))
        excluded = {f['name'] for f in result['excluded_definitions']}
        self.assertIn('OSEventPendMulti', excluded)
        self.assertIn('OSTmrCreate', excluded)
        self.assertIn('OSDebugInit', excluded)

    def test_upstream_mutation_is_rejected(self):
        self.change(CHECKOUT / 'Source/os_core.c', 'return (OS_VERSION);', 'return (0u);')
        self.assertIn('upstream hash mismatch', self.run_inventory(1))

    def test_extra_source_is_rejected(self):
        (self.root / CHECKOUT / 'Source/hidden.c').write_text('void hidden(void) {}\n')
        self.assertIn('file set differs', self.run_inventory(1))

    def test_configuration_mutation_is_rejected(self):
        p = self.root / CHECKOUT / 'os_cfg.h'
        p.write_text(p.read_text() + '\n#define EXTRA_SETTING 1\n')
        self.assertIn('configuration hash mismatch', self.run_inventory(1))

    def test_port_cannot_override_fixed_configuration(self):
        p = self.root / 'csrc/analysis-port/os_cpu.h'
        p.write_text(p.read_text() + '\n#undef OS_MUTEX_EN\n#define OS_MUTEX_EN 0u\n')
        self.assertIn('effective macro differs', self.run_inventory(1))

    def test_empty_critical_section_is_rejected(self):
        self.change('csrc/analysis-port/os_cpu.h',
                    '#define OS_ENTER_CRITICAL() V293_EnterCritical(&cpu_sr)',
                    '#define OS_ENTER_CRITICAL() ((void)0)')
        self.assertIn('critical-section boundary erased', self.run_inventory(1))

    def test_unclassified_boundary_is_rejected(self):
        p = self.root / 'csrc/analysis-port/app_cfg.h'
        p.write_text(p.read_text() + '\nvoid UnknownHook(void);\n')
        self.assertIn('unclassified declaration', self.run_inventory(1))

    def test_manifest_tampering_is_rejected_without_rewrite(self):
        self.run_inventory()
        path = self.root / 'audit/source-inventory.json'
        path.write_text('{}\n')
        self.assertIn('inventory drift', self.run_inventory(1, check=True))
        self.assertEqual(path.read_text(), '{}\n')

    def test_adapter_width_mismatch_is_rejected_by_compiler(self):
        self.change('csrc/analysis-port/os_cpu.h',
                    'typedef unsigned int   INT32U;', 'typedef unsigned short INT32U;')
        self.assertIn('INT32U width', self.run_inventory(1))

    def test_empty_context_switch_is_rejected(self):
        self.change('csrc/analysis-port/os_cpu.h',
                    '#define OS_TASK_SW() OSCtxSw()', '#define OS_TASK_SW() ((void)0)')
        self.assertIn('context-switch boundary erased', self.run_inventory(1))

    def fake_tool(self, name, transform):
        real = shutil.which(name)
        directory = self.root / 'bin'
        directory.mkdir()
        tool = directory / name
        tool.write_text(
            '#!/usr/bin/env python3\nimport subprocess, sys\n'
            f'p = subprocess.run([{real!r}, *sys.argv[1:]], capture_output=True)\n'
            'data = p.stdout\n' + transform + '\n'
            'sys.stdout.buffer.write(data)\nsys.stderr.buffer.write(p.stderr)\n'
            'sys.exit(p.returncode)\n')
        tool.chmod(0o755)
        self.env['PATH'] = str(directory) + os.pathsep + self.env['PATH']

    def test_preprocessor_disagreement_is_rejected(self):
        self.fake_tool('gcc', "if '-E' in sys.argv: data = data.replace(b'OSVersion', b'WrongName')")
        self.assertIn('preprocessing disagree', self.run_inventory(1))

    def test_catalogue_missing_active_function_is_rejected(self):
        self.fake_tool('ctags', "if '--version' not in sys.argv:\n"
                       " data = b'\\n'.join(l for l in data.splitlines() if b'OSVersion' not in l)")
        self.assertIn('source extent disagreement: OSVersion', self.run_inventory(1))


if __name__ == '__main__':
    unittest.main()
