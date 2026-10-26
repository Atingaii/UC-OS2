"""Real kernel matrix plus single-factor mutations of downstream mechanisms."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('c_regression', ROOT / 'scripts/check-v293-c-regressions.py')
REGRESSION = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REGRESSION)


class KernelMatrixTests(unittest.TestCase):
    def test_real_two_by_two_matrix_at_two_optimization_levels(self):
        report = REGRESSION.check_matrix()
        self.assertEqual(len(report['results']), 4 * 2 * 2 * 23)
        self.assertTrue(report['matrix_passed'], json.dumps(
            [r for r in report['results'] if not r['expectation_met']], indent=2))
        self.assertTrue(report['both_repairs_all_cases_passed'])
        self.assertEqual(sum(r['expected'] == 'KNOWN_FAILURE' for r in report['results']), 112)


class RunnerBoundaryTests(unittest.TestCase):
    def test_configuration_drift_is_rejected_without_rewriting_it(self):
        with tempfile.TemporaryDirectory(prefix='ucos-c-readonly-') as directory:
            root = Path(directory)
            lock = json.loads((ROOT / 'csrc/UPSTREAM.lock.json').read_text())
            paths = [*REGRESSION.PATCHES.values(), Path('csrc/UPSTREAM.lock.json'),
                     Path('csrc/config/v29301-profile.json'),
                     Path('csrc/analysis-port/os_cpu.h'), Path('csrc/analysis-port/app_cfg.h'),
                     Path('scripts/check-v293-c-regressions.py'), Path('scripts/inventory-v293-source.py'),
                     Path('audit/source-inventory.json')]
            paths += [REGRESSION.CHECKOUT / p for p in [*lock['files'], lock['config_template'], 'os_cfg.h']]
            for rel in paths:
                target = root / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / rel, target)
            config = root / REGRESSION.CHECKOUT / 'os_cfg.h'
            changed = config.read_bytes() + b'\n#define MUTATED_LOCAL_CONFIG 1u\n'
            config.write_bytes(changed)
            result = subprocess.run(['python3', str(root / 'scripts/check-v293-c-regressions.py')],
                                    cwd=root, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn('configuration hash mismatch', result.stderr)
            self.assertEqual(config.read_bytes(), changed)

    def test_patch_cannot_modify_a_third_source_file(self):
        with tempfile.TemporaryDirectory(prefix='ucos-c-patch-scope-') as directory:
            root = Path(directory)
            patch = root / 'outside.patch'
            patch.write_text('--- a/Source/os_core.c\n+++ b/Source/os_core.c\n'
                             '@@ -1 +1 @@\n-old\n+new\n')
            old = REGRESSION.PATCHES['mutex']
            try:
                REGRESSION.PATCHES['mutex'] = patch
                with self.assertRaisesRegex(ValueError, 'outside its authorized source'):
                    REGRESSION.materialize(root / 'kernel', ('mutex',))
            finally:
                REGRESSION.PATCHES['mutex'] = old


class MechanismAblationTests(unittest.TestCase):
    """Only the listed source expression changes; fixture/profile stay fixed.

    Each mutant must reach its own, preselected assertion. An earlier crash or
    unrelated failure is NOT evidence that a downstream mechanism is covered.
    """
    def mutant(self, source_file, old, new, case, assertion):
        with tempfile.TemporaryDirectory(prefix='ucos-c-mutant-') as directory:
            work = Path(directory)
            source = work / 'kernel'
            REGRESSION.materialize(source, ('mutex', 'guard'))
            path = source / 'Source' / source_file
            original = path.read_text()
            self.assertEqual(original.count(old), 1, old)
            path.write_text(original.replace(old, new))
            self.assertNotEqual(path.read_bytes(), original.encode())
            binary = work / 'mutant'
            REGRESSION.compile_binary(source, binary)
            result = subprocess.run([str(binary), str(case)], capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn(f'expression={assertion}\n', result.stdout)
            self.assertEqual(result.stderr, '')

    def test_accept_must_save_base_not_current_priority(self):
        self.mutant('os_mutex.c',
                    '(INT16U)OSMutex_BasePrio(OSTCBCur); /* Save base priority, not an inherited PCP */',
                    '(INT16U)OSTCBCur->OSTCBPrio;', 4, 'owner->OSTCBPrio == 10')

    def test_pend_must_save_base_not_current_priority(self):
        self.mutant('os_mutex.c',
                    '(INT16U)OSMutex_BasePrio(OSTCBCur); /* Save base priority before inheritance   */',
                    '(INT16U)OSTCBCur->OSTCBPrio;', 3, 'owner->OSTCBPrio == 10')

    def test_handoff_must_save_new_owners_base_priority(self):
        self.mutant('os_mutex.c', '(INT16U)OSMutex_BasePrio(OSTCBPrioTbl[prio]);',
                    '(INT16U)prio;', 21, '(second->OSEventCnt & 0xffu) == 10')

    def test_remaining_contribution_must_not_be_discarded(self):
        self.mutant('os_mutex.c', '(OSTCBPrioTbl[pcp] == ptcb) &&',
                    '(0u != 0u) &&', 3, 'owner->OSTCBPrio == (reverse ? 5 : 3)')

    def test_relocation_must_not_ready_suspended_owner(self):
        self.mutant('os_mutex.c', 'if (rdy == OS_TRUE) {\n        OSRdyGrp',
                    'if (1) {\n        OSRdyGrp', 19,
                    '(OSRdyTbl[owner->OSTCBY] & owner->OSTCBBitX) == 0')

    def test_relocation_must_move_wait_map_membership(self):
        self.mutant('os_mutex.c', 'if (waiting == OS_TRUE) {\n        event->OSEventGrp',
                    'if (0) {\n        event->OSEventGrp', 20,
                    '(second->OSEventTbl[10 >> 3] & (1u << (10 & 7))) != 0')

    def test_relocation_must_not_change_other_current_priority(self):
        self.mutant('os_mutex.c', 'if (ptcb == OSTCBCur) {\n        OSPrioCur = prio;',
                    'if (1) {\n        OSPrioCur = prio;', 20,
                    'OSPrioCur == 3 && OSTCBCur == controller')

    def test_slot_ownership_is_checked_after_correct_base_restoration(self):
        self.mutant('os_mutex.c', '    OSTCBPrioTbl[prio] = ptcb;',
                    '    OSTCBPrioTbl[prio] = ptcb;\n'
                    '    if (prio == 10u) { OSTCBPrioTbl[5] = ptcb; }', 5,
                    'OSTCBPrioTbl[5] == replacement && replacement->OSTCBPrio == 5')

    def test_guard_must_not_reject_noncurrent_task(self):
        self.mutant('os_task.c', '(ptcb == OSTCBCur) && (OSLockNesting > 0u)',
                    '(OSLockNesting > 0u)', 17, 'OSTaskDel(9) == OS_ERR_NONE')

    def test_guard_must_not_reject_unlocked_current_task(self):
        self.mutant('os_task.c', '(ptcb == OSTCBCur) && (OSLockNesting > 0u)',
                    '(ptcb == OSTCBCur)', 17, 'OSTaskDel(OS_PRIO_SELF) == OS_ERR_NONE')

    def test_guard_must_precede_first_ready_mutation(self):
        self.mutant('os_task.c',
                    'if ((ptcb == OSTCBCur) && (OSLockNesting > 0u)) {',
                    'OSRdyTbl[ptcb->OSTCBY] &= (OS_PRIO)~ptcb->OSTCBBitX;\n'
                    '    if ((ptcb == OSTCBCur) && (OSLockNesting > 0u)) {',
                    13, 'equal_bytes(&before, &after, sizeof(before))')


if __name__ == '__main__':
    unittest.main()
