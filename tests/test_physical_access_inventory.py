"""Test actual Clang AST lvalue contexts, not a regex over C source."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import re
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('physical_access', ROOT / 'scripts/inventory-v293-physical-access.py')
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)
FIXTURE = b'''
struct nested { int x; };
struct sample { int scalar; int array[2]; int *pointer; struct nested nested; };
int G, GA[2], *GP;
void (*FP)(void);
void consume(int *p);
void write_field(struct sample *p) { p->scalar = G; }
int read_field(struct sample *p) { return p->scalar; }
void compound(struct sample *p) { p->scalar += 2; }
void increment(struct sample *p) { ++p->scalar; }
int *address(struct sample *p) { return &p->scalar; }
unsigned int size(struct sample *p) { return sizeof(p->scalar); }
void array_write(struct sample *p) { p->array[1] = 2; }
int array_read(struct sample *p) { return p->array[1]; }
void pointer_write(struct sample *p) { p->pointer[1] = 2; }
void array_escape(struct sample *p) { consume(p->array); }
void nested_write(struct sample *p) { p->nested.x = 2; }
void globals(void) { G = 1; ++G; GA[1] = 2; GP[1] = G; consume(&G); }
void shadow(void) { int G = 2; ++G; }
void whole_copy(struct sample *p, struct sample *q) { *p = *q; }
void indirect(void) { FP(); }
void empty_loop(void) { for (;;) { break; } }
'''


class PhysicalAccessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inv = TOOL.load('inventory-v293-source.py')
        cls.ast = json.loads(subprocess.run(['clang', *cls.inv.CLANG_FLAGS, '-x', 'c',
            '-fsyntax-only', '-Xclang', '-ast-dump=json', '-'], input=FIXTURE,
            capture_output=True, check=True).stdout)
        cls.rows = cls.rescan()

    @classmethod
    def rescan(cls):
        return {f['name']: f for f in TOOL.scan(cls.ast, FIXTURE, cls.inv.SourceMap(FIXTURE))}

    def modes(self, function, resource):
        return self.rows[function]['direct_resources'][resource]

    def test_scalar_read_write_and_read_modify_write(self):
        for function, mode in [('read_field', 'read'), ('write_field', 'write'),
                               ('compound', 'read_write'), ('increment', 'read_write')]:
            self.assertEqual(self.modes(function, 'sample.scalar'), [mode])

    def test_address_is_not_write_and_sizeof_is_unevaluated(self):
        self.assertEqual(self.modes('address', 'sample.scalar'), ['address'])
        self.assertEqual(self.modes('size', 'sample.scalar'), ['unevaluated'])

    def test_array_element_write_is_not_pointer_field_write(self):
        self.assertEqual(self.modes('array_write', 'sample.array'), ['write'])
        self.assertEqual(self.modes('array_read', 'sample.array'), ['read'])
        self.assertEqual(self.modes('pointer_write', 'sample.pointer'), ['read'])
        self.assertEqual(self.modes('array_escape', 'sample.array'), ['address'])

    def test_nested_aggregate_is_explicitly_unresolved(self):
        self.assertEqual(self.modes('nested_write', 'nested.x'), ['write'])
        self.assertEqual(self.modes('nested_write', 'sample.nested'), ['subobject_unresolved'])

    def test_global_shadowing_and_pointer_pointee(self):
        self.assertEqual(self.rows['shadow']['direct_resources'], {})
        self.assertEqual(self.modes('globals', 'G'), ['address', 'read', 'read_write', 'write'])
        self.assertEqual(self.modes('globals', 'GA'), ['write'])
        self.assertEqual(self.modes('globals', 'GP'), ['read'])

    def test_whole_record_and_indirect_call_are_not_silent_empty_effects(self):
        self.assertEqual(self.rows['whole_copy']['unresolved_effect_sites']['whole_record_assignments'], 1)
        self.assertEqual(self.rows['whole_copy']['unresolved_effect_sites']['explicit_pointer_dereferences'], 2)
        self.assertEqual(self.rows['indirect']['unresolved_effect_sites']['indirect_calls'], 1)
        self.assertEqual(self.modes('indirect', 'FP'), ['read'])

    def test_exact_expression_slices_and_locations(self):
        for row in self.rows.values():
            for access in row['accesses']:
                self.assertEqual(FIXTURE[access['begin_byte']:access['end_byte_exclusive']].decode(), access['expression'])
                self.assertEqual(FIXTURE[:access['begin_byte']].count(b'\n') + 1, access['line'])

    def test_for_loop_empty_ast_slots_are_not_expressions(self):
        self.assertEqual(self.rows['empty_loop']['direct_resources'], {})

    def test_write_recognition_single_factor_ablation(self):
        original = TOOL.access_mode
        with patch.object(TOOL, 'access_mode', side_effect=lambda a: 'read' if original(a) == 'write' else original(a)):
            mutated = self.rescan()
        self.assertNotEqual(mutated['write_field']['direct_resources']['sample.scalar'], ['write'])
        self.assertEqual(mutated['read_field'], self.rows['read_field'])
        self.assertEqual(mutated['address'], self.rows['address'])

    def test_address_recognition_single_factor_ablation(self):
        original = TOOL.access_mode
        with patch.object(TOOL, 'access_mode', side_effect=lambda a: 'read' if original(a) == 'address' else original(a)):
            mutated = self.rescan()
        self.assertNotEqual(mutated['address']['direct_resources']['sample.scalar'], ['address'])
        self.assertEqual(mutated['write_field'], self.rows['write_field'])

    def test_unknown_member_cannot_be_silently_skipped(self):
        ast = copy.deepcopy(self.ast)
        for node, _ in TOOL.walk(ast):
            if node['kind'] == 'MemberExpr':
                node['referencedMemberDecl'] = 'missing-field-id'
                break
        with self.assertRaisesRegex(ValueError, 'member declaration not resolved'):
            TOOL.scan(ast, FIXTURE, self.inv.SourceMap(FIXTURE))


class PhysicalInventoryIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.actual = TOOL.collect()

    def test_report_reproduces_without_rewriting(self):
        self.assertEqual(self.actual, json.loads((ROOT / TOOL.REPORT).read_text()))
        self.assertEqual(self.actual['summary']['functions'], 94)
        self.assertFalse(self.actual['proof_coverage_credit'])

    def test_tick_requires_fields_not_always_owned_by_selected_record_layout(self):
        tick = next(f for f in self.actual['functions'] if f['name'] == 'OSTimeTick')
        self.assertIn('read', tick['direct_resources']['os_tcb.OSTCBNext'])
        self.assertIn('read', tick['direct_resources']['os_tcb.OSTCBDly'])
        self.assertIn('write', tick['direct_resources']['os_tcb.OSTCBStatPend'])
        self.assertEqual(self.actual['record_layouts']['os_tcb']['fields']['OSTCBDly']['offset'], 44)
        self.assertEqual(self.actual['record_layouts']['os_tcb']['fields']['OSTCBStatPend']['offset'], 49)
        self.assertEqual(self.actual['record_layouts']['os_tcb']['fields']['OSTCBNext']['offset'], 20)
        self.assertEqual(self.actual['record_layouts']['os_tcb']['size'], 56)

    def test_no_unclassified_sites_in_this_configured_program(self):
        self.assertNotIn('unclassified', self.actual['summary']['modes'])
        self.assertNotIn('subobject_unresolved', self.actual['summary']['modes'])
        self.assertEqual(sum(self.actual['summary']['modes'].values()), 1007)

    def test_gap_countermodel_actual_compilation_kernel_and_assumptions(self):
        log = ROOT / 'audit/logs/stage27-physical-access'
        proof = json.loads((log / 'proof-result.json').read_text())
        self.assertTrue(proof['passed'])
        for item in proof['commands']:
            self.assertEqual(item['exit_code'], 0)
        for path, digest in proof['retained_input_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), digest, path)
        source = (ROOT / 'audit/probes/V293PhysicalInvariantGapProbe.v').read_text()
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b', source))
        blocks = (log / 'gap-probe03-coqc.log').read_text().split('Axioms:\n')[1:]
        self.assertEqual(len(blocks), 5)
        for block in blocks:
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s*:', block, re.M)),
                             {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'})
        self.assertFalse(proof['source_only_whole_repository_rebuild_claimed'])

    def test_frozen_identity_drift_rejected_before_scan(self):
        original = TOOL.load
        freeze = original('freeze-v293-source.py')
        frozen, inventory = freeze.collect(ROOT)
        frozen['source_identity_sha256'] = '0' * 64
        with patch.object(freeze, 'collect', return_value=(frozen, inventory)):
            with patch.object(TOOL, 'load', side_effect=lambda n: freeze if n == 'freeze-v293-source.py' else original(n)):
                with self.assertRaisesRegex(ValueError, 'frozen source identity drift'):
                    TOOL.collect()


if __name__ == '__main__':
    unittest.main()
