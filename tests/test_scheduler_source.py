"""Single-factor tests of the restricted scheduler source seam, not C proofs."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('scheduler', ROOT / 'scripts/v293-scheduler-source.py')
SCHED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SCHED)


def nodes(node):
    yield node
    for child in node.get('inner', []):
        yield from nodes(child)


class SchedulerTranslationTests(unittest.TestCase):
    def setUp(self):
        self.node = json.loads((ROOT / 'tests/fixtures/osschednew-ast.json').read_text())['function']

    def find(self, kind, **fields):
        return next(n for n in nodes(self.node) if n.get('kind') == kind
                    and all(n.get(k) == v for k, v in fields.items()))

    def reject(self):
        with self.assertRaises(ValueError):
            SCHED.decode(self.node)

    def test_actual_ast_emits_committed_program(self):
        self.assertEqual(SCHED.decode(self.node), 3)
        self.assertEqual(SCHED.emit_code(3), (ROOT / SCHED.CODE).read_text())

    def test_shift_mutation_reaches_semantics_instead_of_being_hardcoded(self):
        self.find('IntegerLiteral')['value'] = '2'
        self.assertEqual(SCHED.decode(self.node), 2)
        self.assertIn('Int.repr 2', SCHED.emit_code(SCHED.decode(self.node)))

    def test_missing_integer_promotion(self):
        node = self.find('ImplicitCastExpr', castKind='IntegralCast')
        child = copy.deepcopy(node['inner'][0])
        node.clear(); node.update(child)
        self.reject()

    def test_wrong_narrowing(self):
        self.find('CStyleCastExpr')['castKind'] = 'BitCast'
        self.reject()

    def test_missing_array_decay(self):
        self.find('ImplicitCastExpr', castKind='ArrayToPointerDecay')['castKind'] = 'NoOp'
        self.reject()

    def test_wrong_array_extent(self):
        # Find the actual table use, not local y.
        node = next(n for n in nodes(self.node) if n.get('referencedDecl', {}).get('name') == 'OSUnMapTbl')
        node['type']['qualType'] = 'const INT8U[255]'
        node['referencedDecl']['type']['qualType'] = 'const INT8U[255]'
        self.reject()

    def test_reference_type_must_match_declaration(self):
        self.find('DeclRefExpr')['referencedDecl']['type']['qualType'] = 'int'
        self.reject()

    def test_wrong_referenced_name(self):
        self.find('DeclRefExpr')['referencedDecl']['name'] = 'another_global'
        self.reject()

    def test_wrong_declaration_kind(self):
        self.find('DeclRefExpr')['referencedDecl']['kind'] = 'FunctionDecl'
        self.reject()

    def test_extra_side_effect(self):
        self.find('CompoundStmt')['inner'].append({'kind': 'CallExpr'})
        self.reject()

    def test_added_parameter(self):
        self.node['inner'].insert(0, {'kind': 'ParmVarDecl'})
        self.reject()

    def test_removed_static_linkage(self):
        del self.node['storageClass']
        self.reject()

    def test_added_attribute(self):
        self.node['inner'].append({'kind': 'NoReturnAttr'})
        self.reject()

    def test_added_local_initializer(self):
        self.find('VarDecl')['inner'] = [{'kind': 'IntegerLiteral', 'value': '0'}]
        self.reject()

    def test_out_of_range_shift(self):
        self.find('IntegerLiteral')['value'] = '32'
        self.reject()

    def test_signed_shift_literal(self):
        self.find('IntegerLiteral')['type']['qualType'] = 'int'
        self.reject()


class SchedulerTableTests(unittest.TestCase):
    def setUp(self):
        # Hand-build only this small initializer grammar; the live gate extracts
        # and compares the real initializer from both configured preprocessors.
        self.values = [0 if n == 0 else (n & -n).bit_length() - 1 for n in range(256)]
        self.entries = [{'kind': 'ImplicitCastExpr', 'castKind': 'IntegralCast',
                         'type': {'qualType': 'INT8U', 'desugaredQualType': 'unsigned char'},
                         'inner': [{'kind': 'IntegerLiteral', 'type': {'qualType': 'unsigned int'},
                                    'value': str(v)}]} for v in self.values]
        self.table = {'kind': 'VarDecl', 'name': 'OSUnMapTbl',
                      'type': {'qualType': 'const INT8U[256]'},
                      'inner': [{'kind': 'InitListExpr', 'inner': self.entries}]}
        self.ast = {'inner': [self.table]}

    def reject(self):
        with self.assertRaises(ValueError):
            SCHED.extract_table(self.ast)

    def test_initializer_emits_committed_table(self):
        self.assertEqual(SCHED.extract_table(self.ast), self.values)
        self.assertEqual(SCHED.emit_table(self.values), (ROOT / SCHED.TABLE).read_text())

    def test_wrong_value_is_emitted_for_downstream_coq_rejection(self):
        self.entries[16]['inner'][0]['value'] = '3'
        extracted = SCHED.extract_table(self.ast)
        self.assertEqual(extracted[16], 3)
        self.assertNotEqual(SCHED.emit_table(extracted), (ROOT / SCHED.TABLE).read_text())

    def test_declaration_without_definition(self):
        self.table['inner'] = []
        self.reject()

    def test_two_definitions(self):
        self.ast['inner'].append(copy.deepcopy(self.table))
        self.reject()

    def test_incomplete_initializer(self):
        self.entries.pop()
        self.reject()

    def test_wrong_extent(self):
        self.table['type']['qualType'] = 'const INT8U[255]'
        self.reject()

    def test_extra_attribute(self):
        self.table['inner'].append({'kind': 'AlignedAttr'})
        self.reject()

    def test_wrong_conversion(self):
        self.entries[16]['castKind'] = 'BitCast'
        self.reject()

    def test_signed_destination(self):
        self.entries[16]['type']['desugaredQualType'] = 'signed char'
        self.reject()

    def test_negative_literal(self):
        self.entries[16]['inner'][0]['value'] = '-1'
        self.reject()

    def test_overflow_literal(self):
        self.entries[16]['inner'][0]['value'] = '256'
        self.reject()

    def test_literal_with_hidden_child(self):
        self.entries[16]['inner'][0]['inner'] = [{'kind': 'CallExpr'}]
        self.reject()
