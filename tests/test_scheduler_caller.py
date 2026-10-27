"""Single-factor source-seam tests; no fixture is used by the live source gate."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

CALLER = load('v293-scheduler-caller.py')
SCHED = load('v293-scheduler-source.py')


class SchedulerCallerTranslationTests(unittest.TestCase):
    def setUp(self):
        data = json.loads((ROOT / 'tests/fixtures/ossched-ast.json').read_text())
        self.node = data['function']
        self.declarations = {d['id']: d for d in data['declarations']}
        self.body = self.node['inner'][0]['inner']
        self.unlocked = self.body[2]['inner'][1]['inner'][0]['inner'][1]['inner']

    def find(self, kind, **fields):
        return next(n for n in CALLER.walk(self.node) if n.get('kind') == kind
                    and all(n.get(k) == v for k, v in fields.items()))

    def ref(self, name):
        return next(n for n in CALLER.walk(self.node) if n.get('referencedDecl', {}).get('name') == name)

    def reject(self):
        with self.assertRaises(ValueError): CALLER.decode(self.node, SCHED)

    def test_actual_whole_shape_and_references(self):
        CALLER.decode(self.node, SCHED)
        CALLER.check_references(self.node, self.declarations)
        self.assertEqual(CALLER.EMISSION, (ROOT / CALLER.CODE).read_text())

    def test_extra_statement_is_not_silently_dropped(self):
        self.unlocked.append({'kind': 'NullStmt'}); self.reject()

    def test_call_and_pointer_update_cannot_be_reordered(self):
        self.unlocked[0], self.unlocked[1] = self.unlocked[1], self.unlocked[0]; self.reject()

    def test_wrong_callee(self):
        self.ref('OS_SchedNew')['referencedDecl']['name'] = 'Other'; self.reject()

    def test_wrong_pointer_table_extent(self):
        n = self.ref('OSTCBPrioTbl'); n['type']['qualType'] = 'OS_TCB *[12]'
        n['referencedDecl']['type']['qualType'] = 'OS_TCB *[12]'; self.reject()

    def test_wrong_pointer_target(self):
        self.ref('OSTCBHighRdy')['referencedDecl']['name'] = 'OSTCBCur'; self.reject()

    def test_wrong_priority_index(self):
        self.ref('OSPrioHighRdy')['referencedDecl']['name'] = 'OSPrioCur'; self.reject()

    def test_missing_pointer_array_decay(self):
        self.find('ImplicitCastExpr', castKind='ArrayToPointerDecay')['castKind'] = 'NoOp'; self.reject()

    def test_interrupt_guard_is_checked(self):
        self.ref('OSIntNesting')['referencedDecl']['name'] = 'OSLockNesting'; self.reject()

    def test_locked_guard_is_checked(self):
        self.body[2]['inner'][1]['inner'][0]['inner'][0]['opcode'] = '!='; self.reject()

    def test_critical_wrapper_not_treated_as_empty_macros(self):
        del self.body[1]; self.reject()

    def test_critical_boundary_requires_saved_token_address(self):
        self.find('UnaryOperator', opcode='&')['opcode'] = '*'; self.reject()

    def test_token_is_initialized_to_zero(self):
        self.find('IntegerLiteral')['value'] = '1'; self.reject()

    def test_token_initialization_kind_is_checked(self):
        self.find('VarDecl')['init'] = 'call'; self.reject()

    def test_token_width_is_checked(self):
        self.find('VarDecl')['type']['desugaredQualType'] = 'unsigned short'; self.reject()

    def test_postfix_counter_is_not_confused_with_prefix(self):
        self.find('UnaryOperator', opcode='++')['isPostfix'] = False; self.reject()

    def test_added_attribute_is_rejected(self):
        self.node['inner'].append({'kind': 'NoReturnAttr'}); self.reject()

    def test_forged_reference_identity_is_rejected(self):
        self.ref('OSTCBPrioTbl')['referencedDecl']['id'] = 'unknown'
        CALLER.decode(self.node, SCHED)  # spelling/type alone still match
        with self.assertRaisesRegex(ValueError, 'actual declaration'):
            CALLER.check_references(self.node, self.declarations)

    def test_same_name_wrong_declaration_kind_is_rejected(self):
        n = self.ref('OS_SchedNew'); self.declarations[n['referencedDecl']['id']]['kind'] = 'VarDecl'
        with self.assertRaisesRegex(ValueError, 'actual declaration'):
            CALLER.check_references(self.node, self.declarations)
