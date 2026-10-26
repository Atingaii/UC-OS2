"""Single-factor rejection tests for the restricted source correspondence seam."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('functions', ROOT / 'scripts/check-v293-functions.py')
FUNCTIONS = importlib.util.module_from_spec(spec)
spec.loader.exec_module(FUNCTIONS)


def fixture():
    literal = {'kind': 'IntegerLiteral', 'type': {'qualType': 'unsigned int'}, 'value': '29300'}
    paren = {'kind': 'ParenExpr', 'type': {'qualType': 'unsigned int'}, 'inner': [literal]}
    cast = {'kind': 'ImplicitCastExpr', 'castKind': 'IntegralCast',
            'type': {'qualType': 'INT16U', 'desugaredQualType': 'unsigned short'}, 'inner': [paren]}
    ret = {'kind': 'ReturnStmt', 'inner': [cast]}
    body = {'kind': 'CompoundStmt', 'inner': [ret]}
    return {'kind': 'FunctionDecl', 'name': 'OSVersion', 'type': {'qualType': 'INT16U (void)'},
            'inner': [body]}


class TranslationTests(unittest.TestCase):
    def setUp(self):
        self.node = fixture()
        self.body = self.node['inner'][0]
        self.ret = self.body['inner'][0]
        self.cast = self.ret['inner'][0]
        self.literal = self.cast['inner'][0]['inner'][0]

    def reject(self, fragment):
        with self.assertRaisesRegex(ValueError, fragment):
            FUNCTIONS.decode_osversion(self.node)

    def test_exact_shape_emits_the_committed_model(self):
        value = FUNCTIONS.decode_osversion(self.node)
        self.assertEqual(value, 29300)
        self.assertEqual(FUNCTIONS.emit_osversion(value), (ROOT / FUNCTIONS.CODE).read_text())

    def test_changed_literal_changes_emission_instead_of_being_hardcoded(self):
        self.literal['value'] = '29301'
        self.assertIn('Int.repr 29301', FUNCTIONS.emit_osversion(FUNCTIONS.decode_osversion(self.node)))

    def test_extra_side_effect_is_not_discarded(self):
        self.body['inner'].insert(0, {'kind': 'CallExpr'})
        self.reject('CompoundStmt')

    def test_added_parameter_is_rejected(self):
        self.node['inner'].insert(0, {'kind': 'ParmVarDecl'})
        self.reject('FunctionDecl')

    def test_changed_signature_is_rejected(self):
        self.node['type']['qualType'] = 'INT32U (void)'
        self.reject('signature')

    def test_static_linkage_is_rejected(self):
        self.node['storageClass'] = 'static'
        self.reject('linkage')

    def test_signed_return_is_not_confused_with_unsigned(self):
        self.cast['type']['desugaredQualType'] = 'short'
        self.reject('return conversion')

    def test_missing_narrowing_is_rejected(self):
        self.ret['inner'] = copy.deepcopy(self.cast['inner'])
        self.reject('ImplicitCastExpr')

    def test_non_integral_cast_is_rejected(self):
        self.cast['castKind'] = 'BitCast'
        self.reject('return conversion')

    def test_signed_literal_is_rejected(self):
        self.literal['type']['qualType'] = 'int'
        self.reject('literal type')

    def test_overflow_literal_is_rejected(self):
        self.literal['value'] = str(2**32)
        self.reject('UINT32 literal')

    def test_nonliteral_return_is_rejected(self):
        self.literal['kind'] = 'DeclRefExpr'
        self.reject('IntegerLiteral')

    def test_ast_attribute_is_not_silently_erased(self):
        self.node['inner'].append({'kind': 'NoReturnAttr'})
        self.reject('FunctionDecl')


if __name__ == '__main__':
    unittest.main()
