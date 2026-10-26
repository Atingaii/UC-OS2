"""Assumption-output parsing must retain real axioms, not the output header."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('memory_trust', ROOT / 'scripts/check-memory-trust.py')
TRUST = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TRUST)


class AssumptionParserTests(unittest.TestCase):
    def test_actual_header_and_multiline_types_are_not_axiom_names(self):
        text = '''Axioms:
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type), A -> A
Classical_Prop.classic : forall P : Prop, P \/ ~ P
'''
        self.assertEqual(TRUST.assumptions(text), TRUST.ALLOWED)

    def test_closed_context_has_no_axioms(self):
        self.assertEqual(TRUST.assumptions('Closed under the global context\n'), set())

    def test_bad_axiom_is_not_silently_filtered(self):
        actual = TRUST.assumptions('Axioms:\nBaselineMemory.MemoryNotFull : forall m, ~ FullMemory m\n')
        self.assertEqual(actual - TRUST.ALLOWED, {'BaselineMemory.MemoryNotFull'})

    def test_unknown_axiom_fails_closed(self):
        with self.assertRaises(ValueError):
            TRUST.check_assumptions('Axioms:\nUnexpected.escape : False\n', TRUST.FRAMEWORK_ALLOWED)

    def test_unicode_axiom_cannot_escape_the_allowlist(self):
        with self.assertRaises(ValueError):
            TRUST.check_assumptions('Axioms:\nα : False\n', TRUST.FRAMEWORK_ALLOWED)

    def test_universe_annotated_axiom_cannot_be_silently_dropped(self):
        with self.assertRaises(ValueError):
            TRUST.check_assumptions('Axioms:\nUnsafe.escape@{u} : False\n', TRUST.FRAMEWORK_ALLOWED)

    def test_bad_axiom_fails_even_if_added_to_allowlist(self):
        with self.assertRaises(ValueError):
            TRUST.check_assumptions('Axioms:\nMemoryNotFull : False\n', {'MemoryNotFull'})

    def test_primed_qualified_names_are_not_lost(self):
        self.assertEqual(TRUST.assumptions("Axioms:\nUnsafe.escape' : False\n"), {"Unsafe.escape'"})

    def test_new_representation_does_not_inherit_framework_exceptions(self):
        with self.assertRaises(ValueError):
            TRUST.check_assumptions('Axioms:\nLibTactics.inj_pair2 : True\n', TRUST.ALLOWED)

    def test_legacy_map_axioms_are_not_framework_exceptions(self):
        for name in ['Coqlib.extensionality', 'auxdef.TMSpecMod.extensionality',
                     'auxdef.TOSpecMod.extensionality']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                TRUST.check_assumptions(f'Axioms:\n{name} : True\n', TRUST.FRAMEWORK_ALLOWED)

    def test_historical_failure_remains_frozen(self):
        self.assertEqual(TRUST.sha(ROOT / TRUST.HISTORY), TRUST.HISTORY_SHA256)
