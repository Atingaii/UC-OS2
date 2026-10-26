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
