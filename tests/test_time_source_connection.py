"""可执行AST拒绝检查；Coq等式/组件证据单独检查，不以文本代替证明。"""
from copy import deepcopy
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage337-time-source-connection'
P = 'certiucos/v293/proofs/V293TimeSourceAPI.v'
C = 'certiucos/v293/code/V293TimeSource.v'
Q = 'audit/probes/V293TimeSourceAPIProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def seam():
    spec = importlib.util.spec_from_file_location('time_source_tests', R / 'scripts/v293-time-source.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def nodes():
    return json.loads((D / 'configured-ast.json').read_text())


def walk(n):
    yield n
    for c in n.get('inner', []):
        yield from walk(c)


class TimeSourceConnectionTests(unittest.TestCase):
    def test_original_ast_emits_complete_functions(self):
        m = seam()
        sources = {n['name']: m.decode(n) for n in nodes()}
        self.assertEqual(sources, {'OSTimeGet': 'OSTime', 'OSTimeSet': 'ticks'})
        self.assertEqual((R / C).read_text(), m.emit(sources))

    def test_unknown_semantic_fields_fail_closed(self):
        for name, value in [('storageClass', 'static'), ('tlsKind', 'static'), ('inline', True)]:
            for n in nodes():
                n[name] = value
                with self.assertRaises(ValueError):
                    seam().decode(n)

    def test_local_reference_identity_checked(self):
        for n in nodes():
            reference = next(x for x in walk(n) if x.get('referencedDecl', {}).get('name') == 'cpu_sr')
            reference['referencedDecl']['id'] = 'different-object'
            with self.assertRaisesRegex(ValueError, 'identity mismatch'):
                seam().decode(n)

    def test_volatile_global_and_uint32_width_checked(self):
        for n in nodes():
            for name in ['OSTime', 'ticks']:
                candidate = deepcopy(n)
                reference = next(x for x in walk(candidate)
                                 if x.get('referencedDecl', {}).get('name') == name)
                reference['type']['desugaredQualType'] = 'unsigned long'
                with self.assertRaises(ValueError):
                    seam().decode(candidate)

    def test_initializer_and_declaration_order_checked(self):
        for n in nodes():
            literal = next(x for x in walk(n) if x.get('kind') == 'IntegerLiteral')
            literal['value'] = '1'
            with self.assertRaises(ValueError):
                seam().decode(n)
        getter = nodes()[0]
        body = getter['inner'][0]['inner']
        body[0], body[1] = body[1], body[0]
        with self.assertRaises(ValueError):
            seam().decode(getter)

    def test_marker_identity_and_same_saved_address_checked(self):
        for n in nodes():
            calls = [x for x in walk(n) if x.get('kind') == 'CallExpr']
            calls[-1]['inner'][0]['inner'][0]['referencedDecl']['name'] = 'V293_EnterCritical'
            with self.assertRaises(ValueError):
                seam().decode(n)
        for n in nodes():
            address = next(x for x in walk(n) if x.get('kind') == 'UnaryOperator')
            address['inner'][0]['referencedDecl']['name'] = 'ticks'
            with self.assertRaises(ValueError):
                seam().decode(n)

    def test_extra_or_reordered_statements_rejected(self):
        for n in nodes():
            body = n['inner'][-1]['inner']
            body.append({'kind': 'NullStmt'})
            with self.assertRaises(ValueError):
                seam().decode(n)
        for n in nodes():
            body = n['inner'][-1]['inner']
            calls = [i for i, x in enumerate(body) if x['kind'] == 'CallExpr']
            i = calls[0]
            body[i], body[i+1] = body[i+1], body[i]
            with self.assertRaises(ValueError):
                seam().decode(n)

    def test_fresh_source_and_late_mutant_gates_repeated(self):
        for repeat in [1, 2]:
            root = D / f'replay-{repeat}'
            report = json.loads((root / 'report.json').read_text())
            self.assertTrue(report['passed'] and report['gcc_clang_agreement'])
            self.assertEqual(report['sources'], {'OSTimeGet': 'OSTime', 'OSTimeSet': 'ticks'})
            for path, h in report['inputs'].items():
                self.assertEqual(sha(R / path), h)
            checks = report['checks']
            self.assertEqual([c['exit'] for c in checks], [0, 1, 1])
            self.assertTrue(all(c['decoder_accepted'] for c in checks))
            for c in checks:
                self.assertEqual(sha(root / (c['label'] + '.v.snapshot.txt')), c['snapshot_sha256'])
                if c['exit']:
                    log = (root / (c['label'] + '.log')).read_text()
                    self.assertIn(f"line {c['expected_equality_line']}, characters", log)
                    self.assertIn('Unable to unify', log)
                    self.assertNotEqual(c['code_sha256'], checks[0]['code_sha256'])
            for row in report['locations']:
                self.assertEqual(sha(root / (row['name'] + '.configured.c.snapshot.txt')),
                                 row['preprocessed_definition_sha256'])
                self.assertEqual(sha(root / (row['name'] + '.source.c.snapshot.txt')),
                                 row['source_lines_sha256'])

    def test_prospective_protocol_and_only_rhs_changed(self):
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertTrue(protocol['prospective'])
        self.assertIn('change only the copy RHS source variable', protocol['ablation']['factor'])
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        pairs = [('OSTimeGet', b'ticks = OSTime;', b'ticks = ticks;'),
                 ('OSTimeSet', b'OSTime = ticks;', b'OSTime = OSTime;')]
        root = D / 'replay-1'
        for name, old, new in pairs:
            original = (root / (name + '.configured.c.snapshot.txt')).read_bytes()
            mutant = (root / (name + '.mutant.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(original.count(old), 1)
            self.assertEqual(original.replace(old, new), mutant)
            positive = (root / 'positive.v.snapshot.txt').read_text()
            negative = (root / ('mutant-' + name + '.v.snapshot.txt')).read_text()
            self.assertEqual(positive.split('Theorem checked_get', 1)[1],
                             negative.split('Theorem checked_get', 1)[1])

    def test_component_uses_real_builders_and_same_invariant(self):
        s = (R / P).read_text()
        self.assertIn('eapply V293_TimeGet_api_contract; eassumption', s)
        self.assertIn('eapply V293_TimeSet_api_contract; eassumption', s)
        self.assertIn('V293_time_names_good', s)
        q = (R / Q).read_text()
        self.assertIn('Theorem TSbuilders_nonempty', q)
        self.assertIn('BuildPreA\'', q)
        self.assertIn('BuildRetA\'', q)
        for p in [C, P, Q]:
            text = (R / p).read_text()
            self.assertNotRegex(text, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            if p != Q:
                self.assertNotIn('Require Import CertiOS.audit.', text)

    def test_repeat_compilation_and_recursive_trust(self):
        for name, p in [('code', C), ('proof', P), ('probe', Q)]:
            for i in [1, 2]:
                row = json.loads((D / f'stable-{name}-{i}.json').read_text())
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['source_sha256'], sha(R / p))
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], 8)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        inputs = json.loads((D / 'trust-inputs.json').read_text())
        for p in [C, P, Q]:
            self.assertEqual(inputs[p], sha(R / p))

    def test_old_inputs_preserved_and_claims_bounded(self):
        baseline = json.loads((D / 'baseline.json').read_text())
        self.assertEqual([p for p, h in baseline.items() if not (R / p).is_file() or sha(R / p) != h], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        prefix = (D / '_CoqProject.baseline').read_bytes() + (C + '\n' + P + '\n').encode()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(prefix))
        self.assertTrue(all(line.startswith('certiucos/v293/') and line.endswith('.v')
                            for line in current[len(prefix):].decode().splitlines()))
        doc = (R / 'audit/STAGE337_TIME_SOURCE_CONNECTION.md').read_text()
        for term in ['不是经验证C前端', 'ADR0005', '不是运行时反例', 'GOOD_OS', 'K1–K4',
                     'uCOS3', '两个CPU hook仍缺实现', '总目标保持active', '旧覆盖清单不改写']:
            self.assertIn(term, doc)
