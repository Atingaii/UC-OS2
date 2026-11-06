"""不调度完整调用的结构、边界、来源和机器检查证据。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / "audit/logs/stage297-exit-no-dispatch"
P = "certiucos/v293/proofs/V293ExitNoDispatchCallTaskSim.v"
Q = "audit/probes/V293ExitNoDispatchCallTaskSimProbe.v"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class ExitNoDispatchCallTests(unittest.TestCase):
    def test_fixed_identity_and_project_append(self):
        ident = json.loads((D / "source-identity.json").read_text())
        for p, digest in ident["files"].items():
            self.assertEqual(sha(R / p), digest, p)
        lines = (R / "csrc/upstream/v2.93.01/checkout/Source/os_core.c").read_text().splitlines()
        for number, anchor in ident["line_anchors"].items():
            self.assertEqual(lines[int(number) - 1].strip(), anchor)
        self.assertEqual((R / "_CoqProject").read_bytes(),
                         (D / "_CoqProject.baseline").read_bytes() + ("\n" + P + "\n").encode())
        self.assertNotIn(Q, (R / "_CoqProject").read_text())
        self.assertEqual((D / "protocol.sha256").read_text().split(),
                         [sha(D / "protocol.json"), "protocol.json"])

    def test_complete_public_interface_not_continuation_oracle(self):
        source = (R / P).read_text()
        self.assertEqual(re.findall(r"^Theorem (\w+)", source, re.M),
                         ["V293_exit_no_dispatch_client_call_TaskSim"])
        public = source.split("Theorem V293_exit_no_dispatch_client_call_TaskSim :", 1)[1].split("Proof.", 1)[0]
        self.assertEqual(public.count("TaskSim("), 1)
        self.assertEqual(public.count("curs(scall f nil)"), 2)
        self.assertIn("fun _:vallist=>spec_done None", public)
        self.assertIn("V293_exit_quiet_resource", public)
        self.assertIn(r"2<=n \/ 0<l", public)
        self.assertIn("RDYINV G t **LINV", public)
        self.assertNotRegex(public, r"\b(?:cstep|store|load|evalval|evaltype|evaladdr|fresh|InOS)\b")
        self.assertNotRegex(source, r"\b(?:Definition|spec_choice|Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b")
        self.assertIn("V293_storage_split", source)
        self.assertIn("V293_storage_append", source)
        self.assertIn("V293_nested_prefix_TaskSim", source)
        self.assertIn("V293_locked_prefix_TaskSim", source)
        self.assertIn("V293_exit_saved_successor", source)
        self.assertIn("V293_storage_pending_TaskSim", source)

    def test_byte_domain_and_single_factor_decision(self):
        # 独立核对 C 的饱和递减后双 guard；这不是完整 Coq 调用证明的替代。
        checked = 0
        changed = 0
        for n in range(256):
            after = n - 1 if n > 0 else 0
            for lock in range(256):
                blocked = after != 0 or lock != 0
                self.assertEqual(blocked, n >= 2 or lock > 0)
                if lock == 0:
                    self.assertEqual(blocked, n >= 2)
                checked += 1
            changed += (after == 0 and 1 != 0) != (after == 0 and 0 != 0)
        self.assertEqual(checked, 65536)
        self.assertEqual(changed, 2)
        self.assertFalse(0 >= 2 or 0 > 0)
        self.assertFalse(1 >= 2 or 0 > 0)

    def test_existing_nonempty_heap_same_api_and_invariant(self):
        source = (R / Q).read_text()
        self.assertNotRegex(source, re.compile(r"^Definition \w*(?:memory|Memory|heap|Heap)\w*", re.M))
        for name in ["NDsame_invariant", "NDnested_original_input_call",
                     "NDquiet_original_API_call", "NDlock_single_factor_complete_call"]:
            self.assertIn(name, source)
        self.assertEqual(source.count("(RCprogram,QCspec)(curs(scall 114%Z nil)"), 4)
        self.assertIn("pose proof(ACbase n NB)", source)
        self.assertIn("store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval l)", source)
        self.assertIn("get Ml(b,i)=get(ACmemory n)(b,i)", source)
        self.assertIn("V293_byte_type l LB", source)
        self.assertIn("V293_storebytes_outside", source)
        self.assertNotRegex(source, r"\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b")

    def test_stable_compiles_and_all_roots_kernel_checked(self):
        stable = json.loads((D / "stable-compiles.json").read_text())
        roots = []
        for p in [P, Q]:
            names = re.findall(r"^(?:Lemma|Theorem|Corollary) (\w+)\s*:", (R / p).read_text(), re.M)
            roots.extend(Path(p).stem + "." + name for name in names)
            row = stable[p]
            self.assertEqual(row["sha256"], sha(R / p))
            self.assertEqual(row["roots"], names)
            self.assertEqual(len(row["runs"]), 2)
            for run in row["runs"]:
                self.assertEqual(run["exit"], 0)
                self.assertEqual(run["initial_source_sha256"], row["sha256"])
                self.assertEqual(run["source_sha256"], row["sha256"])
        trust = json.loads((D / "trust.json").read_text())
        self.assertEqual(len(roots), 12)
        self.assertEqual(trust["roots"], roots)
        self.assertTrue(trust["passed"] and trust["recursive"])
        self.assertTrue(all(command["exit"] == 0 for command in trust["commands"]))
        self.assertLessEqual(set(trust["assumptions"]),
                             {"Classical_Prop.classic", "FunctionalExtensionality.functional_extensionality_dep"})


if __name__ == "__main__":
    unittest.main()
