(* Independent concrete address controls and an adversarial GoodI check.
   Conditional body derivations do not establish an executable kernel. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSiteFreshness.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.audit.probes.V293TaskCreateJointSharedProbe.
Require Import CertiOS.audit.probes.V293TCBSharedContractProbe.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.audit.probes.V293InitChainProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition SFGuard reserved := negb(existsb(fun node=>tidspec.beq node reserved)
 (V293_tcb_table_sites 82%positive)).
Lemma SFReservedAccepted : SFGuard SCReserved=true.
Proof. reflexivity. Qed.
Lemma SFReservedOutside : ~In SCReserved(V293_tcb_table_sites 82%positive).
Proof. vm_compute;intuition congruence. Qed.
Lemma SFAllThirteenDistinct : forall node,
 In node(V293_tcb_table_sites 82%positive) -> node<>SCReserved.
Proof.
 intros node Member Equal. subst node.
 vm_compute in Member;intuition congruence.
Qed.
(* Single factor: only reserved changes; catalogue, guard, code remain fixed. *)
Lemma SFAliasRejected : SFGuard(82%positive,Int.zero)=false.
Proof. reflexivity. Qed.
Lemma SFAliasMember : In(82%positive,Int.zero)(V293_tcb_table_sites 82%positive).
Proof. left;reflexivity. Qed.
Lemma SFAliasHasNoOutside : ~ (~In(82%positive,Int.zero)(V293_tcb_table_sites 82%positive)).
Proof. intro Outside;apply Outside;left;reflexivity. Qed.
(* Different blocks are sufficient, not necessary: offset1 is not a record start. *)
Lemma SFSameBlockAccepted : SFGuard(82%positive,Int.one)=true.
Proof. reflexivity. Qed.
Lemma SFSameBlockOutside : ~In(82%positive,Int.one)(V293_tcb_table_sites 82%positive).
Proof. vm_compute;intuition congruence. Qed.
Definition SFPhysicalInv := V293_create_joint_inv 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive 182%positive SCReserved.
(* Actual original initialization supplies a nonempty physical core. It contains
   no abstract-state ownership, so the first GoodI obligation cannot hold. *)
Theorem SFPhysicalInvNotGoodI : forall sd li,~GoodI SFPhysicalInv sd li.
Proof.
 intros sd li GI.
 destruct(CPActualInitialization kstop)as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&Joint&FR&FT).
 apply sat_split in Joint.
 destruct Joint as(m1&m2&o1&o2&JM&JO&Core&Frame).
 change(join o1 o2 (emp:osabst))in JO.
 apply map_join_pos in JO;destruct JO as[E1 E2];subst o1.
 assert(InvState:(ChainGE,ChainCaller,m1,(fun _=>false),(false,nil,nil),(emp:osabst),spec_done None)
  |= starinv_noisr SFPhysicalInv 0%nat(S INUM)).
 { apply V293_create_joint_noisr_core. exact Core. }
 destruct GI as[NoExtension _].
 assert(Extension:join(emp:osabst)(sig curtid(oscurt FPTid))(sig curtid(oscurt FPTid))).
 { apply map_join_comm;apply map_join_emp. }
 pose proof(NoExtension _ _ _ _ _ InvState Extension)as Empty.
 assert(Value:get(sig curtid(oscurt FPTid))curtid=Some(oscurt FPTid))by apply map_get_sig.
 rewrite Empty in Value. change(None=Some(oscurt FPTid))in Value. discriminate.
Qed.
