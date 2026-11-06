(* Literal entry for the direct delay InfRules; empty test LocalInv only.
   The original operational expiry fixture is an independent negative oracle. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.audit.probes.V293TimeTickExpiryProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition DHtid : tid := (81%positive,Int.repr 8).
Definition DHge : env := set ExpiryGlobal OSTCBCur (94%positive,Tptr Tvoid).
Definition DHcurrent : mem := V293_encoded_memory 94%positive 0 false (encode_val (Tptr Tvoid) (Vptr DHtid)).
Definition DHbindings := Alvarenv 901%Z (Tptr V293_tcb_type) (70%positive,0%Z) //\\
 A_notin_lenv 902%Z //\\ Agvarenv 902%Z (Tarray Tint8 2) (93%positive,0%Z) //\\
 A_notin_lenv 903%Z //\\ Agvarenv 903%Z Tint8 (92%positive,0%Z).
Definition DHR := DHbindings ** (CurTid DHtid ** LINV V293_witness_li DHtid [] ** ExpiryFrame).
Definition DHcells d s := V293_tick_expiry_cells 70%positive 81%positive 8%Z
 (81%positive,Int.repr 8) (Int.repr d) TickNext s 7 1 2 92%positive 1 93%positive 128.
Definition DHmemory d s := merge (OwnershipCellsMemory (DHcells d s ++ ExpiryFrameCells)) DHcurrent.
Definition DHstate M : RstateOP := (DHge,TickLocal,M,(fun _=>false),(false,[3],[false]),emp,spec_done None).
Definition DHpre d s := <||spec_done None||> ** V293_rdy_raw_cells (DHcells d s) DHR.
Definition DHpost d s := <||spec_done None||> ** V293_rdy_raw_cells
 (V293_tick_expiry_cells 70%positive 81%positive 8%Z (81%positive,Int.repr 8)
 (Int.repr (V293_tick_after_delay d)) TickNext (V293_tick_after_stat d s)
 (V293_tick_after_pend d 7 s) 1 2 92%positive (V293_tick_after_group d s 1 1)
 93%positive (V293_tick_after_row d s 128 2)) DHR.
Lemma DHenv : forall st, st |= DHR -> V293_tick_delay_env 901%Z 902%Z 903%Z
 70%positive 93%positive 92%positive (getgenv st) (getlenv st).
Proof.
 intros st Held. eapply V293_star_env_l;[ |exact Held].
 intros s (Bc&Nr&Gr&Ng&Gg).
 destruct Bc as [b [B [E _]]];inversion E;subst b.
 destruct Gr as [br [R [Er _]]];inversion Er;subst br.
 destruct Gg as [bg [G [Eg _]]];inversion Eg;subst bg.
 destruct Nr as [Nr _]. destruct Ng as [Ng _].
 unfold V293_tick_delay_env. repeat split;try assumption.
 - destruct (get (getlenv s) 902%Z) eqn:V;[exfalso;apply Nr;eexists;exact V|exact V].
 - destruct (get (getlenv s) 903%Z) eqn:V;[exfalso;apply Ng;eexists;exact V|exact V].
Qed.
Lemma DHcur : DHR ==> CurLINV V293_witness_li DHtid.
Proof.
 unfold DHR. apply V293_star_CurLINV_r. intros st Held.
 unfold CurLINV. exists ([]:list logicvar). clear -Held. sep auto.
Qed.
Lemma DHstar : forall m1 m2 m p q,
 join m1 m2 m -> DHstate m1 |= p -> DHstate m2 |= q -> DHstate m |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists (emp:osabst). exists (emp:osabst).
 split;[assumption| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma DHbinding_spatial : DHstate emp |= DHbindings.
Proof.
 unfold DHbindings. repeat split.
 - exists 70%positive. split;[apply map_get_sig| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 93%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros [v E];vm_compute in E;discriminate.
 - exists 92%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
Qed.
Lemma DHcurrent_spatial : DHstate DHcurrent |= CurTid DHtid.
Proof.
 exists Tvoid. exists 94%positive. eapply DHstar with (m1:=emp) (m2:=DHcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 94%positive. split;[apply map_get_set| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma DHlinv_spatial : DHstate emp |= LINV V293_witness_li DHtid [].
Proof.
 unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Lemma DHowned_raw : forall cells R,
 V293_owned_record_cells cells ** R ==> V293_rdy_raw_cells cells R.
Proof.
 induction cells as [ | [[a tp] v] cells IH];intros R st Held.
 - apply astar_l_aemp_elim in Held;exact Held.
 - cbn [V293_owned_record_cells V293_rdy_raw_cells] in *.
   apply astar_assoc_elim in Held. eapply astar_mono;[ |apply IH|exact Held].
   intros s H. unfold V293_owned_record_cell in H. apply astar_l_apure_elim in H;exact (proj2 H).
Qed.
Theorem DHentry : forall d s, s<256 -> DHstate (DHmemory d s) |= DHpre d s.
Proof.
 intros d s S.
 assert (Apart : OwnershipCellsSeparated (DHcells d s ++ ExpiryFrameCells)).
 { vm_compute. repeat split;intros;intuition congruence. }
 assert (Valid : Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true)
   (DHcells d s ++ ExpiryFrameCells)).
 { repeat constructor;try reflexivity. exact (V293_byte_type s S). }
 pose proof (OwnershipCellsSpatial _ Apart Valid DHge TickLocal) as Owned.
 assert (Rebased : DHstate (OwnershipCellsMemory (DHcells d s ++ ExpiryFrameCells)) |=
   V293_owned_record_cells (DHcells d s) ** ExpiryFrame).
 { apply V293_tick_cells_append. unfold DHstate. eapply TickCellsRebase;exact Owned. }
 assert (Both : DHstate (DHmemory d s) |=
   (V293_owned_record_cells (DHcells d s) ** ExpiryFrame) ** CurTid DHtid).
 { eapply DHstar;[ |exact Rebased|apply DHcurrent_spatial].
   apply map_join_merge;apply map_disjoint;intros [b i].
   destruct (Pos.eq_dec b 94%positive) as [E|E].
   - subst b. left. apply OwnershipCellsOutside. vm_compute. intuition congruence.
   - right;left. apply V293_encoded_memory_outside;left;exact E. }
 unfold DHpre. apply astar_l_aop'_intro;[ |reflexivity]. apply DHowned_raw.
 unfold DHR. assert (WithEmpty : DHstate (DHmemory d s) |=
   DHbindings ** (LINV V293_witness_li DHtid [] **
   ((V293_owned_record_cells (DHcells d s) ** ExpiryFrame) ** CurTid DHtid))).
 { eapply DHstar with (m1:=emp) (m2:=DHmemory d s).
   - apply map_join_comm;apply map_join_emp.
   - exact DHbinding_spatial.
   - eapply DHstar with (m1:=emp) (m2:=DHmemory d s).
     + apply map_join_comm;apply map_join_emp.
     + exact DHlinv_spatial.
     + exact Both. }
 clear -WithEmpty. sep auto.
Qed.
Theorem DHrules : forall Spec sd I r ri d s,
 (0<=d<=Int.max_unsigned)%Z -> s<256 ->
 InfRules Spec sd V293_witness_li I r ri (DHpre d s)
 (V293_tick_delay 901%Z 902%Z 903%Z) (DHpost d s) DHtid.
Proof.
 intros. apply V293_tick_delay_fragment_hoare;
 first [assumption|lia|change (8+54<=4294967295)%Z;lia|exact DHenv|exact DHcur].
Qed.

(* Same actual operational Mf, unchanged input/code/semantics. Each rejected
   observation changes exactly one byte expectation, not the executed heap. *)
Theorem DHwrong_row : forall P ks enabled, exists Mf,
 ExpiryExecution P ks enabled 1 Mf /\
 load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 132) /\
 load Tint8 Mf (93%positive,1%Z)<>Some(V293_byteval 128) /\
 load Tint8 Mf (81%positive,57%Z)=Some(V293_byteval 1) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (ExpiryLiteralExecution P ks enabled 1 ltac:(lia))
 as (Mf&Exec&Dly&Stat&Pend&Group&Row&Pointer&Frame&Rest).
 exists Mf. split;[exact Exec| ]. split;[exact Row| ]. split.
 - rewrite Row. vm_compute;discriminate.
 - split;[exact Pend| ]. apply Frame. left;reflexivity.
Qed.
Theorem DHwrong_pend : forall P ks enabled, exists Mf,
 ExpiryExecution P ks enabled 9 Mf /\
 load Tint8 Mf (81%positive,57%Z)=Some(V293_byteval 1) /\
 load Tint8 Mf (81%positive,57%Z)<>Some(V293_byteval 0) /\
 load Tint8 Mf (93%positive,1%Z)=Some(V293_byteval 128) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (ExpiryLiteralExecution P ks enabled 9 ltac:(lia))
 as (Mf&Exec&Dly&Stat&Pend&Group&Row&Pointer&Frame&Rest).
 exists Mf. split;[exact Exec| ]. split;[exact Pend| ]. split.
 - rewrite Pend. vm_compute;discriminate.
 - split;[exact Row| ]. apply Frame. left;reflexivity.
Qed.
Theorem DHbranch_cases : forall d s,
 In d [0%Z;1%Z;3%Z;4294967295%Z] ->
 In s [0;1;2;4;8;9;16;32;64;128;255] ->
 DHstate (DHmemory d s) |= DHpre d s /\
 (forall Spec sd I r ri, InfRules Spec sd V293_witness_li I r ri (DHpre d s)
   (V293_tick_delay 901%Z 902%Z 903%Z) (DHpost d s) DHtid).
Proof.
 intros d s Ds Ss. assert (D:(0<=d<=Int.max_unsigned)%Z).
 { change (0<=d<=4294967295)%Z. simpl in Ds;intuition lia. }
 assert (S:s<256) by (simpl in Ss;intuition lia).
 split;[apply DHentry;exact S|intros;apply DHrules;assumption].
Qed.
Print Assumptions DHentry.
Print Assumptions DHrules.
Print Assumptions DHwrong_row.
Print Assumptions DHwrong_pend.
Print Assumptions DHbranch_cases.
