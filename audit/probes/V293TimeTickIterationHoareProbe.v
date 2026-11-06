(* Both initial IE values, literal owned entry; independent old operational
   execution for single-observation controls, not a premise of new rules. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickIterationHoare.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.audit.probes.V293TimeTickExpiryProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
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
Definition IHstate enabled M : RstateOP :=
 (DHge,TickLocal,M,(fun _=>false),(enabled,[1],[false]),emp,spec_done None).
Definition IHpre enabled d s := <||spec_done None||> **
 OS[(fun _=>false),enabled,[1],[false]] ** V293_rdy_raw_cells (DHcells d s) DHR.
Definition IHpost enabled d s := <||spec_done None||> **
 OS[(fun _=>false),enabled,[1],[false]] ** V293_rdy_raw_cells
 (V293_tick_expiry_cells 70%positive 81%positive 8%Z TickNext
 (Int.repr (V293_tick_after_delay d)) TickNext (V293_tick_after_stat d s)
 (V293_tick_after_pend d 7 s) 1 2 92%positive (V293_tick_after_group d s 1 1)
 93%positive (V293_tick_after_row d s 128 2)) DHR.
Lemma IHframe_good : GoodFrm DHR.
Proof.
 unfold DHR,DHbindings,LINV,V293_witness_li,CurTid,ExpiryFrame,
 V293_owned_record_cells,V293_owned_record_cell,ExpiryFrameCells.
 cbn [GoodFrm]. repeat split;intros;exact I.
Qed.
Theorem IHentry : forall enabled d s, s<256 ->
 IHstate enabled (DHmemory d s) |= IHpre enabled d s.
Proof.
 intros enabled d s S.
 pose proof (DHentry d s S) as Owned. apply astar_l_aop'_elim in Owned. destruct Owned as [_ Owned].
 assert (Good:GoodFrm (V293_rdy_raw_cells (DHcells d s) DHR))
  by (apply V293_raw_cells_good_frame;exact IHframe_good).
 pose proof (goodfrm_prop _ _ _ _ _ _ Good Owned (fun _=>false)
   (enabled,[1],[false]) (spec_done None)) as Rebased.
 assert (WithCtrl:IHstate enabled (DHmemory d s) |=
   Aisr (fun _=>false) ** (Aie enabled ** (Ais (1::nil) ** (Acs (false::nil) **
    V293_rdy_raw_cells (DHcells d s) DHR)))).
 { apply astar_l_aisr_intro;[ |reflexivity].
   apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity].
   apply astar_l_acs_intro;[exact Rebased|reflexivity]. }
 unfold IHpre. apply astar_l_aop'_intro;[ |reflexivity]. clear -WithCtrl. sep auto.
Qed.
Theorem IHrules : forall Spec sd I r ri enabled d s,
 (0<=d<=Int.max_unsigned)%Z -> s<256 ->
 InfRules Spec sd V293_witness_li I r ri (IHpre enabled d s)
 (V293_tick_iteration 901%Z 902%Z 903%Z) (IHpost enabled d s) DHtid.
Proof.
 intros. apply V293_tick_iteration_hoare;
 first [assumption|lia|change (8+54<=4294967295)%Z;lia|exact DHenv|exact DHcur|
   exact IHframe_good|change (1<=INUM)%nat;unfold INUM;lia].
Qed.
Theorem IHbranch_cases : forall enabled d s,
 In d [0%Z;1%Z;3%Z;4294967295%Z] ->
 In s [0;1;2;4;8;9;16;32;64;128;255] ->
 IHstate enabled (DHmemory d s) |= IHpre enabled d s /\
 (forall Spec sd I r ri, InfRules Spec sd V293_witness_li I r ri (IHpre enabled d s)
   (V293_tick_iteration 901%Z 902%Z 903%Z) (IHpost enabled d s) DHtid).
Proof.
 intros enabled d s Ds Ss. assert (D:(0<=d<=Int.max_unsigned)%Z).
 { change (0<=d<=4294967295)%Z. simpl in Ds;intuition lia. }
 assert (S:s<256) by (simpl in Ss;intuition lia).
 split;[apply IHentry;exact S|intros;apply IHrules;assumption].
Qed.
Definition IHopstate enabled M : RstateOP :=
 (ExpiryGlobal,TickLocal,M,(fun _=>false),(enabled,[1],[false]),emp,spec_done None).
Lemma IHoperational_entry : forall enabled s, s<256 ->
 IHopstate enabled (ExpiryMemory s) |= V293_owned_record_cells (ExpiryCells s) ** ExpiryFrame.
Proof.
 intros enabled s S. pose proof (ExpiryEntrySatisfiable enabled s S) as Owned.
 assert (Good:GoodFrm (V293_owned_record_cells (ExpiryCells s) ** ExpiryFrame)).
 { unfold ExpiryCells,V293_tick_expiry_cells,ExpiryFrame,ExpiryFrameCells,
     V293_owned_record_cells,V293_owned_record_cell. cbn [GoodFrm]. repeat split;exact I. }
 exact (goodfrm_prop _ _ _ _ _ _ Good Owned (fun _=>false)
   (enabled,[1],[false]) (spec_done None)).
Qed.
Definition IHexecution P ks enabled s Mf : Prop :=
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((ExpiryGlobal,TickLocal,ExpiryMemory s),(fun _ => false),(enabled,(1%nat :: nil),(false :: nil)))
    (curs (sskip None),(kenil,ks))
    ((ExpiryGlobal,TickLocal,Mf),(fun _ => false),(enabled,(1%nat :: nil),(false :: nil))).

Theorem IHliteralExecution : forall P ks enabled s,
  s < 256 -> exists Mf,
  IHexecution P ks enabled s Mf /\
  load Tint32 Mf (81%positive,52%Z) = Some (Vint32 Int.zero) /\
  load Tint8 Mf (81%positive,56%Z) = Some (V293_byteval (V293_tick_expired_stat s)) /\
  load Tint8 Mf (81%positive,57%Z) = Some (V293_byteval (V293_tick_expired_pend s)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval (V293_tick_expired_group s 1 1)) /\
  load Tint8 Mf (93%positive,1%Z) = Some (V293_byteval (V293_tick_expired_row s 128 2)) /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr TickNext) /\
  (forall a tp v, In (a,tp,v) ExpiryFrameCells -> load tp Mf a = Some v) /\
  IHopstate enabled Mf |= V293_owned_record_cells
    (V293_tick_expiry_cells 70%positive 81%positive 8%Z TickNext Int.zero TickNext
      (V293_tick_expired_stat s) (V293_tick_expired_pend s) 1 2 92%positive
      (V293_tick_expired_group s 1 1) 93%positive (V293_tick_expired_row s 128 2)) ** ExpiryFrame.
Proof.
  intros P ks enabled s S.
  destruct (V293_tick_expiry_iteration_owned_execution P ks ExpiryGlobal TickLocal (ExpiryMemory s)
    (fun _ => false) enabled (1%nat :: nil) (false :: nil) emp (spec_done None) 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z TickNext s 7 1 2 92%positive 1 93%positive 128 ExpiryFrame
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(lia) ltac:(change (8+54<=4294967295)%Z;lia)
    S ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (IHoperational_entry enabled s S)) as (Mf & Exec & Dly & Stat & Pend & Group & Row & Pointer & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Dly | ]. split; [exact Stat | ].
  split; [exact Pend | ]. split; [exact Group | ]. split; [exact Row | ]. split; [exact Pointer | ].
  split; [ | exact Returned]. intros a tp v Member.
  change (load tp (getmem (IHopstate enabled Mf)) a = Some v).
  eapply V293_record_star_load_r; [ | exact Returned].
  unfold ExpiryFrame. apply V293_owned_record_cells_load. exact Member.
Qed.

(* Same actual Mf, only the expected local pointer is changed. The real next
   field and caller canary remain readable from that very same output. *)
Theorem IHwrong_pointer : forall P ks enabled, exists Mf,
 IHexecution P ks enabled 1 Mf /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some(Vptr TickNext) /\
 load (Tptr V293_tcb_type) Mf (70%positive,0%Z)<>Some(Vptr (81%positive,Int.repr 8)) /\
 load (Tcom_ptr 410%Z) Mf (81%positive,28%Z)=Some(Vptr TickNext) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (IHliteralExecution P ks enabled 1 ltac:(lia))
 as (Mf&Exec&Dly&Stat&Pend&Group&Row&Pointer&Frame&Rest).
 exists Mf. split;[exact Exec| ]. split;[exact Pointer| ]. split.
 - rewrite Pointer. vm_compute;discriminate.
 - split.
   + change (load (Tcom_ptr 410%Z) (getmem (IHopstate enabled Mf)) (81%positive,28%Z)=Some(Vptr TickNext)).
     eapply V293_record_star_load_l;[ |exact Rest].
     apply V293_owned_record_cells_load. cbn [V293_tick_expiry_cells In];tauto.
   + apply Frame. left;reflexivity.
Qed.
(* Independent execution has this actual final control state. Change only IE
   in the rejected assertion; stack, code, input, Mf and canary stay fixed. *)
Theorem IHwrong_ie : forall P ks enabled, exists Mf,
 IHexecution P ks enabled 1 Mf /\
 (IHopstate enabled Mf |= Aie enabled ** Atrue) /\
 ~ (IHopstate enabled Mf |= Aie (negb enabled) ** Atrue) /\
 (IHopstate enabled Mf |= Acs (false::nil) ** Atrue) /\
 load Tint32 Mf (90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros. destruct (IHliteralExecution P ks enabled 1 ltac:(lia))
 as (Mf&Exec&Dly&Stat&Pend&Group&Row&Pointer&Frame&Rest).
 exists Mf. split;[exact Exec| ]. split.
 - apply astar_l_aie_intro;[exact I|reflexivity].
 - split.
   + intro Bad. apply astar_l_aie_elim in Bad. destruct Bad as [Bad _].
     change (enabled=negb enabled) in Bad. destruct enabled;discriminate.
   + split;[apply astar_l_acs_intro;[exact I|reflexivity]|apply Frame;left;reflexivity].
Qed.
Print Assumptions IHframe_good.
Print Assumptions IHentry.
Print Assumptions IHrules.
Print Assumptions IHbranch_cases.
Print Assumptions IHwrong_pointer.
Print Assumptions IHwrong_ie.

Print Assumptions IHoperational_entry.
Print Assumptions IHliteralExecution.
