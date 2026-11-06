(* Original normalized iteration, including next BEFORE exit, both initial IE
   values. Caller holds the raw fields separately from any acquired invariant;
   this does not move TCB resources out of a production IRQ invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Theorem V293_tick_advance_fragment_hoare : forall Spec sd li I r ri tid aop R
 ptcb bc bt base delay next s pend y x bg g br row,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (forall st, st |= R -> get (getlenv st) ptcb=Some(bc,Tptr V293_tcb_type)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) delay next s pend y x bg g br row) R)
 (V293_tick_advance ptcb)
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base next delay next s pend y x bg g br row) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb bc bt base delay next s pend y x bg g br row
 Base Limit Env HR.
 unfold V293_tick_advance,V293_tick_expiry_cells.
 eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop [] (bc,0%Z)
  (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)) _ (Vptr next) _ _ (Tcom_ptr 410%Z) R).
 - reflexivity.
 - apply eq_vcomptr. split;[left;exists V293_tcb_type;reflexivity|left;exists 410%Z;reflexivity].
 - intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
   pose proof (V293_raw_cells_frame_env _ R
    (fun ge le=>get le ptcb=Some(bc,Tptr V293_tcb_type)) Env _ Owned) as Binding.
   change (get le ptcb=Some(bc,Tptr V293_tcb_type)) in Binding.
   assert (NextEval : evaltype (V293_tick_field ptcb 7%Z) (ge,le,M)=Some(Tcom_ptr 410%Z) /\
    evalval (V293_tick_field ptcb 7%Z) (ge,le,M)=Some(Vptr next)).
   { eapply V293_tick_raw_field_eval with (cells:=V293_tick_expiry_cells bc bt base
      (bt,Int.repr base) delay next s pend y x bg g br row) (R:=R)
      (bc:=bc) (bt:=bt) (base:=base) (delta:=20%Z) (field:=7%Z)
      (ptcb:=ptcb) (tp:=Tcom_ptr 410%Z) (v:=Vptr next) (s:=(ge,le,M,ir,aux,O,op));
     [exact Env|cbn [V293_tick_expiry_cells In];tauto|cbn [V293_tick_expiry_cells In];tauto|
      reflexivity|exact Base|lia|lia|reflexivity|reflexivity|exact Owned]. }
   destruct NextEval as [Nt Nv].
   cbn [sat getsmem get_smem evaltype evaladdr get_lenv get_genv]. rewrite Binding.
   repeat split;try assumption;reflexivity || discriminate.
 - exact HR.
Qed.

(* The original right association is retained; tail is a separately proved
   continuation. In particular exit cannot be commuted before next. *)
Theorem V293_tick_delay_advance_with_tail : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base d next s pend y x bg g br row tail q,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base next (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)) R) tail q tid ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row) R)
 (sseq (V293_tick_delay ptcb rows group) (sseq (V293_tick_advance ptcb) tail)) q tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc bt base d next s pend y x bg g br row tail q
 Base Limit D S Pend Y X G Row Env HR Tail.
 eapply seq_rule.
 - apply V293_tick_delay_fragment_hoare;eassumption.
 - eapply seq_rule;[ |exact Tail]. apply V293_tick_advance_fragment_hoare;
   [exact Base|exact Limit| |exact HR]. intros st HS;exact (proj1 (Env st HS)).
Qed.

(* Resources in R are owned before entry. The acquired ISR invariant is an
   arbitrary untouched frame, not a source of production TCB ownership. *)
Theorem V293_tick_iteration_hoare : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base d next s pend y x bg g br row enabled ir si ci,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si <= INUM)%nat ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row) R)
 (V293_tick_iteration ptcb rows group)
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base next (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc bt base d next s pend y x bg g br row
 enabled ir si ci Base Limit D S Pend Y X G Row Env HR GF Bound.
 set (before:=V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row).
 set (after:=V293_tick_expiry_cells bc bt base next (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)).
 set (P:=V293_rdy_raw_cells before R).
 set (Q:=V293_rdy_raw_cells after R).
 assert (GP:GoodFrm P) by (apply V293_raw_cells_good_frame;exact GF).
 assert (GQ:GoodFrm Q) by (apply V293_raw_cells_good_frame;exact GF).
 assert (IQ:Q ==> CurLINV li tid) by (apply V293_raw_cells_CurLINV;exact HR).
 assert (Work: forall extra tail target,
   InfRules Spec sd li I r ri (<||aop||> ** extra ** Q) tail target tid ->
   InfRules Spec sd li I r ri (<||aop||> ** extra ** P)
    (sseq (V293_tick_delay ptcb rows group) (sseq (V293_tick_advance ptcb) tail)) target tid).
 { intros extra tail target Tail.
   eapply conseq_rule with (p:=<||aop||> ** V293_rdy_raw_cells before (extra ** R)) (q:=target).
   - apply astar_mono;[intros st H;exact H|apply V293_raw_cells_unmove_frame].
   - intros st H;exact H.
   - unfold before,after in *. eapply V293_tick_delay_advance_with_tail;try eassumption.
     + intros st H. eapply V293_star_env_r;[exact Env|exact H].
     + apply V293_star_CurLINV_r;exact HR.
     + eapply conseq_rule with (p:=<||aop||> ** extra ** Q) (q:=target);[ | |exact Tail].
       * apply astar_mono;[intros st H;exact H|apply V293_raw_cells_move_frame].
       * intros st H;exact H. }
 change (InfRules Spec sd li I r ri (<||aop||> ** OS[ir,enabled,si,ci] ** P)
   (sseq (sprim encrit) (sseq (V293_tick_delay ptcb rows group)
     (sseq (V293_tick_advance ptcb) (sprim excrit))))
   (<||aop||> ** OS[ir,enabled,si,ci] ** Q) tid).
 destruct enabled.
 - eapply seq_rule.
   + eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) ** [| (gettopis si <= INUM)%nat |] ** P)
       (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si) ** P).
     * intros st H. assert (IS:st |= Ais si ** Atrue) by (sep auto).
       pose proof (V293_time_topis si Atrue st IS) as Top.
       apply astar_l_atopis_elim in Top. destruct Top as [Top _].
       pose proof (@astar_l_atopis_intro st (gettopis si) _ H Top) as HT.
       clear H. rename HT into H. sep auto.
     * intros st H;exact H.
     * apply encrit1_rule;exact GP.
   + eapply conseq_rule with
       (p:=<||aop||> ** (OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si)) ** P)
       (q:=<||aop||> ** OS[ir,true,si,ci] ** Q);[ | |apply Work].
     * intros st H;sep auto.
     * intros st H;exact H.
     * eapply conseq_rule with
         (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) ** invlth_isr I 0 (gettopis si) ** Q)
         (q:=<||aop||> ** OS[ir,true,si,ci] ** Q).
       -- intros st H. assert (IS:st |= Ais si ** Atrue) by (sep auto).
          pose proof (V293_time_topis si Atrue st IS) as Top.
          apply astar_l_atopis_elim in Top. destruct Top as [Top _].
          pose proof (@astar_l_atopis_intro st (gettopis si) _ H Top) as HT.
          clear H. rename HT into H. sep auto.
       -- intros st H;exact H.
       -- apply excrit1_rule;assumption.
 - eapply seq_rule.
   + apply encrit2_rule;exact GP.
   + apply Work. apply excrit2_rule;exact GQ.
Qed.

Theorem V293_tick_iteration_semantics : forall Spec sd li I r ri tid aop R
 ptcb rows group bc bt base d next s pend y x bg g br row enabled ir si ci,
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z -> (0<=d<=Int.max_unsigned)%Z ->
 s<256 -> pend<256 -> y<2 -> x<8 -> g<256 -> row<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si <= INUM)%nat ->
 simulation.RuleSem Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base (bt,Int.repr base) (Int.repr d) next s pend y x bg g br row) R)
 (V293_tick_iteration ptcb rows group)
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
  (V293_tick_expiry_cells bc bt base next (Int.repr (V293_tick_after_delay d)) next
   (V293_tick_after_stat d s) (V293_tick_after_pend d pend s) y x bg
   (V293_tick_after_group d s g y) br (V293_tick_after_row d s row x)) R) tid.
Proof. intros. apply RuleSound. apply V293_tick_iteration_hoare;assumption. Qed.

Print Assumptions V293_tick_advance_fragment_hoare.
Print Assumptions V293_tick_delay_advance_with_tail.
Print Assumptions V293_tick_iteration_hoare.
Print Assumptions V293_tick_iteration_semantics.
