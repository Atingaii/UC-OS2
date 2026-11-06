(* Ownership-preserving connection of the original interrupt-exit middle to
   actual critical calls. Caller bindings remain outside callee resources. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition V293_exit_guard_bindings nesting lock bn bl : asrt :=
 (Agvarenv nesting Tint8(bn,0%Z) //\\ A_notin_lenv nesting) **
 (Agvarenv lock Tint8(bl,0%Z) //\\ A_notin_lenv lock).
Lemma V293_exit_guard_bindings_env : forall nesting lock bn bl s,
 s |= V293_exit_guard_bindings nesting lock bn bl ->
 V293_interrupt_env nesting lock bn bl(getgenv s)(getlenv s).
Proof.
 intros nesting lock bn bl s H.
 assert(E:forall x b st,st |= Agvarenv x Tint8(b,0%Z) //\\ A_notin_lenv x ->
  get(getlenv st)x=None /\ get(getgenv st)x=Some(b,Tint8)).
 { intros x b st[G [N _]]. apply agvarenv_elim in G.
   split;[ |exact(proj2(proj1 G))].
   destruct(get(getlenv st)x)as[v| ]eqn:X;[exfalso;apply N;exists v;exact X|reflexivity]. }
 unfold V293_exit_guard_bindings in H. unfold V293_interrupt_env.
 assert(A: get(getlenv s)nesting=None /\ get(getgenv s)nesting=Some(bn,Tint8)).
 { eapply V293_star_env_l;[apply E|exact H]. }
 assert(B: get(getlenv s)lock=None /\ get(getgenv s)lock=Some(bl,Tint8)).
 { eapply V293_star_env_r;[apply E|exact H]. } tauto.
Qed.

Section Bridge.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter nesting lock : var.
Variables bcur bcounter bn bl : block.
Variable nc : nat.

(* All these bindings are memory/abstract-state empty. Global bindings travel
   with the caller when conjoined to its local non-shadowing facts. *)
Definition V293_exit_caller_bindings : asrt :=
 V293_prefix_bindings table high target tp bp bo **
 ((Agvarenv current Tint8(bcur,0%Z) //\\ A_notin_lenv current) **
 (V293_counter_bindings counter bcounter ** V293_exit_guard_bindings nesting lock bn bl)).
Definition V293_exit_physical_pre nest locked old c : asrt :=
 V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
 ((V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid(abstcblist tasks)) **
 (Amapsto(bcur,0%Z)Tint8 false(V293_byteval nc) **
  V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)Aemp)) **
 (V293_prefix_output tp bo old ** PV(bcounter,Int.zero)@Tint32|->Vint32 c).
Definition V293_exit_physical_tail nest locked c : asrt :=
 EX t : Modules.tid,[|V293_highest_ready tasks t|] **
 (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
 (((V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid(abstcblist tasks)) **
 (Amapsto(bcur,0%Z)Tint8 false(V293_byteval nc) **
  V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)Aemp)) **
 (V293_prefix_output tp bo(Vptr t) ** PV(bcounter,Int.zero)@Tint32|->Vint32 c))).
Let oldpre R := V293_exit_ready_pre unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter bn bl nc
 (V293_exit_guard_bindings nesting lock bn bl ** R).
Let oldtail nest locked R := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter nc
 (V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)
  (V293_exit_guard_bindings nesting lock bn bl ** R)).
Lemma V293_exit_pre_split : forall R nest locked old c,
 oldpre R nest locked old c ==>
 V293_exit_physical_pre nest locked old c ** (V293_exit_caller_bindings ** R).
Proof.
 intros R nest locked old c s H.
 unfold oldpre,V293_exit_ready_pre,V293_exit_physical_pre,V293_exit_caller_bindings,
  V293_prefix_frame,V293_guard_cell,V293_counter_cell,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_pre_join : forall R nest locked old c,
 V293_exit_physical_pre nest locked old c ** (V293_exit_caller_bindings ** R) ==>
 oldpre R nest locked old c.
Proof.
 intros R nest locked old c s H.
 unfold oldpre,V293_exit_ready_pre,V293_exit_physical_pre,V293_exit_caller_bindings,
  V293_prefix_frame,V293_guard_cell,V293_counter_cell,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_tail_split : forall R nest locked c,
 oldtail nest locked R c ==>
 V293_exit_physical_tail nest locked c ** (V293_exit_caller_bindings ** R).
Proof.
 intros R nest locked c s[t H]. unfold oldtail,V293_OSSched_tail_state in H.
 unfold V293_exit_physical_tail. sep normal. exists t.
 unfold V293_exit_caller_bindings,V293_prefix_frame,V293_guard_cell,V293_counter_cell,
  V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *;sep auto.
Qed.
Lemma V293_exit_tail_join : forall R nest locked c,
 V293_exit_physical_tail nest locked c ** (V293_exit_caller_bindings ** R) ==>
 oldtail nest locked R c.
Proof.
 intros R nest locked c s H. unfold V293_exit_physical_tail in H. sep normal in H.
 destruct H as[t H]. unfold oldtail,V293_OSSched_tail_state. exists t.
 unfold V293_exit_caller_bindings,V293_prefix_frame,V293_guard_cell,V293_counter_cell,
  V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *;sep auto.
Qed.
Lemma V293_exit_caller_bindings_good : GoodFrm V293_exit_caller_bindings.
Proof.
 unfold V293_exit_caller_bindings,V293_prefix_bindings,V293_counter_bindings,V293_exit_guard_bindings.
 repeat split;exact I.
Qed.
Lemma V293_exit_physical_pre_good : forall nest locked old c,
 GoodLInvAsrt li -> GoodFunAsrt(V293_exit_physical_pre nest locked old c).
Proof.
 clear oldpre oldtail table target current counter nesting lock.
 intros nest locked old c Hli.
 assert(P:GoodFunAsrt(V293_read_pointers tp bp 0 entries)).
 { generalize 0%Z;induction entries;intros;cbn[V293_read_pointers GoodFunAsrt];auto. }
 unfold V293_exit_physical_pre. split.
 - apply V293_sched_internal_pre_good;exact Hli.
 - unfold V293_prefix_output,V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells Aptrmapsto GoodFunAsrt].
   repeat split;try exact I;exact P.
Qed.
Lemma V293_exit_physical_tail_good : forall nest locked c,
 GoodLInvAsrt li -> GoodFunAsrt(V293_exit_physical_tail nest locked c).
Proof.
 clear oldpre oldtail table target current counter nesting lock.
 intros nest locked c Hli.
 assert(P:GoodFunAsrt(V293_read_pointers tp bp 0 entries)).
 { generalize 0%Z;induction entries;intros;cbn[V293_read_pointers GoodFunAsrt];auto. }
 unfold V293_exit_physical_tail. intro t. split;[exact I| ]. split.
 - apply V293_sched_internal_post_good;exact Hli.
 - unfold V293_prefix_output,V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells Aptrmapsto GoodFunAsrt].
   repeat split;try exact I;exact P.
Qed.
Lemma V293_exit_physical_pre_local : forall nest locked old c,
 V293_exit_physical_pre nest locked old c ==> CurLINV li tid.
Proof.
 intros nest locked old c. unfold V293_exit_physical_pre. apply V293_star_CurLINV_l.
 apply V293_sched_internal_pre_CurLINV.
Qed.
Lemma V293_exit_physical_tail_local : forall nest locked c,
 V293_exit_physical_tail nest locked c ==> CurLINV li tid.
Proof.
 intros nest locked c s[t H]. eapply V293_star_CurLINV_r;[ |exact H].
 apply V293_star_CurLINV_l. apply V293_sched_internal_post_CurLINV.
Qed.
Definition V293_exit_acquired nest locked old c token address : asrt :=
 V293_exit_physical_pre nest locked old c ** PV address @Tint32|->token.
Definition V293_exit_leaving nest locked old c token (switch_post:addrval->asrt) address : asrt :=
 if V293_exit_enabled nest locked then
  if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then
   V293_exit_physical_tail(V293_exit_depth nest)locked c ** PV address @Tint32|->token
  else switch_post address
 else V293_exit_physical_pre(V293_exit_depth nest)locked old c ** PV address @Tint32|->token.
Lemma V293_exit_acquired_good : forall nest locked old c token,
 GoodLInvAsrt li -> forall address,GoodFunAsrt(V293_exit_acquired nest locked old c token address).
Proof.
 intros nest locked old c token Hli address. unfold V293_exit_acquired.
 split;[apply V293_exit_physical_pre_good;exact Hli|exact I].
Qed.
Lemma V293_exit_leaving_good : forall nest locked old c token switch_post,
 GoodLInvAsrt li -> (forall address,GoodFunAsrt(switch_post address)) ->
 forall address,GoodFunAsrt(V293_exit_leaving nest locked old c token switch_post address).
Proof.
 intros nest locked old c token switch_post Hli G address. unfold V293_exit_leaving.
 destruct(V293_exit_enabled nest locked);[destruct(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc)| ];
 try apply G;split;try exact I;
 first[apply V293_exit_physical_pre_good|apply V293_exit_physical_tail_good];exact Hli.
Qed.
Lemma V293_exit_acquired_local : forall nest locked old c token address,
 V293_exit_acquired nest locked old c token address ==> CurLINV li tid.
Proof.
 intros nest locked old c token address. unfold V293_exit_acquired.
 apply V293_star_CurLINV_l. apply V293_exit_physical_pre_local.
Qed.
Lemma V293_exit_leaving_local : forall nest locked old c token switch_post address,
 (switch_post address ==> CurLINV li tid) ->
 V293_exit_leaving nest locked old c token switch_post address ==> CurLINV li tid.
Proof.
 intros nest locked old c token switch_post address L. unfold V293_exit_leaving.
 destruct(V293_exit_enabled nest locked);[destruct(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc)| ];
 try exact L;apply V293_star_CurLINV_l;
 first[apply V293_exit_physical_pre_local|apply V293_exit_physical_tail_local].
Qed.

(* No whole-middle premise: only the real interrupt-switch call remains,
   under the enabled/different-priority conditions, with the updated counter. *)
Theorem V293_OSIntExit_middle_bridge : forall Spec sd I r ri sched_id int_switch saved bs extra
 token old c nest locked switch_post (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<256 -> locked<256 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm extra ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 (V293_exit_depth nest=0 -> locked=0 -> V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri
   ((V293_exit_physical_tail(V293_exit_depth nest)locked(Int.add c Int.one) **
     PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))tid) ->
 InfRules Spec sd li I r ri
 (V293_exit_acquired nest locked old c token(bs,Int.zero) **
  (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))
 (V293_OSIntExit_nesting_dispatch nesting lock
   (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
 (V293_exit_leaving nest locked old c token switch_post(bs,Int.zero) **
  (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))tid.
Proof.
 intros Spec sd I r ri sched_id int_switch saved bs extra token old c nest locked switch_post
 Hli Hlo Hhi Hr Hnc Hn Hl Hb Htable F Lookup Call.
 let R := constr:(PV(bs,Int.zero)@Tint32|->token ** (Alvarenv saved Tint32(bs,0%Z) ** extra))in
 eapply conseq_rule with(p:=oldpre R nest locked old c)
 (q:=if V293_exit_enabled nest locked then
   if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then
    oldtail(V293_exit_depth nest)locked R c
   else switch_post(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra))
  else oldpre R(V293_exit_depth nest)locked old c).
 - intros s H. apply V293_exit_pre_join. unfold V293_exit_acquired in H;sep auto.
 - unfold V293_exit_leaving.
   destruct(V293_exit_enabled nest locked);[destruct(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc)| ].
   + intros s H. apply V293_exit_tail_split in H;sep auto.
   + intros s H;exact H.
   + intros s H. apply V293_exit_pre_split in H;sep auto.
 - unfold oldpre,oldtail. eapply V293_OSIntExit_ready_dispatch with(Hli:=Hli);try eassumption.
   + cbn[GoodFrm]. split;[unfold V293_exit_guard_bindings;repeat split;exact I| ].
     cbn[Aptrmapsto GoodFrm];tauto.
   + intros st H. eapply V293_star_env_l;[apply V293_exit_guard_bindings_env|exact H].
   + intros En El Different. eapply conseq_rule with
      (p:=(V293_exit_physical_tail(V293_exit_depth nest)locked(Int.add c Int.one) **
        PV(bs,Int.zero)@Tint32|->token) **
       (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra))).
     * intros s H. apply V293_exit_tail_split in H;sep auto.
     * intros s H;exact H.
     * apply Call;assumption.
Qed.

(* The actual enter/exit call rules now consume the proved middle above.
   Fixed-owner, empty-logic-argument contracts are not a production port. *)
Theorem V293_OSIntExit_resource_bridge : forall Spec sd I r ri sched_id int_switch enter exit saved bs extra
 token old c nest locked switch_post entry restored (Hli:GoodLInvAsrt li)
 (SG:forall address,GoodFunAsrt(switch_post address))
 (EG:forall address,GoodFunAsrt(entry address))
 (RG:forall address,GoodFunAsrt(restored address)),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<256 -> locked<256 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm extra ->
 (entry(bs,Int.zero) ==> CurLINV li tid) ->
 (restored(bs,Int.zero) ==> CurLINV li tid) ->
 (switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 Spec enter=Some(V293_saved_pointer_fpre tid entry EG,
  V293_saved_pointer_fpost tid(V293_exit_acquired nest locked old c token)
   (V293_exit_acquired_good nest locked old c token Hli),(Tvoid,(Tptr Tint32)::nil)) ->
 Spec exit=Some(V293_saved_pointer_fpre tid(V293_exit_leaving nest locked old c token switch_post)
   (V293_exit_leaving_good nest locked old c token switch_post Hli SG),
  V293_saved_pointer_fpost tid restored RG,(Tvoid,(Tptr Tint32)::nil)) ->
 (V293_exit_depth nest=0 -> locked=0 -> V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri
   ((V293_exit_physical_tail(V293_exit_depth nest)locked(Int.add c Int.one) **
     PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))tid) ->
 InfRules Spec sd li I r ri
 (entry(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))
 (sseq(scall enter ((eaddrof(evar saved))::nil))
   (sseq(V293_OSIntExit_nesting_dispatch nesting lock
     (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
     (scall exit ((eaddrof(evar saved))::nil))))
 (restored(bs,Int.zero) ** (Alvarenv saved Tint32(bs,0%Z) ** (V293_exit_caller_bindings ** extra)))tid.
Proof.
 intros Spec sd I r ri sched_id int_switch enter exit saved bs extra token old c nest locked
 switch_post entry restored Hli SG EG RG Hlo Hhi Hr Hnc Hn Hl Hb Htable F EL RL SL Lookup Enter Exit Call.
 eapply V293_OSIntExit_critical_calls with
 (acquired:=V293_exit_acquired nest locked old c token)
 (leaving:=V293_exit_leaving nest locked old c token switch_post)
 (EG:=EG)(AG:=V293_exit_acquired_good nest locked old c token Hli)
 (LG:=V293_exit_leaving_good nest locked old c token switch_post Hli SG)(RG:=RG);try eassumption.
 - cbn[GoodFrm]. split;[apply V293_exit_caller_bindings_good|exact F].
 - apply V293_exit_acquired_local.
 - apply V293_exit_leaving_local;exact SL.
 - apply V293_OSIntExit_middle_bridge with(Hli:=Hli);assumption.
Qed.
End Bridge.
