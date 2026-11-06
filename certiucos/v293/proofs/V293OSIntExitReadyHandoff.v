(* Actual interrupt-exit suffix under the ready/TCB/storage invariant.
   Shared task records return to Inv; they are not a private switch frame. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Section ReadyHandoff.
Variables br bg bp : block.
Variables high current counter target : var.
Variables bh bc bk : block.
Variable tp : type.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable next : Modules.tid.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Let bytecells := ((bh,0%Z),Tint8)::((bc,0%Z),Tint8)::rest.
Let cells := ((bk,0%Z),Tint32)::bytecells.
Let inv := V293_ready_storage_inv br bg bp target tp cells.
Let private := V293_counter_bindings counter bk **
 ((V293_handoff_binding high bh ** V293_handoff_binding current bc) ** px).
Definition V293_ready_exit_tail nh nc c :=
 <||sched;;aop||> **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_counter_cell counter bk c **
 (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px))))))).
Definition V293_ready_exit_resumed :=
 <||aop||> ** SWINVt inv tid ** Ais stack ** Acs critical ** private.
Definition V293_ready_exit_switch_payload nh nc c :=
 <||sched;;aop||> **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (Amapsto(bh,0%Z)Tint8 true(V293_byteval nh) **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (Amapsto(bk,0%Z)Tint32 true(Vint32 c) **
 (V293_ready_payload br bg bp tasks ** V293_storage rest)))))).
Lemma V293_ready_exit_split : forall nh nc c,
 V293_ready_exit_tail nh nc c ==>
 V293_ready_exit_switch_payload nh nc c ** private.
Proof.
 intros nh nc c st H;unfold V293_ready_exit_tail,V293_ready_exit_switch_payload,
 private,V293_counter_cell,V293_handoff_byte in *;sep auto.
Qed.
Lemma V293_ready_exit_close : forall nh nc c,
 nh<256 ->nc<256 ->
 V293_ready_exit_switch_payload nh nc c ==>
 <||sched;;aop||> ** SWINVt inv tid ** Ais stack ** Acs critical.
Proof.
 intros nh nc c BH BC st H.
 assert(Storage:Amapsto(bh,0%Z)Tint8 true(V293_byteval nh) **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (Amapsto(bk,0%Z)Tint32 true(Vint32 c) ** V293_storage rest)) ==>
 V293_storage cells).
 { intros s S;cbn[cells bytecells V293_storage];unfold V293_storage_cell.
   sep auto;[apply V293_byte_type;exact BH|apply V293_byte_type;exact BC]. }
 assert(Open:st |=
 (V293_storage_open target tp tid tasks events now next **
 (V293_ready_payload br bg bp tasks ** V293_storage cells)) **
 (<||sched;;aop||> ** (CurTid tid ** (Ais stack ** Acs critical)))).
 { assert(S:st |= (Amapsto(bh,0%Z)Tint8 true(V293_byteval nh) **
 (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) **
 (Amapsto(bk,0%Z)Tint32 true(Vint32 c) ** V293_storage rest))) **
 ((V293_storage_open target tp tid tasks events now next ** V293_ready_payload br bg bp tasks) **
 (<||sched;;aop||> ** (CurTid tid ** (Ais stack ** Acs critical)))))
 by(unfold V293_ready_exit_switch_payload in H;sep auto).
 eapply astar_mono in S;[ |exact Storage|intros s HS;exact HS];clear H;sep auto. }
 assert(Close:V293_storage_open target tp tid tasks events now next **
 (V293_ready_payload br bg bp tasks ** V293_storage cells) ==> SWINV inv).
 { intros s S;apply V293_ready_storage_switch_close.
   unfold V293_storage_open,V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core,
   V293_shared_ready_records,V293_ready_storage_extra,V293_dispatch_cell in *;sep auto. }
 eapply astar_mono in Open;[ |exact Close|intros s HS;exact HS].
 unfold SWINVt;fold(CurTid tid);clear H;sep auto.
Qed.
Lemma V293_ready_exit_switch_pre : forall nh nc c,
 indom tasks tid ->V293_highest_ready tasks next ->
 V293_ready_exit_switch_payload nh nc c ==> SWPRE_NDEAD V293_scheduler target tid.
Proof.
 intros nh nc c Member Highest st H.
 unfold V293_ready_exit_switch_payload,V293_storage_open,V293_shared_fields in H.
 unfold SWPRE_NDEAD;split.
 - assert(K:st |= (CurTid tid ** CurTid tid) **
 (Aabsdata abstcblsid(abstcblist tasks) **
 ((GV target@(Tptr tp)|->Vptr next) ** (isrclr ** Atrue)))).
 { unfold V293_shared_flags in H;sep auto. }
 eapply astar_mono in K;[ |apply V293_current_halves_write| ].
 2:{apply astar_mono;[apply V293_tasks_highest_spatial;exact Highest|intros s HS;exact HS]. }
 unfold SWPRE;exists next;clear H;sep auto.
 - exists tasks;sep auto.
Qed.
Theorem V293_ready_exit_increment : forall Spec r ri nh nc c,
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_ready_exit_tail nh nc c)(V293_OSSched_increment counter)
 (V293_ready_exit_tail nh nc(Int.add c Int.one))tid.
Proof.
 intros Spec r ri nh nc c Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))) ** V293_counter_cell counter bk c))
 (q:=<||sched;;aop||> **
 (((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) **
 (V293_handoff_byte high bh nh ** (V293_handoff_byte current bc nc **
 (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))) ** V293_counter_cell counter bk(Int.add c Int.one))).
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - apply V293_OSSched_counter_increment;intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_exit_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_ready_exit_copy : forall Spec r ri nh nc c,
 nh<256 ->(px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_ready_exit_tail nh nc c)(sassign(evar current)(evar high))
 (V293_ready_exit_tail nh nh c)tid.
Proof.
 intros Spec r ri nh nc c Bound Local.
 eapply conseq_rule with
 (p:=<||sched;;aop||> ** (V293_handoff_byte current bc nc **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px))))))))
 (q:=<||sched;;aop||> ** (V293_handoff_byte current bc nh **
 (V293_handoff_byte high bh nh **
 ((V293_storage_open target tp tid tasks events now next ** CurTid tid) **
 ((Ais stack ** Acs critical) ** (V293_counter_cell counter bk c ** (V293_ready_payload br bg bp tasks ** (V293_storage rest ** px)))))))).
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - unfold V293_ready_exit_tail;intros st H;sep auto.
 - apply V293_handoff_byte_copy;[exact Bound| ].
   intros st H;apply V293_CurLINV_extend with(extra:=Atrue).
   eapply astar_mono;[apply V293_exit_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_ready_exit_handoff : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_ready_exit_tail nh nc c)(V293_interrupt_handoff high current target)
 V293_ready_exit_resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 unfold V293_interrupt_handoff;eapply seq_rule with(p':=V293_ready_exit_tail nh nh c).
 - apply V293_ready_exit_copy;assumption.
 - unfold V293_ready_exit_resumed;eapply switch_rule with
 (P':=V293_ready_exit_switch_payload nh nh c)(Px:=private)(lg:=nil).
 + unfold private,V293_handoff_binding,V293_counter_bindings;cbn[GoodFrm];tauto.
 + apply V293_ready_exit_split.
 + apply V293_ready_exit_close;assumption.
 + apply V293_ready_exit_switch_pre;assumption.
 + unfold private;intros st H.
   assert(P:st |= px ** Atrue)by(clear -H;sep auto).
   eapply astar_mono in P;[ |exact Local|intros s HS;exact HS];clear -P;sep auto.
Qed.
Theorem V293_ready_exit_changed_tail : forall Spec r ri nh nc c,
 nh<256 ->indom tasks tid ->V293_highest_ready tasks next ->GoodFrm px ->
 (px ==> LINV V293_shared_li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler V293_shared_li inv r ri
 (V293_ready_exit_tail nh nc c)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))
 V293_ready_exit_resumed tid.
Proof.
 intros Spec r ri nh nc c Bound Member Highest Good Local.
 eapply seq_rule with(p':=V293_ready_exit_tail nh nc(Int.add c Int.one)).
 - apply V293_ready_exit_increment;exact Local.
 - eapply seq_rule with(p':=V293_ready_exit_tail nh nc(Int.add c Int.one)).
 + apply skip_rule.
 + apply V293_ready_exit_handoff;assumption.
Qed.
End ReadyHandoff.
