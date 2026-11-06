Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
(* Actual writes use an arbitrary ambient invariant; switch closure is a separate obligation. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptCurrentEntry.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Section Prefix.
Variables li:LocalInv.
Variable RI:Inv.
Variables br bg bp:block.
Variables high current counter target:var.
Variables bh bc bk:block.
Variable tp:type.
Variable rest:list(addr*type).
Variable tid:Modules.tid.
Variable tasks:TcbMod.map.
Variable events:EcbMod.map.
Variable now:int32.
Variable next:Modules.tid.
Variable aop:spec_code.
Variable stack:list hid.
Variable critical:list bool.
Variable px:asrt.
Local Notation tail := (V293_ready_exit_tail br bg bp high current counter target bh bc bk tp rest tid tasks events now next aop stack critical px).
Lemma V293_current_handoff_local :
 (px ==> LINV li tid nil ** Atrue) ->
 CurTid tid ** px ==> CurLINV li tid.
Proof.
 intros Local st H;unfold CurLINV;exists(nil:list logicvar).
 eapply astar_mono in H;[ |intros s HS;exact HS|exact Local];clear -H;sep auto.
Qed.
Theorem V293_current_handoff_increment : forall Spec r ri nh nc c,
 (px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li RI r ri
 (tail nh nc c)(V293_OSSched_increment counter)
 (tail nh nc(Int.add c Int.one))tid.
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
   eapply astar_mono;[apply V293_current_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_current_handoff_copy : forall Spec r ri nh nc c,
 nh<256 ->(px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li RI r ri
 (tail nh nc c)(sassign(evar current)(evar high))
 (tail nh nh c)tid.
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
   eapply astar_mono;[apply V293_current_handoff_local;exact Local|intros s HS;exact HS| ]. clear -H;sep auto.
Qed.
Theorem V293_current_handoff_prefix : forall Spec r ri nh nc c,
 nh<256 ->(px ==> LINV li tid nil ** Atrue) ->
 InfRules Spec V293_scheduler li RI r ri
 (tail nh nc c)
 (sseq(V293_OSSched_increment counter)
  (sseq(sskip None)(sassign(evar current)(evar high))))
 (tail nh nh(Int.add c Int.one))tid.
Proof.
 intros Spec r ri nh nc c Bound Local.
 eapply seq_rule with(p':=tail nh nc(Int.add c Int.one)).
 - apply V293_current_handoff_increment;exact Local.
 - eapply seq_rule with(p':=tail nh nc(Int.add c Int.one)).
   + apply skip_rule.
   + apply V293_current_handoff_copy;assumption.
Qed.
End Prefix.

Section CandidateClosure.
Variables br bg bp:block.
Variable target:var.
Variable tp:type.
Variable cells:list(addr*type).
Variable bc:block.
Let basecore:=V293_ready_storage_core br bg bp target tp cells.
Let candidate:=V293_ready_current_inv br bg bp target tp cells bc.
Let core:=V293_ready_current_core br bg bp target tp cells bc.
Lemma V293_current_handoff_core_enrich :
 (basecore ==> EX nc:nat,[|nc<256|] **
   (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Atrue)) ->
 forall R ct tasks ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=basecore ** R ->
 get O curtid=Some(oscurt ct) ->get O abstcblsid=Some(abstcblist tasks) ->
 (ge,le,M,ir,aux,O,op)|=V293_current_guard bc ct tasks ->
 (ge,le,M,ir,aux,O,op)|=core ** R.
Proof.
 intros Own R ct tasks ge le M ir aux O op H Current Tasks Guard.
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&Base&Frame).
 unfold basecore,V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core in Base.
 sep normal in Base;sep destruct Base.
 assert(Fields:(ge,le,m1,ir,aux,o1,op)|=(CurTid x ** V293_shared_fields x x0 x1 x2) ** Atrue).
 { unfold V293_shared_ready_records in Base;sep auto. }
 destruct(V293_shared_fields_core_get _ _ _ _ _ _ Fields)as[C[T _]].
 assert(Cfull:get O curtid=Some(oscurt x))by(eapply OSAbstMod.join_get_l;[exact JO|exact C]).
 assert(Tfull:get O abstcblsid=Some(abstcblist x0))by(eapply OSAbstMod.join_get_l;[exact JO|exact T]).
 assert(x=ct)by congruence;assert(x0=tasks)by congruence;subst x x0.
 assert(P:(ge,le,M,ir,aux,O,op)|=
 (V293_shared_ready_records br bg bp ct tasks x1 x2 ** V293_ready_storage_extra target tp cells) ** R).
 { apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split;assumption. }
 assert(Keep:(ge,le,M,ir,aux,O,op)|=
 ((V293_shared_ready_records br bg bp ct tasks x1 x2 ** V293_ready_storage_extra target tp cells)
 //\\ V293_current_guard bc ct tasks) ** R).
 { apply V293_current_guard_separate.
   - intros st K;apply Own;unfold basecore,V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core.
     eapply astar_mono;[ |intros s H;exact H|exact K].
     intros s H;exists ct;exists tasks;exists x1;exists x2;exact H.
   - split;assumption. }
 eapply astar_mono;[ |intros st K;exact K|exact Keep].
 intros st K;exists ct;exists tasks;exists x1;exists x2;exact K.
Qed.
Theorem V293_current_handoff_guard_reject : forall ge le M ir aux O op ct tasks nc,
 nc<256 ->load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 ~V293_current_task tasks ct nc ->~V293_highest_ready tasks ct ->
 ~(ge,le,M,ir,aux,O,op)|=V293_current_guard bc ct tasks.
Proof.
 intros ge le M ir aux O op ct tasks nc Bound Load NotCurrent NotHighest G.
 destruct(V293_current_guard_same bc ct tasks nc (ge,le,M,ir,aux,O,op) Bound Load G);contradiction.
Qed.
Theorem V293_current_handoff_switch_reject : forall R ge le M ir aux O op ct tasks nc t,
 get O curtid=Some(oscurt ct) ->get O abstcblsid=Some(abstcblist tasks) ->
 nc<256 ->load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 ~V293_current_task tasks ct nc ->~V293_highest_ready tasks ct ->
 ~(ge,le,M,ir,aux,O,op)|=SWINVt candidate t ** R.
Proof.
 intros R ge le M ir aux O op ct tasks nc t Current Tasks Bound Load NotCurrent NotHighest H.
 unfold SWINVt in H;fold(CurTid t)in H.
 eapply astar_mono in H;[ |apply astar_mono;[apply V293_current_switch_open|intros st K;exact K]|intros st K;exact K].
 assert(Core:(ge,le,M,ir,aux,O,op)|=core ** (V293_shared_flags ** (CurTid t ** R)))by(sep auto).
 destruct(V293_current_core_guard_frame br bg bp target tp cells bc _ ge le M ir aux O op Core)
 as[u[ts[C[T G]]]].
 assert(u=ct)by congruence;assert(ts=tasks)by congruence;subst u ts.
 eapply V293_current_handoff_guard_reject; eassumption.
Qed.
Theorem V293_current_handoff_switch_highest_frame : forall R ge le M ir aux O op t,
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_storage_inv br bg bp target tp cells)t ** R ->
 sched_self V293_scheduler O ->
 (ge,le,M,ir,aux,O,op)|=SWINVt candidate t ** R.
Proof.
 intros R ge le M ir aux O op t H Self;unfold SWINVt in *;fold(CurTid t)in *.
 eapply astar_mono in H;[ |apply astar_mono;[apply V293_ready_storage_switch_open|intros st K;exact K]|intros st K;exact K].
 assert(P:(ge,le,M,ir,aux,O,op)|=basecore ** (V293_shared_flags ** (CurTid t ** R)))by(sep auto).
 apply V293_current_core_highest_frame with(bc:=bc)in P;[ |exact Self].
 eapply astar_mono;[ |intros st K;exact K| ].
 - apply astar_mono;[apply V293_current_switch_close|intros st K;exact K].
 - clear H;sep auto.
Qed.
End CandidateClosure.
