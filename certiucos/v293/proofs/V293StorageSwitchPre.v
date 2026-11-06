(* Read the actual target on the shared heap before forgetting its value.
   This does not add current-priority coherence to the storage invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Lemma V293_dispatch_read_frame : forall target tp bt next R ge le M Mf Mall ir aux O op,
 get ge target=Some(bt,Tptr tp) ->join M Mf Mall ->
 load(Tptr tp)Mall(bt,0%Z)=Some(Vptr next) ->
 (ge,le,M,ir,aux,O,op)|=V293_dispatch_cell target tp **R ->
 (ge,le,M,ir,aux,O,op)|=(GV target @ (Tptr tp) |-> (Vptr next)) **R /\
 load(Tptr tp)M(bt,0%Z)=Some(Vptr next).
Proof.
 intros target tp bt next R ge le M Mf Mall ir aux O op Env Frame Read Held.
 apply sat_split in Held;destruct Held as(mc&mr&oc&orr&JM&JO&[v Cell]&Rest).
 apply astar_l_apure_elim in Cell;destruct Cell as[Typed Cell].
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(b&GE&Map&Empty).
 pose proof(@mapstoval_load _ _ _ _ _ Typed Map)as Load.
 pose proof(@lmachLib.load_mono _ _ _ _ _ _ JM Load)as InM.
 rewrite <-InM in Load.
 pose proof(@lmachLib.load_mono _ _ _ _ _ _ Frame Load)as Whole.
 assert(b=bt)by congruence;subst b.
 assert(v=Vptr next)by congruence;subst v.
 split;[ |exact Load].
 apply sat_split';exists mc;exists mr;exists oc;exists orr;
 split;[exact JM| ];split;[exact JO| ];split;assumption.
Qed.

(* SWPRE is established on this SAME shared memory and abstract state.
   It cannot borrow any task-private or external spatial resource. *)
Theorem V293_storage_switch_pre : forall br bg bp target tp cells current next bt tasks
 ge le M ir aux O op,
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
 get O abstcblsid=Some(abstcblist tasks) ->indom tasks current ->
 V293_highest_ready tasks next ->
 (ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_storage_inv br bg bp target tp cells)current ->
 (ge,le,M,ir,aux,O,op)|=
 SWINVt(V293_ready_storage_inv br bg bp target tp cells)current //\\
 SWPRE_NDEAD V293_scheduler target current.
Proof.
 intros br bg bp target tp cells current next bt tasks ge le M ir aux O op
 Env Read TaskMap Member Highest Held.
 split;[exact Held| ].
 apply V293_ready_storage_switch_resources in Held.
 assert(Open:(ge,le,M,ir,aux,O,op)|=V293_dispatch_cell target tp **
 (SWINVt(V293_ready_inv br bg bp)current **V293_storage cells)).
 { unfold V293_ready_storage_extra in Held;sep auto. }
 clear Held.
 destruct(V293_dispatch_read_frame target tp bt next _ ge le M (emp:mem) M ir aux O op
 Env (map_join_emp M) Read Open)as[Named SameRead].
 clear Open.
 assert(Held:(ge,le,M,ir,aux,O,op)|=SWINVt(V293_ready_inv br bg bp)current **
 ((GV target @ (Tptr tp) |-> (Vptr next)) **V293_storage cells))by(sep auto).
 clear Named.
 eapply astar_mono in Held;[ |apply V293_ready_switch_full|intros st H;exact H].
 unfold V293_ready_full in Held;sep normal in Held;sep destruct Held.
 assert(Map:get O abstcblsid=Some(abstcblist x)).
 { eapply V293_star_abst_get_l with(s:=(ge,le,M,ir,aux,O,op))
 (p:=Aabsdata abstcblsid(abstcblist x))(q:=Atrue).
 - intros st H;rewrite <-(proj1 H);apply map_get_sig.
 - unfold V293_shared_fields in Held;sep auto. }
 assert(x=tasks)by congruence;subst x.
 unfold SWPRE_NDEAD;split.
 - assert(Payload:(ge,le,M,ir,aux,O,op)|=Aabsdata abstcblsid(abstcblist tasks) **
 ((GV target @ (Tptr tp) |-> (Vptr next)) **
 (isrclr **((EX tq:type,GV OSTCBCur @ (Tptr tq) |-> (Vptr current)) **Atrue)))).
 { unfold V293_shared_fields,V293_shared_flags in Held;sep auto. }
 eapply astar_mono in Payload;[ |apply V293_tasks_highest_spatial;exact Highest|intros st H;exact H].
 unfold SWPRE;exists next;clear Held;sep auto.
 - exists tasks;unfold V293_shared_fields in Held;sep auto.
Qed.
