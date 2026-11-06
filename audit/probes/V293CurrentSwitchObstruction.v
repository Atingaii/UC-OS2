(* A boundary obstruction for exact coherence strengthening, not kernel reachability. *)
Require Import CertiOS.audit.probes.V293ReadyStorageInvariantProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderCurrentCounterexample.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition CSstate M O : RstateOP :=
 (CGge,CGle,M,(fun _:hid=>false),(false,nil,[false]),O,spec_done None).
Lemma CScache_owned : forall t M O,CSstate M O|=SWINVt PPinv t ->
 exists v,load Tint8 M(94%positive,0%Z)=Some v.
Proof.
 intros t M O H;unfold PPinv in H;apply V293_ready_storage_switch_resources in H.
 assert(C:CSstate M O|=V293_storage_cell(94%positive,0%Z)Tint8 **Atrue).
 { unfold V293_ready_storage_extra,PPcells in H;cbn[V293_storage]in H;sep auto. }
 unfold V293_storage_cell in C;sep normal in C;sep destruct C.
 apply astar_l_apure_elim in C;destruct C as[T C].
 exists x;change(load Tint8(getmem(CSstate M O))(94%positive,0%Z)=Some x).
 eapply V293_record_star_load_l;[ |exact C].
 intros st Cell;eapply mapstoval_load;[exact T|exact(proj1 Cell)].
Qed.
Lemma CSfields : forall t M O,CSstate M O|=SWINVt PPinv t ->
 exists tasks,get O curtid=Some(oscurt t) /\
 get O abstcblsid=Some(abstcblist tasks) /\
 CSstate M O|=Aabsdata abstcblsid(abstcblist tasks) **Atrue.
Proof.
 intros t M O H;unfold PPinv in H;apply V293_ready_storage_switch_resources in H.
 eapply astar_mono in H;[ |apply V293_ready_switch_full|intros st K;exact K].
 unfold V293_ready_full in H;sep normal in H;sep destruct H.
 assert(P:CSstate M O|=V293_shared_fields t x x0 x1 **Atrue)by(sep auto).
 assert(C:get O curtid=Some(oscurt t)).
 { change(get(getabst(CSstate M O))curtid=Some(oscurt t)).
   eapply V293_star_abst_get_l;[ |exact P].
   intros st K;exact(proj1(V293_shared_fields_get _ _ _ _ st K)). }
 assert(T:get O abstcblsid=Some(abstcblist x)).
 { change(get(getabst(CSstate M O))abstcblsid=Some(abstcblist x)).
   eapply V293_star_abst_get_l;[ |exact P].
   intros st K;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ st K))). }
 exists x;split;[exact C| ];split;[exact T| ].
 unfold V293_shared_fields in P;clear H;sep auto.
Qed.
Lemma CSrelation_after_false : forall M O,
 get O abstcblsid=Some(abstcblist OwnershipTasks) ->
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) ->
 ~NCcurrent_relation(CSstate M(set O curtid(oscurt OwnershipReady))).
Proof.
 intros M O Tasks Read[t[ts[n[C[T[N[L Cur]]]]]]].
 change(get(set O curtid(oscurt OwnershipReady))curtid=Some(oscurt t))in C.
 change(get(set O curtid(oscurt OwnershipReady))abstcblsid=Some(abstcblist ts))in T.
 rewrite map_get_set in C;rewrite map_get_set' in T by discriminate.
 assert(t=OwnershipReady)by congruence;assert(ts=OwnershipTasks)by congruence;subst t ts.
 change(load Tint8 M(94%positive,0%Z)=Some(V293_byteval n))in L.
 assert(n=6)by(eapply RTbyte_injective;[exact N|lia|congruence]);subst n.
 destruct Cur as[_[st[msg Task]]];vm_compute in Task;discriminate.
Qed.
Theorem CSswitch_witness : exists M O Mf,
 CSstate M O|=SWINVt PPinv OwnershipWaiting /\
 NCcurrent_relation(CSstate M O) /\
 CSstate M O|=AHprio V293_scheduler OwnershipReady **Atrue /\
 get O abstcblsid=Some(abstcblist OwnershipTasks) /\
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Mf /\
 CSstate Mf(set O curtid(oscurt OwnershipReady))|=SWINVt PPinv OwnershipReady /\
 ~NCcurrent_relation(CSstate Mf(set O curtid(oscurt OwnershipReady))) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 6) /\
 (forall b off,b<>1%positive ->get Mf(b,off)=get M(b,off)).
Proof.
 destruct(PPnonempty false nil)as(Full&Trace&Held&Target&Cache).
 change(CSstate Full(RIabstract OwnershipWaiting)|=SWINVt PPinv OwnershipWaiting **PPprivate)in Held.
 apply sat_split in Held;destruct Held as(M&Mp&O&Op&JM&JO&H&Private).
 destruct(CScache_owned _ _ _ H)as[v L].
 assert(Lfull:load Tint8 Full(94%positive,0%Z)=Some v).
 { eapply load_mem_mono;[exact L|exists Mp;exact JM]. }
 assert(v=V293_byteval 6)by congruence;subst v.
 destruct(CSfields _ _ _ H)as[ts[C[T Spatial]]].
 assert(Tfull:get(RIabstract OwnershipWaiting)abstcblsid=Some(abstcblist ts)).
 { eapply join_get_get_l;[reflexivity|exact JO|exact T]. }
 pose proof(RIfixed_tasks OwnershipWaiting)as Tfixed.
 assert(ts=OwnershipTasks)by congruence;subst ts.
 assert(Highest:CSstate M O|=AHprio V293_scheduler OwnershipReady **Atrue).
 { eapply astar_mono;[apply V293_tasks_highest_spatial;exact RIhighest|intros st K;exact K|exact Spatial]. }
 pose proof H as Open;unfold PPinv in Open;apply V293_ready_storage_switch_resources in Open.
 assert(Raw:CSstate M O|=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **Atrue)by(sep auto).
 destruct(V293_ready_current_write 80%positive 81%positive 82%positive
 OwnershipWaiting OwnershipReady Atrue CGge CGle M(fun _:hid=>false)(false,nil,[false]) O
 (spec_done None)1%positive V293_tcb_type Raw eq_refl)as(Mf&S&After&Load&Outside).
 assert(Lf:load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 6)).
 { rewrite(V293_load_block_frame _ M Mf 94%positive 0%Z ltac:(intro;apply Outside;left;discriminate));exact L. }
 exists M;exists O;exists Mf;split;[exact H| ];split.
 - exists OwnershipWaiting;exists OwnershipTasks;exists 6.
   split;[exact C| ];split;[exact T| ];split;[lia| ];split;[exact L| ].
   exact(proj1(proj2 NCcurrent_mismatch)).
 - split;[exact Highest| ];split;[exact T| ];split;[exact S| ];split.
   + apply astar_r_aemp_elim.
     eapply V293_ready_storage_store_frame;[apply astar_r_aemp_intro;exact H|reflexivity|exact S].
   + split;[apply CSrelation_after_false;assumption| ];split;[exact L| ];split;[exact Lf| ].
     intros b off Apart;apply Outside;left;exact Apart.
Qed.
Theorem CSexact_strengthening_not_GoodI : forall Inv0 li,
 (forall st,st|=SWINVt PPinv OwnershipWaiting ->NCcurrent_relation st ->
   st|=SWINVt Inv0 OwnershipWaiting) ->
 (forall t st,st|=SWINVt Inv0 t ->NCcurrent_relation st) ->
 ~GoodI Inv0 V293_scheduler li.
Proof.
 intros Inv0 li Includes Coherent [_[_[Switch _]]].
 destruct CSswitch_witness as(M&O&Mf&H&Before&Highest&Tasks&S&After&NotAfter&Unchanged).
 pose proof(Includes _ H Before)as Strong.
 destruct(Switch (CGge,CGle,M,(fun _:hid=>false),(false,nil,[false])) O
 (spec_done None)OwnershipReady 1%positive V293_tcb_type Mf OwnershipWaiting
 Strong Highest eq_refl S)as[ts[T[Live|[Dead Release]]]].
 - assert(ts=OwnershipTasks)by congruence;subst ts.
   exact(NotAfter(Coherent OwnershipReady _ (proj2 Live))).
 - assert(ts=OwnershipTasks)by congruence;subst ts.
   apply Dead;exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,
     Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
Qed.
Theorem CSwithout_strengthening_good : GoodI PPinv V293_scheduler V293_shared_li.
Proof. exact PPgood. Qed.
