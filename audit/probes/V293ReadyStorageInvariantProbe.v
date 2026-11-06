(* Existing concrete source prefix, then the original primitive. No boot claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition PPcells : list(addr*type) :=
 [((91%positive,0%Z),Tint8);((94%positive,0%Z),Tint8);
  ((95%positive,0%Z),Tint32);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)].
Definition PPvalues : list V293_record_cell :=
 [((91%positive,0%Z),Tint8,V293_byteval 4);((94%positive,0%Z),Tint8,V293_byteval 6);
  ((95%positive,0%Z),Tint32,Vint32 Int.zero);((96%positive,0%Z),Tint8,V293_byteval 0);
  ((97%positive,0%Z),Tint8,V293_byteval 0)].
Definition PPinv := V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells.
Definition PPextra := V293_ready_storage_extra 106%Z V293_tcb_type PPcells.
Definition PPprivate := V293_owned_record_cell((98%positive,0%Z),Tint32,Vint32 Int.zero) ** RCframe.
Lemma PPgood : GoodI PPinv V293_scheduler V293_shared_li.
Proof. apply V293_ready_storage_good. Qed.
Lemma PPdispatch : forall ge le M ir aux O op,
 get ge 106%Z=Some(93%positive,Tptr V293_tcb_type) ->
 (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ->
 (ge,le,M,ir,aux,O,op) |= V293_dispatch_cell 106%Z V293_tcb_type.
Proof.
 intros ge le M ir aux O op Env Cell.
 exists(Vptr OwnershipReady);apply astar_l_apure_intro;[ |reflexivity].
 eapply V293_ready_named_target;[exact Env|exact Cell].
Qed.
Lemma PPclose : forall M ci,
 CGstate OwnershipWaiting M ci |=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** CGpost true 0 0 ->
 CGstate OwnershipWaiting M ci |= SWINVt PPinv OwnershipWaiting ** PPprivate.
Proof.
 intros M ci Held.
 assert(Raw:CGstate OwnershipWaiting M ci |= V293_owned_record_cells PPvalues **
   (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** PPprivate))).
 { unfold CGpost,CGframe,CGextra,PPvalues,PPprivate in *.
   cbn [V293_owned_record_cells STcache] in *;sep auto. }
 eapply astar_mono in Raw;[ |apply V293_owned_cells_storage|intros st H;exact H].
 change(CGstate OwnershipWaiting M ci |= V293_storage PPcells **
   (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** PPprivate)))in Raw.
 assert(Env:get CGge 106%Z=Some(93%positive,Tptr V293_tcb_type))by reflexivity.
 destruct (CGstate OwnershipWaiting M ci) as [[[[[[ge le] mem] ir] aux] O] op] eqn:State.
 assert(Env':get ge 106%Z=Some(93%positive,Tptr V293_tcb_type)).
 { unfold CGstate in State;inversion State;subst;exact Env. }
 assert(Named:(ge,le,mem,ir,aux,O,op) |=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_storage PPcells ** PPprivate)))by(sep auto).
 apply sat_split in Named;destruct Named as(m1&m2&o1&o2&JM&JO&Target&Rest).
 assert(Packed:(ge,le,mem,ir,aux,O,op) |= V293_dispatch_cell 106%Z V293_tcb_type **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_storage PPcells ** PPprivate))).
 { apply sat_split';exists m1;exists m2;exists o1;exists o2.
   split;[exact JM| ];split;[exact JO| ];split;[eapply PPdispatch;[exact Env'|exact Target]|exact Rest]. }
 change((ge,le,mem,ir,aux,O,op) |= SWINVt PPinv OwnershipWaiting ** PPprivate).
 eapply astar_mono with(P:=SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** PPextra)(Q:=PPprivate).
 - intros st H;apply V293_ready_storage_switch_resources;exact H.
 - intros st H;exact H.
 - unfold PPextra,V293_ready_storage_extra;clear Held Raw Rest Target;sep auto.
Qed.

(* This uses the existing actual call/guard/counter prefix, not an assumed heap. *)
Theorem PPnonempty : forall enabled ci,exists Mtail,
 V293_local_steps CGprogram(curs CGcontrol,(kenil,kstop))
 ((CGge,CGle,CGmemory OwnershipWaiting true 0 0),(fun _=>false),(enabled,nil,ci))
 (curs(sprim(switch 106%Z)),(kenil,CGpending))
 ((CGge,CGle,Mtail),(fun _=>false),(false,nil,enabled::ci)) /\
 CGstate OwnershipWaiting Mtail(enabled::ci) |= SWINVt PPinv OwnershipWaiting ** PPprivate /\
 load(Tptr V293_tcb_type)Mtail(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mtail(94%positive,0%Z)=Some(V293_byteval 6).
Proof.
 intros enabled ci;destruct(CGlocal_ready true enabled ci)as(Mtail&Trace&Held&Target&Counter&Cache).
 exists Mtail;split;[exact Trace| ];split;[apply PPclose;exact Held| ];split;assumption.
Qed.
Theorem PPactual_switch : forall enabled ci ip cst,exists Mtail Mf,
 CGstate OwnershipWaiting Mtail(enabled::ci) |= SWINVt PPinv OwnershipWaiting ** PPprivate /\
 lpstep(RCprogram,(CGpo,CGempty,ip))FCswitch_tasks cst
 (CGge,CGswitch_envs,Mtail,(fun _=>false),CGswitch_aux enabled ci)OwnershipWaiting
 (set FCswitch_tasks OwnershipWaiting(SKIP,(kenil,FCpending)))cst
 (CGge,CGswitch_envs,Mf,(fun _=>false),CGswitch_aux enabled ci)OwnershipReady /\
 (CGge,CGle,Mf,(fun _=>false),(false,nil,enabled::ci),
   set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None) |=
   SWINVt PPinv OwnershipReady ** PPprivate /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 6) /\
 ~V293_cache_current OwnershipTasks OwnershipReady Mf 94%positive.
Proof.
 intros enabled ci ip cst;destruct(PPnonempty enabled ci)as(Mtail&Trace&Held&Target&Cache).
 destruct(V293_ready_storage_switch_step 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
   RCprogram CGpo CGempty ip FCswitch_tasks cst FCpending OwnershipWaiting OwnershipReady
   93%positive 1%positive CGge CGle CGswitch_envs Mtail(fun _=>false)(false,nil,enabled::ci)
   (CGswitch_aux enabled ci)(RIabstract OwnershipWaiting)(spec_done None)PPprivate
   (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)eq_refl Target eq_refl Held)
   as(Mf&Step&Store&After&Current&Outside).
 assert(Cache':load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 6)).
 { rewrite(V293_load_block_frame _ Mtail Mf 94%positive 0%Z ltac:(intro;apply Outside;left;discriminate));exact Cache. }
 exists Mtail;exists Mf;split;[exact Held| ];split;[exact Step| ];split;[exact After| ];split;[exact Cache'| ].
 eapply V293_cache_current_mismatch with(cached:=6)(selected:=4);[lia| |exact Cache'|lia].
 split;[lia| ];exists rdy;exists Vnull;vm_compute;reflexivity.
Qed.

(* A valid typed bitmap byte is not a bitmap/task relation. Fixed witnesses,
   two heaps differing only at the ready-low byte; no codec rejection. *)
Lemma PPzero_rejects : forall ge le M ir aux O op,
 get O abstcblsid=Some(abstcblist OwnershipTasks) ->
 load Tint8 M(80%positive,0%Z)=Some(V293_byteval 0) ->
 forall t R,~(ge,le,M,ir,aux,O,op) |= SWINVt PPinv t ** R.
Proof.
 intros ge le M ir aux O op Tasks Zero t R Held.
 destruct(V293_ready_storage_selected 80%positive 81%positive 82%positive 106%Z V293_tcb_type PPcells
   t R _ Held)as(ts&lo&hi&es&next&msg&Map&Rel&Reads&Rest).
 change(get O abstcblsid=Some(abstcblist ts))in Map;assert(ts=OwnershipTasks)by congruence;subst ts.
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];destruct Reads as[Low RestReads].
 change(load Tint8 M(80%positive,0%Z)=Some(V293_byteval lo))in Low.
 assert(E:lo=0)by(eapply RTbyte_injective;[exact Lo|lia|congruence]);subst lo.
 assert(Ready:exists t m,get OwnershipTasks t=Some(Int.repr(Z.of_nat 4),rdy,m)).
 { exists OwnershipReady;exists Vnull;vm_compute;reflexivity. }
 apply(proj2(Bitmap 4 ltac:(lia)))in Ready;vm_compute in Ready;intuition lia.
Qed.
Theorem PPbitmap_control : forall enabled ci,exists Mgood Mbad,
 CGstate OwnershipWaiting Mgood(enabled::ci) |= SWINVt PPinv OwnershipWaiting ** PPprivate /\
 store Tint8 Mgood(80%positive,0%Z)(V293_byteval 0)=Some Mbad /\
 (forall a,a<>(80%positive,0%Z)->get Mbad a=get Mgood a) /\
 load Tint8 Mbad(80%positive,0%Z)=Some(V293_byteval 0) /\
 CGstate OwnershipWaiting Mbad(enabled::ci) |=
   V293_owned_record_cell((80%positive,0%Z),Tint8,V293_byteval 0) **
   (V293_storage PPcells ** (V293_owned_task_records OwnershipTasks ** Atrue)) /\
 (forall t R,~CGstate OwnershipWaiting Mbad(enabled::ci) |= SWINVt PPinv t ** R).
Proof.
 intros enabled ci;destruct(PPnonempty enabled ci)as(Mgood&Trace&Held&Target&Cache).
 pose proof Held as Open.
 eapply astar_mono in Open;[ |intros st H;apply V293_ready_storage_switch_resources in H;exact H|intros st H;exact H].
 eapply astar_mono in Open;[ |apply astar_mono;[apply V293_ready_switch_full|intros st H;exact H]|intros st H;exact H].
 unfold V293_ready_full,V293_ready_payload,V293_ready_owned in Open;sep normal in Open;sep destruct Open.
 assert(Fixed:x=OwnershipTasks).
 { assert(Map:get(RIabstract OwnershipWaiting)abstcblsid=Some(abstcblist x)).
   { change(get(getabst(CGstate OwnershipWaiting Mgood(enabled::ci)))abstcblsid=Some(abstcblist x)).
     eapply V293_star_abst_get_l with(p:=Aabsdata abstcblsid(abstcblist x))(q:=Atrue).
     - apply V293_shared_abs_get.
     - unfold V293_shared_fields in Open;clear Held;sep auto. }
   pose proof(RIfixed_tasks OwnershipWaiting);congruence. }subst x.
 assert(Raw:CGstate OwnershipWaiting Mgood(enabled::ci) |=
   V293_owned_record_cell((80%positive,0%Z),Tint8,V293_byteval x3) **
   (V293_storage PPcells ** (V293_owned_task_records OwnershipTasks ** Atrue))).
 { unfold V293_ready_cells,PPextra,V293_ready_storage_extra in Open.
   cbn [V293_owned_record_cells app] in Open;clear Held;sep auto. }
 unfold CGstate in Raw.
 destruct(V293_owned_byte_update _ _ 0 _ _ _ _ _ _ _ _ ltac:(lia) Raw)as[[old Writable]After].
 set(Mbad:=V293_put_byte Mgood(80%positive,0%Z)0)in *.
 assert(Zero:load Tint8 Mbad(80%positive,0%Z)=Some(V293_byteval 0)).
 { apply V293_put_byte_load;lia. }
 exists Mgood;exists Mbad;split;[exact Held| ];split.
 - apply V293_put_byte_store with(old:=old);exact Writable.
 - split.
   + intros a Apart;apply V293_put_byte_other;exact Apart.
   + split;[exact Zero| ];split;[exact After| ].
     intros t R;eapply PPzero_rejects;[apply RIfixed_tasks|exact Zero].
Qed.
