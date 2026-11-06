Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
(* Literal uninitialized entry; actual prefix and conditional two-Hook return chain. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293PublishReturnRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293InitPublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Import ListNotations.

Require Import CertiOS.audit.probes.V293InitPublishRecordsProbe.
Require Import CertiOS.audit.probes.V293TCBInitTickZeroProbe.
Require Import CertiOS.audit.probes.V293TCBInitFieldsProbe.
Require Import CertiOS.certiucos.v293.proofs.V293PublishedTickResources.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitTickZero.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Local Open Scope nat_scope.
Definition PTChainOwned M:=ChainState M |=V293_published_tick_owned ChainUpdated
 301%positive 128 401%positive ChainOldTid
 (V293_tcb_tick_spares 301%positive 128 Vnull Vnull(Vint32 Int.zero)(Vint32 Int.zero)Vnull(Vint32 Int.zero))
 (tl ChainFinalLinks)
 ([((405%positive,0%Z),Tptr V293_tcb_type,Vnull);
 ((406%positive,44%Z),Tptr V293_tcb_type,Vptr ChainNewTid)]++ChainSentinel).
Theorem PTcreation_under_hooks : forall P f hi hc ks enabled si ci,
 ChainHooks P f hi hc ks enabled si ci false -> ChainHooks P f hi hc ks enabled si ci true -> exists Mf,
 V293_local_steps P (curs(ChainCode hi hc),(kenil,kcall f (V293_TCBInit_function_body hi hc) ChainCaller ks))
 ((ChainGE,ChainLE,ChainMemory ChainCells),(fun _=>false),(enabled,si,ci))
 (curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ChainGE,ChainCaller,Mf),(fun _=>false),(enabled,si,ci)) /\
 (ChainState Mf |= ChainPost) /\ ChainFreed Mf /\ PTChainOwned Mf.
Proof.
 intros P f hi hc ks enabled si ci Hook1 Hook2.
 eapply (V293_TCBInit_returns_published_zero_under_hooks ChainTasks P f hi hc ChainCaller ks ChainGE
 (ChainMemory ChainCells) (fun _=>false) (false,nil,nil) (emp:osabst) (spec_done None) enabled si ci
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive 208%positive 209%positive
 405%positive 406%positive 301%positive 128%Z 401%positive 402%positive 403%positive 404%positive
 301%positive 8%Z 11 2 16 1 Vnull Vnull (Vint32 Int.zero) (Vint32 Int.zero) Vnull (Vint32 Int.zero)
 Vundef Vnull (fun _=>Vundef) Vnull Vnull Vnull ChainSentinel);
 try lia;try (change (128+55<=4294967295)%Z;lia);try (change (8+24<=4294967295)%Z;lia).
 - reflexivity.
 - reflexivity.
 - exact ChainEnvironment.
 - reflexivity.
 - repeat constructor;cbn;intuition congruence.
 - repeat split;reflexivity.
 - reflexivity.
 - intros t value Member. change (In (t,value)
    [(ChainOldTid,(Int.repr 12,rdy,Vnull));(ChainNewTid,(Int.repr 11,rdy,Vnull))]) in Member.
   destruct Member as [Same |[Same |Impossible]];[inversion Same;subst |inversion Same;subst |contradiction];
   cbn [ChainOldTid ChainNewTid fst V293_tcb_function_blocks In];intuition discriminate.
 - intros a tp v Member. cbn [V293_pub_link_cells tl app V293_prio_row ChainSentinel
   V293_tcb_init_record_remainder In] in Member.
   repeat destruct Member as [E |Member];try contradiction;inversion E;subst;
   cbn [fst V293_tcb_function_blocks In];intuition discriminate.
 - exact Hook1.
 - exact Hook2.
 - exact ChainSpatialEntry.
Qed.

(* A literal downstream heap, not a claim of unconditional hook reachability.
   Reuse the previous complete candidate and add only the published head. *)
Definition PTcells d:list V293_record_cell:=
 ((701%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8))::TZcells d.
Definition PTmemory d:=InitMemory(PTcells d).
Definition PTge:env:=sig 900%Z(701%positive,Tptr V293_tcb_type).
Definition PTstate M:=V293_wstate PTge InitLE M.
Definition PThead:=V293_owned_record_cell
 ((701%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8)).
Definition PTrecord:=V293_owned_task_record(301%positive,Int.repr 8)(Int.repr 11)rdy Vnull.
Definition PTcanary:=V293_owned_record_cell((601%positive,0%Z),Tint32,Vint32(Int.repr 77)).
Definition PTowned d:=PThead **TZcandidate_owned d.

Lemma PTliteral : forall d,PTstate(PTmemory d)|=V293_rdy_raw_cells(PTcells d)Aemp.
Proof.
 intro d;unfold PTstate,PTmemory.
 cbn[PTcells TZcells TZcanonical app InitMemory V293_rdy_raw_cells].
 repeat match goal with
 |-V293_wstate _ _ (merge(V293_encoded_memory ?b ?off true ?bytes)_) |=_ =>
 let count:=eval cbn[length TZnext V293_byteval encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map] in (Z.of_nat(length bytes)) in
 eapply V293_wstate_star with(m1:=V293_encoded_memory b off true bytes);
 [TZapart b off count|split;[apply V293_encoded_memory_mapsto|reflexivity]| ]
 end.
 split;reflexivity.
Qed.

Lemma PTvalid : forall d,PTstate(PTmemory d)|=PTowned d.
Proof.
 intro d;pose proof(PTliteral d)as Held.
 apply(V293_raw_record_ownership(PTcells d)Aemp
 ltac:(unfold PTcells,TZcells,TZcanonical;repeat constructor;reflexivity))in Held.
 assert(Layout:TZcanonical=V293_record_layout(301%positive,Int.repr 8)11 rdy Vnull 0)by reflexivity.
 unfold PTcells,TZcells in Held;rewrite Layout in Held.
 assert(Cells:PTstate(PTmemory d)|=PThead **
 (V293_owned_record_cells(V293_record_layout(301%positive,Int.repr 8)11 rdy Vnull 0) **
 (V293_owned_record_cell((301%positive,52%Z),Tint32,Vint32 d) **
 (V293_owned_record_cell((301%positive,28%Z),Tcom_ptr 410%Z,Vptr TZnext) **
 (V293_owned_record_cell((201%positive,0%Z),Tptr V293_tcb_type,Vptr(301%positive,Int.repr 8)) **PTcanary))))).
 { unfold PThead,PTcanary;cbn[V293_record_layout V293_owned_record_cells app fst snd]in Held|-*;
   clear -Held;sep auto. }
 unfold PTowned,TZcandidate_owned.
 eapply astar_mono;[intros st HS;exact HS| |exact Cells].
 eapply astar_mono;[ |intros st HS;exact HS].
 intros st HS;exists 11;exists 0;apply astar_l_apure_intro;[exact HS|repeat split;try reflexivity;lia].
Qed.

Theorem PTactual_head_then_tick : forall P ks enabled,exists Mh Mf,
 store(Tptr V293_tcb_type)(PTmemory Int.zero)(201%positive,0%Z)
 (Vptr(301%positive,Int.repr 8))=Some Mh /\
 store(Tptr V293_tcb_type)Mh(201%positive,0%Z)(Vptr TZnext)=Some Mf /\
 V293_local_steps P
 (curs(sseq(sassign(evar 101%Z)(evar 900%Z))(V293_tick_iteration 101%Z 901%Z 902%Z)),(kenil,ks))
 ((PTge,InitLE,PTmemory Int.zero),(fun _=>false),(enabled,nil,nil))
 (curs(sskip None),(kenil,ks))((PTge,InitLE,Mf),(fun _=>false),(enabled,nil,nil)) /\
 (PTge,InitLE,Mf,(fun _=>false),(enabled,nil,nil),(emp:osabst),(spec_done None))|=
 V293_owned_record_cell((201%positive,0%Z),Tptr V293_tcb_type,Vptr TZnext) **
 (PThead **(V293_tick_zero_node 301%positive 8 TZnext **(PTrecord **PTcanary))) /\
 load(Tptr V293_tcb_type)Mf(201%positive,0%Z)=Some(Vptr TZnext) /\
 (forall b i,b<>201%positive \/(i<0)%Z \/(4<=i)%Z ->get Mf(b,i)=get(PTmemory Int.zero)(b,i)).
Proof.
 intros P ks enabled.
 assert(Held:(PTge,InitLE,PTmemory Int.zero,(fun _=>false),(enabled,nil,nil),(emp:osabst),(spec_done None))|=
 Amapsto(201%positive,0%Z)(Tptr V293_tcb_type)true(Vptr(301%positive,Int.repr 8)) **
 (PThead **(V293_tick_zero_node 301%positive 8 TZnext **(PTrecord **PTcanary)))).
 { pose proof(PTvalid Int.zero)as Owned.
   assert(Stable:(PTge,InitLE,PTmemory Int.zero,(fun _=>false),(enabled,nil,nil),(emp:osabst),(spec_done None))|=PTowned Int.zero).
   { eapply good_inv_prop;[ |exact Owned].
     unfold PTowned,TZcandidate_owned,PThead,V293_owned_task_record,V293_owned_record_cell.
     cbn;repeat split;intros;repeat split;exact I. }
   unfold PTowned,TZcandidate_owned,PTrecord,PTcanary,V293_tick_zero_node in Stable|-*.
   unfold V293_owned_record_cell in Stable|-*.
   clear -Stable;sep auto. }
 exact(V293_published_head_then_zero_iteration P ks PTge InitLE(PTmemory Int.zero)
 (fun _=>false)enabled nil nil(emp:osabst)(spec_done None)
 101%Z 900%Z 901%Z 902%Z 201%positive 701%positive 301%positive 8 TZnext
 (Vptr(301%positive,Int.repr 8))(PTrecord **PTcanary)
 eq_refl eq_refl eq_refl ltac:(lia)ltac:(change(8+44<=4294967295)%Z;lia)Held).
Qed.

Lemma PTdelay : forall d,load Tint32(PTmemory d)(301%positive,52%Z)=Some(Vint32 d).
Proof.
 intro d;change(load Tint32(getmem(PTstate(PTmemory d)))(301%positive,52%Z)=Some(Vint32 d)).
 eapply V293_rdy_raw_load;[ |reflexivity|apply PTliteral].
 unfold PTcells,TZcells;right;apply in_or_app;right;left;reflexivity.
Qed.

Theorem PThook_zero_resource_necessary :
 PTstate(PTmemory(Int.repr 3))|=PTowned(Int.repr 3) /\
 ~(PTstate(PTmemory(Int.repr 3))|=V293_tick_zero_node 301%positive 8 TZnext **Atrue).
Proof.
 split;[apply PTvalid| ];intro Held;unfold V293_tick_zero_node in Held.
 assert(Zero:load Tint32(PTmemory(Int.repr 3))(301%positive,52%Z)=Some(Vint32 Int.zero)).
 { change(load Tint32(getmem(PTstate(PTmemory(Int.repr 3))))(301%positive,52%Z)=Some(Vint32 Int.zero)).
   eapply V293_record_star_load_l;[ |exact Held];eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 rewrite PTdelay in Zero;discriminate.
Qed.

Theorem PTzero_gate_passes :
 PTstate(PTmemory Int.zero)|=PTowned Int.zero /\
 PTstate(PTmemory Int.zero)|=V293_tick_zero_node 301%positive 8 TZnext **Atrue.
Proof.
 split;[apply PTvalid| ];pose proof(PTvalid Int.zero)as Held.
 unfold PTowned,TZcandidate_owned,V293_tick_zero_node in *;clear -Held;sep auto.
Qed.

Theorem PTsingle_factor_outside : forall d1 d2 b i,
 b<>301%positive \/(i<52)%Z \/(56<=i)%Z ->
 get(PTmemory d1)(b,i)=get(PTmemory d2)(b,i).
Proof.
 intros d1 d2 b i Outside;unfold PTmemory;cbn[PTcells InitMemory].
 eapply TZmerge_lookup;[reflexivity|apply TZsingle_factor_outside;exact Outside].
Qed.
