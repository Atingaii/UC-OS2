(* Same builder heap, enabled source prefix and original switch match.
   Cache/lookup coherence is explicit; no full handler simulation is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlSwitchSimulation.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlScheduler.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_builder_named_cell_address : forall target tp v b ge le M ir aux O op R,
 get ge target=Some(b,Tptr tp) ->
 (ge,le,M,ir,aux,O,op)|=(GV target @ (Tptr tp) |-> v) ** R ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)(Tptr tp)true v ** R.
Proof.
 intros target tp v b ge le M ir aux O op R G H.
 apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&Cell&Frame).
 destruct(V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell)as(b'&G'&Map&Empty).
 assert(b'=b)by congruence;subst b'.
 apply sat_split';exists m1;exists m2;exists o1;exists o2;split;[exact JM| ];split;[exact JO| ];split;[exact(conj Map Empty)|exact Frame].
Qed.

Section BuilderDispatch.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.
Definition V293_builder_dispatch_frame :=
 V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) **
 (V293_storage rest ** Atrue).
Lemma V293_builder_dispatch_frame_good : GoodInvAsrt V293_builder_dispatch_frame.
Proof. split;[apply V293_storage_good|split;[apply V293_storage_good|exact I]]. Qed.

(* The old storage invariant gives types and write ownership, not cache
   coherence. The cache read below is an independent, visible obligation. *)
Lemma V293_builder_dispatch_resources : forall aop i si t ge M O bo nc,
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 (ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 snapshot 1 1 0 aop false(fun _=>false)(i::si)nil t ->
 exists high targetv c,
 (ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bh,0%Z),Tint8,high) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,targetv) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_builder_dispatch_frame))))))).
Proof.
 intros aop i si t ge M O bo nc Target Cache Held.
 assert(Convert:Aisr(fun _:hid=>false) ==>isrclr).
 { intros s H;exists(fun _:hid=>false);split;[exact H| ].
   apply apure_intro;[exact(proj2(@aisr_elim s (fun _:hid=>false) H))|reflexivity]. }
 assert(Raw:(ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 Aisr(fun _:hid=>false) **
 (Aie false ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (CurTid t ** (V293_dispatch_cell target V293_tcb_type **
 (V293_storage(V293_ready_irq_prefix bt bh bc bk) **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) **(V293_storage rest **Atrue)))))))))).
 { clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
   V293_quiet_irq_kept,p_local,LINV,V293_irq_bound_li in Held;sep auto. }
 eapply astar_mono in Raw;[ |exact Convert|intros s H;exact H].
 apply astar_l_atopis_intro with(i:=i)in Raw;[ |reflexivity].
 assert(Pack:(ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 (V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_core br bg bp) **
 (CurTid t ** (V293_dispatch_cell target V293_tcb_type **
 (V293_storage(V293_ready_irq_prefix bt bh bc bk) **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) **(V293_storage rest **Atrue)))))))).
 { clear Held;unfold V293_shared_flags;sep auto. }
 eapply astar_mono in Pack;[ |apply V293ReadyTaskInvariant.V293_ready_switch_close|intros s H;exact H].
 unfold V293_ready_irq_prefix in Pack;cbn[V293_storage]in Pack.
 unfold V293_storage_cell,V293_dispatch_cell in Pack;sep normal in Pack;sep destruct Pack.
 assert(Named:(ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 (GV target @ (Tptr V293_tcb_type) |-> x) **
 ([|rule_type_val_match (Tptr V293_tcb_type) x=true|] **
 ([|rule_type_val_match Tint8 x1=true|] **
 ([|rule_type_val_match Tint8 x2=true|] **
 ([|rule_type_val_match Tint32 x0=true|] **
 (SWINV(V293ReadyTaskInvariant.V293_ready_inv br bg bp) ** (CurTid t **
 (Amapsto(bh,0%Z)Tint8 true x1 ** (Amapsto(bc,0%Z)Tint8 true x2 **
 (Amapsto(bk,0%Z)Tint32 true x0 **
 (V293_storage(V293_array_cells bt 0 1 Tint8(length V293_ready_table)) **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval 0) **(V293_storage rest **Atrue))))))))))))))).
 { clear Held Raw;sep auto. }
 pose proof(V293_builder_named_cell_address _ _ _ _ _ _ _ _ _ _ _ _ Target Named)as Addr.
 assert(Typed:(ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop)|=
 [|rule_type_val_match Tint32 x0=true|] ** Atrue)by(sep auto).
 apply astar_l_apure_elim in Typed;destruct Typed as[Typed _].
 destruct x0;cbn in Typed;try discriminate.
 assert(Read:load Tint8 M(bc,0%Z)=Some x2).
 { eapply V293_record_star_load_l with
   (s:=(ge,emp,M,(fun _=>false),(false,i::si,nil),O,aop))
   (P:=V293_owned_record_cell((bc,0%Z),Tint8,x2))(Q:=Atrue).
   - apply V293_owned_record_cell_load.
   - unfold V293_owned_record_cell;sep auto. }
 assert(x2=V293_byteval nc)by congruence;subst x2.
 exists x1;exists x;exists i0.
 unfold SWINVt,V293_owned_record_cell,V293_builder_dispatch_frame.
 assert(Byte0:rule_type_val_match Tint8(V293_byteval 0)=true)by(apply V293_byte_type;lia).
 assert(Byte1:rule_type_val_match Tint8(V293_byteval 1)=true)by(apply V293_byte_type;lia).
 clear Held Raw Pack Named Read Cache;unfold CurTid in Addr;sep auto.
Qed.
(* Cache coherence and table contents are stated on the builder's input
   heap. Enter's byte frame transports them, rather than re-assuming them. *)
Theorem V293_builder_dispatch_prefix : forall intspec i si t lg pre aop st P (sd:ossched)
 entry exit vector saved table high current counter sched_id unmap group rows y bo tasks nc,
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec (fun _=>false) si Inv0 li t lg ->st|=pre ->
 V293_control_capture brun bn bl st=Some(getabst st,V293_control 1 0 0) ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 P exit=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
   (V293_interrupt_handoff high current target)) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->bc<>bn ->
 get(getgenv st)unmap=Some(bt,Tarray Tint8 256) ->get(getgenv st)group=Some(bg,Tint8) ->
 get(getgenv st)rows=Some(br,Tarray Tint8 2) ->get(getgenv st)high=Some(bh,Tint8) ->
 get(getgenv st)table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get(getgenv st)target=Some(bo,Tptr V293_tcb_type) ->
 get(getgenv st)nesting=Some(bn,Tint8) ->get(getgenv st)lock=Some(bl,Tint8) ->
 get(getgenv st)running=Some(brun,Tint8) ->get(getgenv st)current=Some(bc,Tint8) ->
 get(getgenv st)counter=Some(bk,Tint32) ->
 get(getabst st)abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks t nc ->
 ~V293_highest_ready tasks t ->
 load Tint8(getmem st)(bc,0%Z)=Some(V293_byteval nc) ->
 (forall n,n<256 ->load Tint8(getmem st)(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 exists bs next nh Mf,
 next<>t /\ nh<>nc /\ V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(sprim(switch target)),(kenil,
   kseq(sprim excrit)(kseq sret(kcall exit
    (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
      (V293_interrupt_handoff high current target))emp(kseq(sprim exint)kstop)))))
 ((getgenv st,V293_cpu_lenv saved bs,Mf),(fun _=>false),(false,i::si,[false])) /\
 (getgenv st,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),getabst st,aop)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_irq_controls brun bn bl 1 0 0 **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **Atrue))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval nh) /\
 V293_control_capture brun bn bl
 (getgenv st,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),getabst st,aop)=
 Some(getabst st,V293_control 1 0 0).
Proof.
 intros intspec i si t lg pre aop st P sd entry exit vector saved table high current counter sched_id
 unmap group rows y bo tasks nc Lookup Pre Held Capture Enter Exit Scheduler Names YU YG YR YH YT HP NT CN
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Cache LookupTable Vector Range.
 destruct(V293_builder_enter_prefix target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i(fun _=>false)si t lg pre aop st P sd entry exit vector Lookup Pre Held Enter Vector Range)
 as(c&Me&Valid&Captured&Prefix&After&Read&Step&Frame).
 rewrite Capture in Captured;inversion Captured;subst c.
 rewrite(V293_irq_clear_update(fun _=>false)i ltac:(reflexivity))in Prefix,After.
 change((getgenv st,emp,Me,(fun _=>false),(false,i::si,nil),getabst st,aop)|=
 snapshot 1 1 0 aop false(fun _=>false)(i::si)nil t)in After.
 assert(CacheE:load Tint8 Me(bc,0%Z)=Some(V293_byteval nc)).
 { etransitivity;[apply V293_load_block_frame;intro z;apply Frame;congruence|exact Cache]. }
 assert(TableE:forall n,n<256 ->load Tint8 Me(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n N;etransitivity;[apply V293_load_block_frame;intro z;apply Frame;congruence|apply LookupTable;exact N]. }
 destruct(V293_builder_dispatch_resources _ _ _ _ _ _ _ _ _ GO CacheE After)as(oldhigh&oldtarget&c&Resources).
 destruct(V293_exit_boundary_entry_local br bg bp P(kseq(sprim exint)kstop)(getgenv st)emp Me
 (fun _=>false)false(i::si)nil(getabst st)aop t V293_builder_dispatch_frame tasks nc
 exit sched_id unmap group rows high y table target nesting lock running saved current counter
 (V293_interrupt_handoff high current target)bt bh bo bn bl brun bc bk c oldhigh oldtarget
 Exit Scheduler Names YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC GCount
 Map Current NotHighest V293_builder_dispatch_frame_good TableE Resources)
 as(bs&next&nh&Mx&Fresh&Next&Changed&Highest&NextCurrent&ExitTrace&ExitPost&Pointer&Count&OldCache&Alive&Outside).
 set(K:=kseq(sprim excrit)(kseq sret(kcall exit
    (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
      (V293_interrupt_handoff high current target))emp(kseq(sprim exint)kstop)))).
 set(R:=V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **V293_builder_dispatch_frame))))).
 assert(CopyPre:(getgenv st,V293_cpu_lenv saved bs,Mx,(fun _=>false),(false,i::si,[false]),getabst st,aop)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **R)))).
 { clear Resources After Held;unfold R;sep auto. }
 assert(SH:saved<>high)by(intro E;apply Names;subst;cbn;tauto).
 assert(SC:saved<>current)by(intro E;apply Names;subst;cbn;tauto).
 assert(LH:get(V293_cpu_lenv saved bs)high=None).
 { unfold V293_cpu_lenv;rewrite map_get_set' by exact SH;apply map_emp_get. }
 assert(LC:get(V293_cpu_lenv saved bs)current=None).
 { unfold V293_cpu_lenv;rewrite map_get_set' by exact SC;apply map_emp_get. }
 destruct(V293_handoff_copy_execution br bg bp P K(getgenv st)(V293_cpu_lenv saved bs)Mx
 (fun _=>false)(false,i::si,[false])(getabst st)aop t R high current target bh bc bo nh nc next
 ltac:(pose proof(proj1 NextCurrent);lia)LH LC GH GC CopyPre)as(Mf&CopyTrace&Store&CopyPost&CopyFrame).
 assert(Final:(getgenv st,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),getabst st,aop)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_irq_controls brun bn bl 1 0 0 **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **Atrue)))).
 { clear Resources After Held ExitPost CopyPre;unfold R,V293_irq_controls,V293_owned_record_cell in CopyPost|-*;sep auto. }
 assert(PtrF:load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next)).
 { eapply V293_record_star_load_l with
   (s:=(getgenv st,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),getabst st,aop))
   (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next))(Q:=Atrue).
   - apply V293_owned_record_cell_load.
   - clear Resources After Held ExitPost CopyPre;sep auto. }
 assert(CacheF:load Tint8 Mf(bc,0%Z)=Some(V293_byteval nh)).
 { eapply V293_record_star_load_l with
   (s:=(getgenv st,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),getabst st,aop))
   (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nh))(Q:=Atrue).
   - apply V293_owned_record_cell_load.
   - clear Resources After Held ExitPost CopyPre;sep auto. }
 exists bs;exists next;exists nh;exists Mf.
 split;[exact Next| ];split;[exact Changed| ];split;[exact Highest| ];split;[exact NextCurrent| ];split.
 - eapply V293_local_trans;[exact Prefix| ];eapply V293_local_trans;[exact ExitTrace| ];
   apply V293_csteps_local;exact CopyTrace.
 - split;[exact Final| ];split;[exact PtrF| ];split;[exact CacheF| ].
   eapply V293_switch_owned_capture;try exact Final;lia.
Qed.
End BuilderDispatch.
