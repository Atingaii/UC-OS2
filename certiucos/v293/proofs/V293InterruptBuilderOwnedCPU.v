(* Keep the allocated CPU cell in the source-prefix postcondition.
   No restoration or automatic schedule-back is asserted. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderDispatchSwitch.
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

Section BuilderOwnedCPU.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.
Let kept:=V293_builder_dispatch_frame bt rest.
Theorem V293_builder_dispatch_owned_cpu_prefix : forall intspec i si t lg pre aop st P (sd:ossched)
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
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)))) /\
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
 destruct(V293_builder_dispatch_resources target running nesting lock bt bg br bh bp bc bk brun bn bl rest _ _ _ _ _ _ _ _ _ GO CacheE After)as(oldhigh&oldtarget&c&Resources).
 destruct(V293_exit_boundary_entry_local br bg bp P(kseq(sprim exint)kstop)(getgenv st)emp Me
 (fun _=>false)false(i::si)nil(getabst st)aop t kept tasks nc
 exit sched_id unmap group rows high y table target nesting lock running saved current counter
 (V293_interrupt_handoff high current target)bt bh bo bn bl brun bc bk c oldhigh oldtarget
 Exit Scheduler Names YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC GCount
 Map Current NotHighest (V293_builder_dispatch_frame_good bt rest) TableE Resources)
 as(bs&next&nh&Mx&Fresh&Next&Changed&Highest&NextCurrent&ExitTrace&ExitPost&Pointer&Count&OldCache&Alive&Outside).
 set(K:=kseq(sprim excrit)(kseq sret(kcall exit
    (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
      (V293_interrupt_handoff high current target))emp(kseq(sprim exint)kstop)))).
 set(R:=V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **kept))))).
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
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue))))).
 { clear Resources After Held ExitPost CopyPre;unfold R,kept,V293_irq_controls,V293_owned_record_cell in CopyPost|-*;sep auto. }
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
End BuilderOwnedCPU.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293ResumedReturnProgSim.
Require Import CertiOS.framework.proof.simulation.

(* At a genuine resumed pending exit, consume ownership instead of requiring
   an independently guessed free result. Caller simulation is still required. *)
Theorem V293_pending_exit_owned_progsim :
 forall pc po pi ip T cst t ge les M ir aus si cs f body caller tail
 tau d1 d2 saved b ph Th O op R,
 po f=Some(tau,d1,d2,body) ->
 get T t=Some(SKIP,(kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail)))) ->
 get les t=Some(V293_cpu_lenv saved b) ->
 get aus t=Some((false,si,false::cs):localst) ->
 (ge,V293_cpu_lenv saved b,M,ir,(false,si,false::cs),O,op)|=
 Amapsto(b,0%Z)Tint32 true(Vint32 Int.zero) **R ->
 get O curtid=Some(oscurt t) ->
 (forall Mf,free Tint32 b M=Some Mf ->
  (ge,V293_cpu_lenv saved b,Mf,ir,(false,si,false::cs),O,op)|=R ->
  ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,tail)))
  (ge,set les t caller,Mf,ir,set aus t(false,si,cs))ph Th O cst t) ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge les M ir aus si cs f body caller tail
 tau d1 d2 saved b ph Th O op R Bind Code Local Aux Owned Cur Post.
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Owned)as(Mf&Free&Rest).
 eapply V293_pending_exit_progsim;try eassumption.
 apply Post;assumption.
Qed.

(* A one-bit physical permission edit, not a program edit. All bytes and
   other locations stay fixed; a successful load cannot justify free. *)
Lemma V293_cpu_first_permission : forall M b v,
 get M(b,0%Z)=Some(true,v) ->
 load Tint32(set M(b,0%Z)(false,v))(b,0%Z)=load Tint32 M(b,0%Z) /\
 free Tint32 b(set M(b,0%Z)(false,v))=None /\
 (forall a,a<>(b,0%Z) ->get(set M(b,0%Z)(false,v))a=get M a).
Proof.
 intros M b v Read;split.
 - unfold load,loadm;cbn[typelen loadbytes].
   rewrite map_get_set;rewrite !map_get_set' by(intro E;inversion E;lia).
   now setoid_rewrite Read.
 - split.
   + unfold free;cbn[typelen freeb];rewrite map_get_set;reflexivity.
   + intros;apply map_get_set';congruence.
Qed.
