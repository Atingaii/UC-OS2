(* Actual pint and an existing global lift of the same builder dispatch prefix.
   Finite execution only; no handler-level interleaving simulation. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderDispatchSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section BuilderGlobal.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Theorem V293_builder_dispatch_global_prefix : forall intspec i si t lg pre aop ge M O pc po pi ip T les aus cst interrupted ike caller ks (sd:ossched)
 entry exit vector saved table high current counter sched_id unmap group rows y bo tasks nc,
 get T t=Some(interrupted,(ike,ks)) ->get les t=Some caller ->get aus t=Some((true,si,nil):localst) ->
 goodks(pc,(po,pi,ip))(kint interrupted ike caller ks) ->
 higherint(fun _=>false)i ->i<INUM ->ip i=Some(V293_irq_source_wrapper entry exit vector) ->
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec (fun _=>false) si Inv0 li t lg ->(ge,emp,M,isrupd(fun _=>false)i true,(false,i::si,nil),O,aop)|=pre ->
 V293_control_capture brun bn bl(ge,emp,M,isrupd(fun _=>false)i true,(false,i::si,nil),O,aop)=Some(O,V293_control 1 0 0) ->
 (pumerge po pi)entry=Some(V293_OSIntEnter_function running nesting) ->
 (pumerge po pi)exit=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id
   (V293_interrupt_handoff high current target)) ->
 (pumerge po pi)sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->bc<>bn ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->
 get ge counter=Some(bk,Tint32) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks t nc ->
 ~V293_highest_ready tasks t ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval nc) ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 exists bs next nh Mf,
 next<>t /\ nh<>nc /\ V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 let entered:=(set T t(curs(V293_irq_source_wrapper entry exit vector),(kenil,kint interrupted ike caller ks)),
 (ge,set les t emp,M,isrupd(fun _=>false)i true,set aus t(false,i::si,nil)),t)in
 let cut:=(set T t(V293_enclose (curs(sprim(switch target)),(kenil,
   kseq(sprim excrit)(kseq sret(kcall exit
    (V293_exit_boundary_body running nesting lock saved table high target current counter sched_id
      (V293_interrupt_handoff high current target))emp(kseq(sprim exint)kstop))))) (kint interrupted ike caller ks)),
 (ge,set les t(V293_cpu_lenv saved bs),Mf,(fun _=>false),set aus t(false,i::si,[false])),t)in
 (match entered with(Ti,Si,ti)=>lpstep(pc,(po,pi,ip))T cst(ge,les,M,(fun _=>false),aus)t Ti cst Si ti end) /\
 V293_global_steps(pc,(po,pi,ip))cst entered cut /\
 (ge,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),O,aop)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **
 (V293_irq_controls brun bn bl 1 0 0 **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **Atrue))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval nh) /\
 V293_control_capture brun bn bl
 (ge,V293_cpu_lenv saved bs,Mf,(fun _=>false),(false,i::si,[false]),O,aop)=
 Some(O,V293_control 1 0 0).
Proof.
 intros intspec i si t lg pre aop ge M O pc po pi ip T les aus cst interrupted ike caller ks sd
 entry exit vector saved table high current counter sched_id unmap group rows y bo tasks nc
 Code Env Aux Good Higher Inum Installed Lookup Pre Held Capture Enter Exit Scheduler Names YU YG YR YH YT HP NT CN
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Cache LookupTable Vector Range.
 destruct(V293_builder_dispatch_prefix target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 intspec i si t lg pre aop (ge,emp,M,isrupd(fun _=>false)i true,(false,i::si,nil),O,aop)(pumerge po pi)sd
 entry exit vector saved table high current counter sched_id unmap group rows y bo tasks nc
 Lookup Pre Held Capture Enter Exit Scheduler Names YU YG YR YH YT HP NT CN
 GU GG GR GH GT GO GN GL GRun GC GCount Map Current NotHighest Cache LookupTable Vector Range)
 as(bs&next&nh&Mf&Different&Changed&Highest&Next&Trace&Post&Pointer&CacheF&Captured).
 pose proof(V293_interrupt_local_steps_global pc po pi ip _ _ _ _ Trace
 interrupted ike caller ks T les aus t cst Good)as Global.
 exists bs;exists next;exists nh;exists Mf.
 split;[exact Different| ];split;[exact Changed| ];split;[exact Highest| ];split;[exact Next| ].
 cbn zeta;split;[eapply V293_interrupt_source_enter;eassumption| ].
 split;[exact Global| ];split;[exact Post| ];split;[exact Pointer| ];split;assumption.
Qed.
End BuilderGlobal.
