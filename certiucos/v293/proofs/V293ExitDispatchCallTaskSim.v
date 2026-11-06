(* Enabled dispatch: one sched API for both changed and highest-current calls. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ExitClientCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitEqualCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import Coq.Logic.Classical_Prop.

Lemma V293_self_sched_skip : forall pc A t ks cst O Of OO,
 getsched(pc,A)=V293_scheduler ->
 get O curtid=Some(oscurt t) ->V293_scheduler O t ->join O Of OO ->
 htstepstar(pc,A)t(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,ks))cst OO
 (SKIP,(kenil,ks))cst OO.
Proof.
 intros pc A t ks cst O Of OO Sched Current Highest Join.
 change(snd A=V293_scheduler)in Sched.
 eapply ht_starS.
 - eapply hapi_step;[reflexivity|apply hidapi_step].
   apply spec_seq_step2;rewrite Sched.
   eapply spec_sched_step;[exact Current|exact Highest|exact Join].
 - eapply ht_starS.
   + eapply hapi_step;[reflexivity|apply hidapi_step;apply spec_seq_step1].
   + eapply ht_starS;
      [eapply hapi_step;[reflexivity|apply hapiexit_step]|apply ht_starO].
Qed.

Lemma V293_self_sched_nil_call_bridge : forall pc po pi ip A f ks o O li I Post t,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 getsched(pc,A)=V293_scheduler ->
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 get O curtid=Some(oscurt t) ->V293_scheduler O t ->
 satp o O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,ks))o
 (pc,A)(SKIP,(kenil,ks))O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,ks))o
 (pc,A)(curs(scall f nil),(kenil,ks))O li I Post t.
Proof.
 intros pc po pi ip A f ks o O li I Post t Outside Sched Bind Current Highest Local API.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   destruct(V293_client_nil_call_low _ _ _ _ A _ _ _ _ _ _ _ OO _ Outside Low)
   as[Same[Code Match]];subst ofull Cf.
   exists(SKIP,(kenil,ks));
   exists OO;exists o;exists Ms;exists O;exists Os.
   split.
   + eapply ht_starS;[exact Match| ];eapply ht_starS;
     [apply V293_client_nil_api_enter;exact Bind| ].
     eapply V293_self_sched_skip;eassumption.
   + split;[exact JM| ];split;[exact JO| ];split;[exact Inv| ];split;assumption.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO ev Inv JM JO Low.
   inversion Low;subst;eapply False_ind;eapply V293_client_nil_call_no_event;eassumption.
 - intros Ms k x Os OO E;discriminate E.
 - intros Ms Os OO(v&E);discriminate E.
 - intros cst o2 Ms Os Mf OO Of OOO NE NS NI NF Inv JM JO JO' Bad.
   eapply V293_client_nil_call_abort;eassumption.
 - intros Ms Os e1 e2 e3 k OO E;discriminate E.
 - intros Ms Os e k OO E;discriminate E.
Qed.

Section DispatchCall.
Variables br bg bp bt bc bh bo bk bn bl bu : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable oldtarget : val.
Variable c : int32.
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.

Lemma V293_exit_active_abstract_current : forall ge le M ir aux O op n hv,
 (ge,le,M,ir,aux,O,op)|=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c n hv ->
 get O curtid=Some(oscurt t).
Proof.
 intros ge le M ir aux O op n hv Held.
 assert(Open:(ge,le,M,ir,aux,O,op)|=
  SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **Atrue).
 { unfold V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource in Held;sep auto. }
 eapply astar_mono in Open;[ |apply V293_ready_switch_full|intros st H;exact H].
 unfold V293_ready_full in Open;sep normal in Open;sep destruct Open.
 change(get(getabst(ge,le,M,ir,aux,O,op))curtid=Some(oscurt t)).
 eapply V293_star_abst_get_l with(p:=Aabsdata curtid(oscurt t))(q:=Atrue).
 - apply V293_shared_abs_get.
 - unfold V293_shared_fields in Open;sep auto.
Qed.

Lemma V293_exit_self_sched_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 getsched(pc,A)=V293_scheduler ->
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n Sched APIBind Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current Highest Bound SU SN SL UG NG LG Clear Held.
 eapply V293_self_sched_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact Sched.
 - exact APIBind.
 - eapply V293_exit_active_abstract_current;exact Held.
 - exists tasks;split;assumption.
 - eapply V293_pending_local with(op:=op);eapply V293_exit_active_current;exact Held.
 - unfold G,Cells;eapply V293_exit_equal_entry_TaskSim with(op:=op)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption.
Qed.

Theorem V293_exit_dispatch_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 getsched(pc,A)=V293_scheduler ->
 fst(fst A)f=Some((fun _:vallist=>spec_seq sched(spec_done None)),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 po helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 saved<>table ->saved<>target ->saved<>high ->saved<>current ->saved<>counter ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->
 V293_current_task tasks t nc ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (forall i,ir i=false) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n Sched APIBind Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current Bound SU SN SL UG NG LG Clear Held.
 destruct(classic(V293_highest_ready tasks t))as[Highest|NotHighest].
 - unfold G,Cells;eapply V293_exit_self_sched_client_call_TaskSim with(op:=op)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption.
 - unfold G,Cells;eapply V293_exit_client_call_TaskSim with(op:=op)(nc:=nc)
   (oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption.
Qed.
End DispatchCall.
