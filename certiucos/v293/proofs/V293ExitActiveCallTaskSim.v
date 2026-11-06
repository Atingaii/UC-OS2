(* Active normalized OSIntExit call: saved initialization, running guard, and critical suffix. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Local Open Scope nat_scope.

Lemma V293_exit_saved_assignment_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M M' ir ci e1 e2 b v,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evaltype e1(ge,le,M)=Some Tint32 ->
 evaladdr e1(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 evaltype e2(ge,le,M)=Some Tint32 ->evalval e2(ge,le,M)=Some v ->
 store Tint32 M(b,0%Z)v=Some M' ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 satp(ge,le,M',ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,M',ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sassign e1 e2),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M M' ir ci e1 e2 b v
 Context TL Addr TR Value Store Before After Tail.
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(cure e2,(kenil,kassignr e1 Tint32 ks)));
 [exact Context|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;eapply stmt_step;[reflexivity| ];eapply sassign_step.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TL.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TR.
   + apply eq_int;auto.
 - eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil);
   [ |reflexivity| |exact Before| ].
   + apply cstepLib.evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks)
     (C':=(cure(eaddrof e1),(kenil,kassignl v Tint32 ks)));
     [exact Context|reflexivity|reflexivity| | |exact Before| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(b,Int.zero)))))(ke':=kenil);
       [ |reflexivity| |exact Before| ].
       -- apply cstepLib.evaladdr_imply_estepstar;exact Addr.
       -- eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
       -- eapply V293_invariant_cstep_TaskSim;[ | | |exact After|exact Tail].
          ++ eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
          ++ intros[x E];discriminate E.
          ++ intros Mf Mall Join;destruct(lmachLib.store_mono _ _ _ _ _ _ _ Join Store)as(Mall'&WholeStore).
             exists Mall';split.
             ** apply map_join_comm;eapply join_store_join;[apply map_join_comm;exact Join|exact Store|exact WholeStore].
             ** split.
                --- eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact WholeStore.
                --- intros;eapply V293_store_cstep_unique;[exact WholeStore|eassumption].
Qed.


Lemma V293_exit_saved_successor : forall p y ks ge le M Cf mf,
 cstep p(curs(salloc nil(dcons y Tint32 dnil)),(kenil,ks))(ge,le,M)Cf mf ->
 exists b,fresh M b /\~indom le y /\
 Cf=(curs(salloc nil dnil),(kenil,ks)) /\
 mf=(ge,set le y(b,Tint32),allocb M b 0%Z(typelen Tint32)).
Proof.
 intros p y ks ge le M Cf mf Step;inversion Step;subst;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   repeat match goal with E0:(_,_)=(_,_) |- _ =>inversion E0;clear E0;subst end.
   match goal with H:alloc _ _ _ _ _ _ |- _ =>destruct H as(b&Fresh&Mem&Absent&Env);subst end.
   exists b;split;[exact Fresh| ];split;[exact Absent| ];split;reflexivity.
Qed.

Lemma V293_exit_exec_successor : forall p f body y ks ge caller M Cf mf,
 p f=Some(Tvoid,dnil,dcons y Tint32 dnil,body) ->
 cstep p(curs(sfexec f nil nil),(kenil,ks))(ge,caller,M)Cf mf ->
 Cf=(curs(salloc nil(dcons y Tint32 dnil)),(kenil,kcall f body caller ks)) /\
 mf=(ge,(emp:env),M).
Proof.
 intros p f body y ks ge caller M Cf mf Bind Step;inversion Step;subst;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   repeat match goal with E0:(_,_)=(_,_) |- _ =>inversion E0;clear E0;subst end.
   match goal with H:p f=Some _ |- _ =>rewrite Bind in H;inversion H;subst end.
   split;reflexivity.
Qed.

Lemma V293_exit_active_running_eval : forall ge le M running b,
 get le running=None ->get ge running=Some(b,Tint8) ->
 load Tint8 M(b,0%Z)=Some(V293_byteval 1) ->
 evalval(V293_OSIntEnter_running running)(ge,le,M)=Some(Vint32 Int.one).
Proof.
 intros ge le M running b NL Global Read.
 unfold V293_OSIntEnter_running;cbn[evalval evaltype get_lenv get_genv];rewrite NL,Global.
 cbn -[load];rewrite Read;reflexivity.
Qed.

Section ActiveCall.
Variables br bg bp bt bc bh bo bk bn bl bu : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable oldtarget : val.
Variable c : int32.
Definition V293_exit_active_frame :=
 V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (V293_read_bytes bt 0%Z V293_ready_table **V293_storage rest))).
Definition V293_exit_active_resource n hv :=
 V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 V293_exit_guard_resource bn bl n
 (V293_helper_resource br bg bp bt bh t V293_exit_active_frame hv).
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.

Lemma V293_exit_active_frame_good : GoodInvAsrt V293_exit_active_frame.
Proof.
 unfold V293_exit_active_frame,V293_owned_record_cell.
 split;[cbn;auto| ];split;[cbn;auto| ];split;[cbn;auto| ];
 split;[apply V293_helper_read_good|apply V293_storage_good].
Qed.

Lemma V293_exit_active_current : forall n hv,
 V293_exit_active_resource n hv ==>CurTid t **Atrue.
Proof.
 intros n hv s Held.
 apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Held.
 - sep auto.
 - intros st H;exact Logic.I.
 - intros st H;unfold V293_exit_guard_resource in H.
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in H.
   + sep auto.
   + intros st' H';exact Logic.I.
   + intros st' H';apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in H'.
     * sep auto.
     * intros st0 H0;exact Logic.I.
     * apply V293_helper_resource_current.
Qed.

Lemma V293_exit_active_lenv : forall n hv ge le M ir aux O op le',
 (ge,le,M,ir,aux,O,op)|=V293_exit_active_resource n hv ->
 (ge,le',M,ir,aux,O,op)|=V293_exit_active_resource n hv.
Proof.
 intros n hv ge le M ir aux O op le' Held.
 set(Tail:=V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
 (V293_read_bytes bt 0%Z V293_ready_table **V293_exit_active_frame))))).
 assert(Pack:(ge,le,M,ir,aux,O,op)|=SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **Tail).
 { unfold Tail,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource in *;sep auto. }
 assert(Good:GoodInvAsrt Tail).
 { unfold Tail,V293_owned_record_cell;split;[cbn;auto| ];split;[cbn;auto| ];
   split;[cbn;auto| ];split;[cbn;auto| ];
   split;[apply V293_helper_read_good|apply V293_exit_active_frame_good]. }
 pose proof(V293_ready_lenv_frame br bg bp t Tail ge le M ir aux O op le' Good Pack)as Move.
 unfold Tail,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource in *;clear Held Pack;sep auto.
Qed.

Lemma V293_exit_active_saved_pack : forall n hv bs,
 V293_owned_record_cell((bs,0%Z),Tint32,Vint32 Int.zero) **V293_exit_active_resource n hv ==>
 V293_exit_guard_resource bn bl n
 (V293_helper_resource br bg bp bt bh t
 (V293_exit_helper_frame bt bc bo bk bs (((bu,0%Z),Tint8)::rest)
 nc(Vint32 Int.zero)oldtarget c)hv).
Proof.
 intros n hv bs s Held.
 unfold V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame in Held.
 assert(Run:s|=V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bs,0%Z),Tint32,Vint32 Int.zero) **
 (V293_exit_guard_resource bn bl n(V293_helper_resource br bg bp bt bh t V293_exit_active_frame hv)))).
 { unfold V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame;sep auto. }
 apply astar_mono with(P':=V293_storage (((bu,0%Z),Tint8)::nil))
 (Q':=V293_owned_record_cell((bs,0%Z),Tint32,Vint32 Int.zero) **
 V293_exit_guard_resource bn bl n(V293_helper_resource br bg bp bt bh t V293_exit_active_frame hv))in Run.
 - unfold V293_exit_guard_resource,V293_helper_resource,V293_exit_helper_frame,V293_exit_active_frame,V293_owned_record_cell in *.
   cbn[V293_storage]in *;clear Held;sep auto.
 - intros st Own;cbn[V293_storage];apply astar_r_aemp_intro;
   eapply V293_exit_cell_to_storage;exact Own.
 - intros st H;exact H.
Qed.

Lemma V293_exit_active_body_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved bs
 helper unmap group rows y oldhigh tasks running nesting lock n,
 getsched(pc,A)=V293_scheduler ->
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
 V293_current_task tasks t nc ->~V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true Vundef **V293_exit_active_resource n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target))caller tail))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved bs
 helper unmap group rows y oldhigh tasks running nesting lock n Sched Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current NotHighest Bound SU SN SL UG NG LG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)).
 set(k:=kcall f body caller tail).
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont k ->intcont ks=intcont k ->
 InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Held;
   [sep auto|intros st H;exact Logic.I|apply V293_exit_active_current]. }
 destruct(V293_tick_raw_slot_update(bs,0%Z)Tint32 Vundef(Vint32 Int.zero)
 (V293_exit_active_resource n oldhigh) _ _ _ _ _ _ _ eq_refl Held)as(M'&Store&Updated).
 assert(After:satp(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Updated;
   [sep auto|intros st H;exact Logic.I|apply V293_exit_active_current]. }
 assert(Absent:forall x,saved<>x ->get(V293_cpu_lenv saved bs)x=None).
 { intros x Ne;unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get. }
 assert(Running:load Tint8 M'(bu,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(assertion.getmem(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci),O,op))(bu,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_r;[ |exact Updated];intros st H.
   unfold V293_exit_active_resource in H;eapply V293_record_star_load_l;[ |exact H];
   apply V293_owned_record_cell_load. }
 assert(Eval:evalval(V293_OSIntEnter_running running)(ge,V293_cpu_lenv saved bs,M')=Some(Vint32 Int.one)).
 { eapply V293_exit_active_running_eval;[apply Absent;exact SU|exact UG|exact Running]. }
 unfold V293_exit_boundary_body;fold body k.
 eapply V293_changed_pure_TaskSim with(ks:=k);
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_exit_saved_assignment_TaskSim with(b:=bs)(M':=M');
   [apply Context;reflexivity| | |reflexivity|reflexivity|exact Store|exact Before|exact After| ].
   + cbn[evaltype get_lenv];unfold V293_cpu_lenv;rewrite map_get_set;reflexivity.
   + cbn[evaladdr get_lenv];unfold V293_cpu_lenv;rewrite map_get_set;reflexivity.
   + eapply V293_changed_pure_TaskSim with(ks:=k);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_changed_pure_TaskSim with(ks:=k);
       [exact Inside|reflexivity|reflexivity| | |exact After| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.one)(take:=true);
          [apply Context;reflexivity|exact After|exact Eval|reflexivity| ].
          unfold G,Cells,k,body.
          eapply V293_exit_guard_helper_TaskSim with(nc:=nc)(bc:=bc)(bo:=bo)
          (saved_value:=Vint32 Int.zero)(oldtarget:=oldtarget)(c:=c)(oldhigh:=oldhigh)
          (tasks:=tasks)(unmap:=unmap)(group:=group)(rows:=rows)(y:=y);
          try eassumption;try(apply Absent;assumption).
          eapply V293_exit_active_saved_pack;exact Updated.
Qed.

Theorem V293_exit_active_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n,
 getsched(pc,A)=V293_scheduler ->
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
 V293_current_task tasks t nc ->~V293_highest_ready tasks t ->
 n<=1 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_exit_active_resource n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(sfexec f nil nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper unmap group rows y oldhigh tasks running nesting lock n Sched Bind Cases Helper YU YG YR YH GU GG GR GH
 ST SO SH SC SK TG CG KG OG Map Current NotHighest Bound SU SN SL UG NG LG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)).
 set(k:=kcall f body caller tail).
 set(ph:=(pc,A):hprog).
 set(Ch:=(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail)):code).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil)).
 set(Res:=V293_exit_active_resource n oldhigh).
 assert(Body:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true Vundef **Res ->
  TaskSim(pc,(po,pi,ip))(curs body,(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh Own;unfold body,k,ph,Ch,Post,Res in *.
   eapply V293_exit_active_body_TaskSim with(op:=op)(oldhigh:=oldhigh)(tasks:=tasks)
   (unmap:=unmap)(group:=group)(rows:=rows)(y:=y);eassumption. }
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons saved Tint32 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(CurrentRes:forall s,s|=Res ->s|=CurTid t **Atrue).
 { unfold Res;apply V293_exit_active_current. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply CurrentRes.
   eapply V293_exit_active_lenv;exact Held. }
 assert(Allocated:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint32 true Vundef **Res).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply V293_exit_active_lenv;exact Held. }
 assert(AllocatedLocal:forall b,fresh M b ->
  satp(ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))O
   (CurLINV V293_shared_li t)).
 { intros b Fresh;eapply V293_pending_local with(op:=op).
   pose proof(Allocated b Fresh)as Own.
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint32 true Vundef)(Q':=CurTid t **Atrue)in Own;
    [sep auto|intros st H;exact H|exact CurrentRes]. }
 assert(AllocatedEnd:forall b,fresh M b ->
  TaskSim(pc,(po,pi,ip))(curs(salloc nil dnil),(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh;eapply V293_invariant_cstep_TaskSim;
    [ | | |apply AllocatedLocal;exact Fresh|apply Body;[exact Fresh|apply Allocated;exact Fresh]].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs(salloc nil dnil),(kenil,k))
      (ge,V293_cpu_lenv saved b,Mall)(curs body,(kenil,k))(ge,V293_cpu_lenv saved b,Mall)).
     { unfold k;eapply stmt_step;[reflexivity|apply sallocend_step]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 assert(Allocate:TaskSim(pc,(po,pi,ip))(curs(salloc nil(dcons saved Tint32 dnil)),(kenil,k))
  (ge,(emp:env),M,ir,(false,nil,ci))ph Ch O V293_shared_li G Post t).
 { eapply V293_branching_cstep_TaskSim.
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(memory_has_fresh_block Mall)as[b Fresh].
     exists(curs(salloc nil dnil),(kenil,k));
     exists(ge,V293_cpu_lenv saved b,allocb Mall b 0%Z(typelen Tint32)).
     eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists b;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate E.
   - intros Cf mf Step;destruct(V293_exit_saved_successor _ _ _ _ _ _ _ _ Step)
      as(b&Fresh&Absent&EC&EM);subst Cf mf.
     do 2 eexists;split;[reflexivity| ];split;
      [apply AllocatedLocal;exact Fresh|apply AllocatedEnd;exact Fresh]. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Allocate].
 - exists(curs(sfexec f nil nil));exists kenil;exists tail;split;[reflexivity| ];left.
   exists f;exists(@nil val);exists(Tvoid,dnil,dcons saved Tint32 dnil,body);exists(@nil type).
   split;[reflexivity|exact Program].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
   + eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil);
     [reflexivity|reflexivity|exact Program|exact Logic.I|reflexivity].
   + intros;eapply V293_exit_exec_successor;[exact Program|eassumption].
Qed.
End ActiveCall.
