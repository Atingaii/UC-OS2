Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitClientCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Import ListNotations.
Local Open Scope nat_scope.

(* Nonzero scheduler lock blocks dispatch for every nesting byte. *)
Definition V293_locked_guard_resource bn bl n l R :=
 V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval l) **R).

Lemma V293_locked_guards_local : forall bn bl n l R t ge le M ir ci O op,
 (R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_locked_guard_resource bn bl n l R ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t).
Proof.
 intros bn bl n l R t ge le M ir ci O op Current Held.
 eapply V293_pending_local with(op:=op).
 unfold V293_locked_guard_resource in Held.
 eapply astar_mono in Held;[ |intros s H;exact H|apply astar_mono;
  [intros s H;exact H|exact Current]].
 sep auto.
Qed.

Lemma V293_locked_prefix_TaskSim : forall pc po pi ip ph Ch O I Post t ks
 ge le M ir ci op nesting lock bn bl n l R dispatch,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 n<256 ->0<l ->l<256 ->get le nesting=None ->get le lock=None ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_locked_guard_resource bn bl n l R ->
 (forall M',(ge,le,M',ir,(false,nil,ci),O,op)|=V293_locked_guard_resource bn bl(Nat.pred n)l R ->
  TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge le M ir ci op nesting lock bn bl n l R dispatch
 Inside Bound LPos LBound NN LN NG LG Current Held Continue.
 assert(Before:satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_locked_guards_local;[exact Current|exact Held]. }
 assert(Guards:forall M' n',n'<256 ->
  (ge,le,M',ir,(false,nil,ci),O,op)|=V293_locked_guard_resource bn bl n' l R ->
  TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t ->
  TaskSim(pc,(po,pi,ip))(curs(V293_OSIntExit_guards nesting lock dispatch),(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { intros M' n' NB H Tail.
   assert(Local:satp(ge,le,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
   { eapply V293_locked_guards_local;[exact Current|exact H]. }
   assert(NRead:load Tint8 M'(bn,0%Z)=Some(V293_byteval n')).
   { change(load Tint8(assertion.getmem(ge,le,M',ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval n')).
     unfold V293_locked_guard_resource in H;eapply V293_record_star_load_l;[ |exact H];apply V293_owned_record_cell_load. }
   unfold V293_OSIntExit_guards.
   destruct n' as [ | n' ].
   - assert(LRead:load Tint8 M'(bl,0%Z)=Some(V293_byteval l)).
     { change(load Tint8(assertion.getmem(ge,le,M',ir,(false,nil,ci),O,op))(bl,0%Z)=Some(V293_byteval l)).
       unfold V293_locked_guard_resource in H;eapply V293_record_star_load_r;[ |exact H];intros.
       eapply V293_record_star_load_l;[ |eassumption];apply V293_owned_record_cell_load. }
     eapply V293_changed_if_TaskSim with(v:=Vint32 Int.one)(take:=true);
     [exact Inside|exact Local|eapply V293_exit_zero_eval;eassumption|reflexivity| ].
     eapply V293_changed_if_TaskSim with(v:=Vint32 Int.zero)(take:=false);
     [exact Inside|exact Local|eapply V293_nested_zero_eval with(n:=l);eassumption|reflexivity|exact Tail].
   - eapply V293_changed_if_TaskSim with(v:=Vint32 Int.zero)(take:=false);
     [exact Inside|exact Local|eapply V293_nested_zero_eval with(n:=S n');try eassumption;lia|reflexivity|exact Tail]. }
 unfold V293_OSIntExit_nesting_dispatch.
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(curs(V293_OSIntExit_decrement nesting),(kenil,kseq(V293_OSIntExit_guards nesting lock dispatch)ks)));
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - assert(NextInside:InOS(SKIP,(kenil,kseq(V293_OSIntExit_guards nesting lock dispatch)ks))(pumerge po pi)).
   { eapply V293_context_inos;[exact Inside|reflexivity|reflexivity]. }
   assert(NRead:load Tint8 M(bn,0%Z)=Some(V293_byteval n)).
   { change(load Tint8(assertion.getmem(ge,le,M,ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval n)).
     unfold V293_locked_guard_resource in Held;eapply V293_record_star_load_l;[ |exact Held];apply V293_owned_record_cell_load. }
   destruct(V293_exit_decrement_eval ge le M nesting bn n Bound NN NG NRead)as[Positive Assignment].
   destruct n as [ | n ].
   + unfold V293_OSIntExit_decrement.
     eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.zero)(take:=false);
     [exact NextInside|exact Before|exact Positive|reflexivity| ].
     eapply V293_changed_pure_TaskSim with(ks:=ks);
     [exact Inside|reflexivity|reflexivity| | |exact Before| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply Guards with(n':=0);[lia|exact Held|apply Continue;exact Held].
   + destruct(V293_owned_record_cell_update _ _ _ (V293_byteval n) _ _ _ _ _ _ _ _
      (V293_byte_type n ltac:(lia)) Held)as(M'&Store&Updated).
     assert(After:satp(ge,le,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
     { eapply V293_locked_guards_local;[exact Current|exact Updated]. }
     unfold V293_OSIntExit_decrement.
     eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.one)(take:=true);
     [exact NextInside|exact Before|exact Positive|reflexivity| ].
     destruct(Assignment ltac:(lia))as(TL&Addr&TR&Value).
     eapply V293_helper_assignment_TaskSim;
     [exact NextInside|exact TL|exact Addr|exact TR|exact Value|exact Store|exact Before|exact After| ].
     eapply V293_changed_pure_TaskSim with(ks:=ks);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply Guards with(n':=n);[lia|exact Updated|apply Continue;exact Updated].
Qed.

Section LockedCall.
Variables br bg bp bn bl bu:block.
Variable target:var.
Variable tp:type.
Variable cells:list(addr*type).
Variable t:tid.
Let Base:=V293_ready_storage_core br bg bp target tp cells.
Let Cells:=((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::cells.
Let Core:=V293_ready_storage_core br bg bp target tp Cells.
Let G:=V293_ready_storage_inv br bg bp target tp Cells.
Definition V293_exit_locked_resource n l :=
 V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (V293_locked_guard_resource bn bl n l (Base **CurTid t)).
Let Res:=V293_exit_locked_resource.

Lemma V293_locked_resource_good : forall n l,GoodInvAsrt(Res n l).
Proof.
 intros;unfold Res,V293_exit_locked_resource,V293_locked_guard_resource.
 split;[unfold V293_owned_record_cell;cbn;auto| ].
 split;[unfold V293_owned_record_cell;cbn;auto| ].
 split;[unfold V293_owned_record_cell;cbn;auto| ].
 split;[apply V293_ready_storage_core_good| ].
 unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact Logic.I.
Qed.
Lemma V293_locked_resource_current : forall n l,Res n l ==>CurTid t **Atrue.
Proof. intros n l st H;unfold Res,V293_exit_locked_resource,V293_locked_guard_resource in H;sep auto. Qed.
Lemma V293_locked_resource_lenv : forall n l ge le M ir aux O op le',
 (ge,le,M,ir,aux,O,op)|=Res n l ->(ge,le',M,ir,aux,O,op)|=Res n l.
Proof. intros n l ge le M ir [[ie si]ci] O op le' Held;eapply good_inv_prop;[apply V293_locked_resource_good|exact Held]. Qed.
Lemma V293_locked_reclose : forall n l,Res n l ==>Core **CurTid t.
Proof.
 intros n l st Held;unfold Res,V293_exit_locked_resource,V293_locked_guard_resource in Held.
 eapply astar_mono in Held;[ |apply V293_exit_cell_to_storage|apply astar_mono;
 [apply V293_exit_cell_to_storage|apply astar_mono;[apply V293_exit_cell_to_storage|intros s H;exact H]]].
 unfold Core,Cells,Base,V293_ready_storage_core,V293_ready_storage_extra;cbn[V293_storage].
 unfold Base,V293_ready_storage_core,V293_ready_storage_extra in Held;sep auto.
Qed.


Lemma V293_locked_critical_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f body caller tail tau d1 d2 saved bs
 helper nesting lock handoff n l,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->n<256 ->0<l ->l<256 ->saved<>nesting ->saved<>lock ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Res n l ->
 TaskSim(pc,(po,pi,ip))
 (curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter helper handoff))(sprim excrit))),
 (kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f body caller tail tau d1 d2 saved bs
 helper nesting lock handoff n l Bind Cases Clear Bound LPos LBound SN SL NG LG Held.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont(kcall f body caller tail) ->
 intcont ks=intcont(kcall f body caller tail) ->InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 set(R:=V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **(Base **CurTid t))).
 assert(ResourceCurrent:R ==>CurTid t **Atrue).
 { unfold R;intros st H;sep auto. }
 assert(Pack:(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=V293_locked_guard_resource bn bl n l R).
 { unfold R,Res,V293_exit_locked_resource,V293_locked_guard_resource in *;sep auto. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_locked_guards_local;[exact ResourceCurrent|exact Pack]. }
 assert(Entered:(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,false::ci),O,op)|=
 V293_locked_guard_resource bn bl n l R).
 { eapply good_inv_prop;[ |exact Pack].
   unfold V293_locked_guard_resource,R.
   split;[unfold V293_owned_record_cell;cbn;auto| ].
   split;[unfold V293_owned_record_cell;cbn;auto| ].
   split;[unfold V293_owned_record_cell;cbn;auto| ].
   split;[cbn;auto| ].
   split;[apply V293_ready_storage_core_good| ].
   unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact Logic.I. }
 assert(After:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,false::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_locked_guards_local;[exact ResourceCurrent|exact Entered]. }
 eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_invariant_encrit_TaskSim.
   + reflexivity.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + exact After.
   + eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
     [exact Inside|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_changed_pure_TaskSim with(ks:=kcall f body caller tail);
       [exact Inside|reflexivity|reflexivity| | |exact After| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_locked_prefix_TaskSim with(op:=op)(n:=n)(l:=l)(bn:=bn)(bl:=bl)(R:=R).
          ++ apply Context;reflexivity.
          ++ exact Bound.
          ++ exact LPos.
          ++ exact LBound.
          ++ unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get.
          ++ unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get.
          ++ exact NG.
          ++ exact LG.
          ++ exact ResourceCurrent.
          ++ exact Entered.
          ++ intros M' Ready.
             assert(Saved:(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,false::ci),O,op)|=
             Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Res(Nat.pred n)l).
             { unfold R,Res,V293_exit_locked_resource,V293_locked_guard_resource in *;sep auto. }
             eapply astar_mono in Saved;[ |intros st H;exact H|apply V293_locked_reclose].
             unfold G,Core in *.
             eapply V293_storage_pending_TaskSim;[exact Bind|exact Cases|exact Clear|exact Saved].
Qed.
Lemma V293_locked_body_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved bs
 helper running nesting lock handoff n l,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 (forall i,ir i=false) ->n<256 ->0<l ->l<256 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 get ge lock=Some(bl,Tint8) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true Vundef **Res n l ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 handoff),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 handoff)caller tail))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved bs
 helper running nesting lock handoff n l Bind Cases Clear Bound LPos LBound SU SN SL UG NG LG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 handoff).
 set(k:=kcall f body caller tail).
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont k ->intcont ks=intcont k ->
 InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Held;
   [sep auto|intros st H;exact Logic.I|apply V293_locked_resource_current]. }
 destruct(V293_tick_raw_slot_update(bs,0%Z)Tint32 Vundef(Vint32 Int.zero)
 (Res n l) _ _ _ _ _ _ _ eq_refl Held)as(M'&Store&Updated).
 assert(After:satp(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Updated;
   [sep auto|intros st H;exact Logic.I|apply V293_locked_resource_current]. }
 assert(Absent:forall x,saved<>x ->get(V293_cpu_lenv saved bs)x=None).
 { intros x Ne;unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get. }
 assert(Running:load Tint8 M'(bu,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(assertion.getmem(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci),O,op))(bu,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_r;[ |exact Updated];intros st H.
   unfold Res,V293_exit_locked_resource in H;eapply V293_record_star_load_l;[ |exact H];
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
          eapply V293_locked_critical_TaskSim with(n:=n)(l:=l)(op:=op);try eassumption.
          unfold V293_owned_record_cell in Updated;sep normal in Updated;sep destruct Updated;clear -Updated;sep auto.
Qed.

Lemma V293_locked_entry_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved helper running nesting lock handoff n l,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 n<256 ->0<l ->l<256 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res n l ->
 TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper running nesting lock handoff n l Bind Cases Clear Bound LPos LBound SU SN SL UG NG LG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper handoff).
 set(k:=kcall f body caller tail).
 set(ph:=(pc,A):hprog).
 set(Ch:=(SKIP,(kenil,tail)):code).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil)).
 set(EntryRes:=Res n l).
 assert(Body:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true Vundef **EntryRes ->
  TaskSim(pc,(po,pi,ip))(curs body,(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh Own;unfold body,k,ph,Ch,Post,EntryRes in *.
   eapply V293_locked_body_TaskSim with(op:=op)(n:=n)(l:=l);eassumption. }
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons saved Tint32 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(CurrentRes:forall s,s|=EntryRes ->s|=CurTid t **Atrue).
 { unfold EntryRes;apply V293_locked_resource_current. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply CurrentRes.
   eapply V293_locked_resource_lenv;exact Held. }
 assert(Allocated:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint32 true Vundef **EntryRes).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply V293_locked_resource_lenv;exact Held. }
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

Theorem V293_exit_locked_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved helper running nesting lock handoff n l,
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 n<256 ->0<l ->l<256 ->saved<>running ->saved<>nesting ->saved<>lock ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res n l ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper running nesting lock handoff n l APIBind Bind Cases Clear Bound LPos LBound SU SN SL UG NG LG Held.
 eapply V293_nested_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact APIBind.
 - eapply V293_pending_local with(op:=op);eapply V293_locked_resource_current;exact Held.
 - eapply V293_locked_entry_TaskSim with(op:=op)(n:=n)(l:=l);eassumption.
Qed.
End LockedCall.
