(* Quiet branch of the unchanged source-boundary body, with the original storage postcondition. *)
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
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_quiet_running_eval : forall ge le M running b,
 get le running=None ->get ge running=Some(b,Tint8) ->
 load Tint8 M(b,0%Z)=Some(V293_byteval 0) ->
 evalval(V293_OSIntEnter_running running)(ge,le,M)=Some(Vint32 Int.zero).
Proof.
 intros ge le M running b NL Global Read.
 unfold V293_OSIntEnter_running;cbn[evalval evaltype get_lenv get_genv];rewrite NL,Global.
 cbn -[load];rewrite Read;reflexivity.
Qed.

Section QuietCall.
Variables br bg bp bu : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable t : tid.
Let Base:=V293_ready_storage_core br bg bp target tp cells.
Let Core:=V293_ready_storage_core br bg bp target tp (((bu,0%Z),Tint8)::cells).
Let G:=V293_ready_storage_inv br bg bp target tp (((bu,0%Z),Tint8)::cells).
Definition V293_exit_quiet_resource :=
 V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 0) **(Base **CurTid t).
Let Res:=V293_exit_quiet_resource.

Lemma V293_quiet_resource_good : GoodInvAsrt Res.
Proof.
 unfold Res,V293_exit_quiet_resource;split.
 - unfold V293_owned_record_cell;cbn;auto.
 - split;[apply V293_ready_storage_core_good| ].
   unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact Logic.I.
Qed.
Lemma V293_quiet_resource_current : Res ==>CurTid t **Atrue.
Proof. intros st H;unfold Res,V293_exit_quiet_resource in H;sep auto. Qed.
Lemma V293_quiet_resource_lenv : forall ge le M ir aux O op le',
 (ge,le,M,ir,aux,O,op)|=Res ->(ge,le',M,ir,aux,O,op)|=Res.
Proof. intros ge le M ir [[ie si]ci] O op le' Held;eapply good_inv_prop;[apply V293_quiet_resource_good|exact Held]. Qed.
Lemma V293_quiet_reclose : Res ==>Core **CurTid t.
Proof.
 intros st Held;unfold Res,V293_exit_quiet_resource in Held.
 eapply astar_mono in Held;[ |apply V293_exit_cell_to_storage|intros st0 H;exact H].
 unfold Core,Base,V293_ready_storage_core,V293_ready_storage_extra;cbn[V293_storage].
 unfold Base,V293_ready_storage_core,V293_ready_storage_extra in Held;sep auto.
Qed.

Lemma V293_quiet_body_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved bs helper running nesting lock handoff,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 saved<>running ->get ge running=Some(bu,Tint8) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true Vundef **Res ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter helper handoff),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter helper handoff)caller tail))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved bs
 helper running nesting lock handoff Bind Cases Clear Different Global Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper handoff).
 set(k:=kcall f body caller tail).
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont k ->intcont ks=intcont k ->
 InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Held;
   [sep auto|intros st H;exact Logic.I|apply V293_quiet_resource_current]. }
 destruct(V293_tick_raw_slot_update(bs,0%Z)Tint32 Vundef(Vint32 Int.zero)
 Res _ _ _ _ _ _ _ eq_refl Held)as(M'&Store&Updated).
 assert(After:satp(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in Updated;
   [sep auto|intros st H;exact Logic.I|apply V293_quiet_resource_current]. }
 assert(Running:load Tint8 M'(bu,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(assertion.getmem(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci),O,op))(bu,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_r;[ |exact Updated];intros st H.
   unfold Res,V293_exit_quiet_resource in H;eapply V293_record_star_load_l;
   [apply V293_owned_record_cell_load|exact H]. }
 assert(Eval:evalval(V293_OSIntEnter_running running)(ge,V293_cpu_lenv saved bs,M')=Some(Vint32 Int.zero)).
 { eapply V293_quiet_running_eval;[ |exact Global|exact Running].
   unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get. }
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
       -- eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.zero)(take:=false);
          [apply Context;reflexivity|exact After|exact Eval|reflexivity| ].
          assert(Final:(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,ci),O,op)|=
           Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **(Core **CurTid t)).
          { unfold V293_owned_record_cell in Updated;sep normal in Updated;sep destruct Updated.
            eapply astar_mono;[intros st H;exact H|apply V293_quiet_reclose| ].
            clear -Updated;sep auto. }
          eapply V293_invariant_return_suffix with(R:=Core **CurTid t)(op:=op);
           [exact Bind|exact Cases|exact Clear| | | |exact Final].
          ++ split;[apply V293_ready_storage_core_good| ].
             unfold CurTid,Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact Logic.I.
          ++ intros st H;sep auto.
          ++ intros g e m r cs o a Empty H;right;unfold SWINVt;fold(CurTid t).
             apply sat_split in H;destruct H as(mc&mt&oc&ot&JM&JO&HC&HT).
             apply sat_split';exists mc;exists mt;exists oc;exists ot.
             split;[exact JM| ];split;[exact JO| ];split;
             [apply V293_storage_return_disabled_SWINV;assumption|exact HT].
Qed.

Lemma V293_quiet_entry_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved helper running nesting lock handoff,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 saved<>running ->get ge running=Some(bu,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res ->
 TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))(pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper running nesting lock handoff Bind Cases Clear SU UG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper handoff).
 set(k:=kcall f body caller tail).
 set(ph:=(pc,A):hprog).
 set(Ch:=(SKIP,(kenil,tail)):code).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil)).
 set(EntryRes:=Res).
 assert(Body:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true Vundef **EntryRes ->
  TaskSim(pc,(po,pi,ip))(curs body,(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh Own;unfold body,k,ph,Ch,Post,EntryRes in *.
   eapply V293_quiet_body_TaskSim with(op:=op);eassumption. }
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons saved Tint32 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(CurrentRes:forall s,s|=EntryRes ->s|=CurTid t **Atrue).
 { unfold EntryRes;apply V293_quiet_resource_current. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply CurrentRes.
   eapply V293_quiet_resource_lenv;exact Held. }
 assert(Allocated:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint32 true Vundef **EntryRes).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply V293_quiet_resource_lenv;exact Held. }
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

Theorem V293_exit_quiet_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved helper running nesting lock handoff,
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper handoff) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->(forall i,ir i=false) ->
 saved<>running ->get ge running=Some(bu,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper running nesting lock handoff APIBind Bind Cases Clear SU UG Held.
 eapply V293_nested_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact APIBind.
 - eapply V293_pending_local with(op:=op);apply V293_quiet_resource_current;exact Held.
 - eapply V293_quiet_entry_TaskSim with(op:=op);eassumption.
Qed.
End QuietCall.
