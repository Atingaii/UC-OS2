(* The changed branch before the accepted source-level handoff boundary. *)
Require Import CertiOS.certiucos.v293.proofs.V293HandoffTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_changed_estep_frame : forall c ke ge le M c' ke' Mframe Mall,
 estep c ke(ge,le,M)c' ke'(ge,le,M) ->join M Mframe Mall ->
 estep c ke(ge,le,Mall)c' ke'(ge,le,Mall).
Proof.
 intros c ke ge le M c' ke' Mframe Mall Step Join.
 inversion Step;subst;try solve[econstructor;eauto;
 try rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);
 try erewrite lmachLib.evalval_mono;eauto].
 inversion H;subst; eapply evderef_step;[reflexivity| ].
 rewrite(lmachLib.load_mono _ _ _ _ _ _ Join H0);exact H0.
Qed.

Lemma V293_changed_pure_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 C C' ge le M ir ci,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 callcont(snd(snd C))=callcont ks ->intcont(snd(snd C))=intcont ks ->~IsEnd C ->
 (forall Mf Mall,join M Mf Mall ->cstep(pumerge po pi)C(ge,le,Mall)C'(ge,le,Mall)) ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))C'(ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))C(ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks[c[ke k]] C' ge le M ir ci
 Inside Call Int End Frames Local Tail.
 eapply V293_invariant_cstep_TaskSim;[ |exact End| |exact Local|exact Tail].
 - eapply V293_context_inos;[exact Inside|exact Call|exact Int].
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   pose proof(Frames Mf Mall Join)as Step;split;[exact Step| ].
   intros Cf mf Other;destruct(cstep_idmove_deter _ _ _ _ _ _ Step Other)as[EC EM];split;symmetry;assumption.
Qed.

Lemma V293_changed_expr_TaskSim : forall c ke m c' ke' m',
 estepstar c ke m c' ke' m' ->
 forall pc po pi ip ph Ch O li I Post t ks ge le M ir ci,
 m=(ge,le,M) ->InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(c',(ke',ks))(ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(c,(ke,ks))(ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros c ke m c' ke' m' Steps;induction Steps as
 [c ke m|c ke m c1 ke1 m1 c2 ke2 m2 Step Rest IH];
 intros pc po pi ip ph Ch O li I Post t ks ge le M ir ci Eq Inside Local Tail.
 - exact Tail.
 - pose proof(cstepLib.estep_mem_same _ _ _ _ _ _ Step)as Same;subst m1;subst m.
   eapply V293_changed_pure_TaskSim with(ks:=ks)(C':=(c1,(ke1,ks)));
   [exact Inside|reflexivity|reflexivity| | |exact Local| ].
   + intros[x E];inversion E;subst.
     inversion Step.
   + intros Mf Mall Join;eapply expr_step;[reflexivity| ].
     eapply V293_changed_estep_frame;[exact Step|exact Join].
   + eapply IH;try eassumption;reflexivity.
Qed.

Lemma V293_changed_if_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M ir ci e yes no v take,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 evalval e(ge,le,M)=Some v ->istrue v=Some take ->
 TaskSim(pc,(po,pi,ip))(curs(if take then yes else no),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sif e yes no),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M ir ci e yes no v take
 Context Local Eval Truth Tail.
 eapply V293_changed_pure_TaskSim with(ks:=ks)(C':=(cure e,(kenil,kif yes no ks)));
 [exact Context|reflexivity|reflexivity| | |exact Local| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sif_step].
 - eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil);[ |reflexivity| |exact Local| ].
   + apply cstepLib.evalval_imply_estepstar;exact Eval.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks);
     [exact Context|reflexivity|reflexivity| | |exact Local|exact Tail].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity| ];destruct take;
       [apply svift_step|apply sviff_step];exact Truth.
Qed.

Lemma V293_changed_increment_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M M' ir ci counter b c,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 get le counter=None ->get ge counter=Some(b,Tint32) ->
 load Tint32 M(b,0%Z)=Some(Vint32 c) ->
 store Tint32 M(b,0%Z)(Vint32(Int.add c Int.one))=Some M' ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 satp(ge,le,M',ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,M',ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(V293_OSSched_increment counter),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M M' ir ci counter b c
 Context NotLocal Global Read Store Before After Tail.
 destruct(V293_ready_counter_eval ge le M counter b c NotLocal Global Read)as(TL&TR&Addr&Value).
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(cure(ebinop oplus(evar counter)(econst32 Int.one)),(kenil,kassignr(evar counter)Tint32 ks)));
 [exact Context|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;eapply stmt_step;[reflexivity| ];eapply sassign_step.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TL.
   + rewrite(lmachLib.evaltype_mono _ _ _ _ _ _ Join);exact TR.
   + apply eq_int;auto.
 - eapply V293_changed_expr_TaskSim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some(Vint32(Int.add c Int.one)))))(ke':=kenil);
   [ |reflexivity| |exact Before| ].
   + apply cstepLib.evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks)
     (C':=(cure(eaddrof(evar counter)),(kenil,kassignl(Vint32(Int.add c Int.one))Tint32 ks)));
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

(* Internal continuation bridge. The public entry constructs its write below. *)
Lemma V293_changed_tail_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M M' ir ci high current counter handoff b c,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evalval(V293_OSSched_different high current)(ge,le,M)=Some(Vint32 Int.one) ->
 get le counter=None ->get ge counter=Some(b,Tint32) ->
 load Tint32 M(b,0%Z)=Some(Vint32 c) ->
 store Tint32 M(b,0%Z)(Vint32(Int.add c Int.one))=Some M' ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 satp(ge,le,M',ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(curs handoff,(kenil,ks))(ge,le,M',ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M M' ir ci high current counter handoff b c
 Context Guard NotLocal Global Read Store Before After Tail.
 eapply V293_changed_if_TaskSim with(v:=Vint32 Int.one)(take:=true);
 [exact Context|exact Before|exact Guard|reflexivity| ].
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(curs(V293_OSSched_increment counter),(kenil,kseq(sseq(sskip None)handoff)ks)));
 [exact Context|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_changed_increment_TaskSim;[ |exact NotLocal|exact Global|exact Read|exact Store|exact Before|exact After| ].
   + eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   + eapply V293_changed_pure_TaskSim with(ks:=ks)
     (C':=(curs(sseq(sskip None)handoff),(kenil,ks)));
     [exact Context|reflexivity|reflexivity| | |exact After| ].
     * intros[x E];discriminate E.
     * intros;eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_changed_pure_TaskSim with(ks:=ks)(C':=(SKIP,(kenil,kseq handoff ks)));
       [exact Context|reflexivity|reflexivity| | |exact After| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_changed_pure_TaskSim with(ks:=ks);
          [exact Context|reflexivity|reflexivity| | |exact After|exact Tail].
          ++ intros[x E];discriminate E.
          ++ intros;eapply stmt_step;[reflexivity|apply sskip_step].
Qed.

Section OwnedChanged.
Variables br bg bp bc bh bo bk saved_block : block.
Variable rest : list(addr*type).
Variable target : var.
Variables next t : tid.
Variables nh nc : nat.
Variable saved_value : val.
Let Cells := ((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::rest.
Let G := V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Let Owned (c:int32) := Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **V293_storage rest))))).

Lemma V293_changed_owned_local : forall ge le M ir aux O op c,
 (ge,le,M,ir,aux,O,op)|=Owned c ->satp(ge,le,M,ir,aux)O(CurLINV V293_shared_li t).
Proof.
 intros ge le M ir aux O op c Held;eapply V293_pending_local with(op:=op).
 unfold Owned,SWINVt in Held;fold(CurTid t)in Held;sep auto.
Qed.

(* Resource-only entry, including unrestricted modular 32-bit counting. *)
Theorem V293_exit_changed_TaskSim : forall pc po pi ip A ge M ir top ci O op
 high current counter f body caller tail tau d1 d2 saved c tasks,
 getsched(pc,A)=V293_scheduler ->
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 nh<256 ->nc<256 ->nh<>nc ->
 get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get(V293_cpu_lenv saved saved_block)counter=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bk,Tint32) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->indom tasks t ->V293_highest_ready tasks next ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=Owned c ->
 TaskSim(pc,(po,pi,ip))
 (curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)
 (sseq(sskip None)(V293_interrupt_handoff high current target)))(sskip None)),
 (kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op high current counter f body caller tail tau d1 d2 saved c tasks
 Sched Bind Cases Nh Nc Different HN CN KN HG CG KG Target Map Member Highest Held.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nh)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold Owned in Held;sep auto. }
 assert(Cache:load Tint8 M(bc,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold Owned in Held;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval _ _ _ _ _ _ _ _ _ Nh Nc HN CN HG CG High Cache)as(Guard&GuardType).
 assert(E:Nat.eqb nh nc=false)by(apply Nat.eqb_neq;exact Different);rewrite E in Guard.
 assert(Count:load Tint32 M(bk,0%Z)=Some(Vint32 c)).
 { eapply V293_record_star_load_l with(s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold Owned in Held;sep auto. }
 assert(ToWrite:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **V293_storage rest))))))
 by(unfold Owned in Held;sep auto).
 destruct(V293_owned_record_cell_update (bk,0%Z) Tint32 (Vint32 c) (Vint32(Int.add c Int.one)) _ _ _ _ _ _ _ _
 ltac:(reflexivity)ToWrite)as(M'&Store&Written).
 assert(AfterOwned:(ge,V293_cpu_lenv saved saved_block,M',ir,(false,nil,top::ci),O,op)|=Owned(Int.add c Int.one))
 by(unfold Owned;clear Held;sep auto).
 eapply V293_changed_tail_TaskSim;[ |exact Guard|exact KN|exact KG|exact Count|exact Store| | | ].
 - eapply V293_context_inos with(ks:=kcall f body caller tail);
   [eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity].
 - eapply V293_changed_owned_local;exact Held.
 - eapply V293_changed_owned_local;exact AfterOwned.
 - unfold G,Cells;eapply V293_handoff_TaskSim with(old:=V293_byteval nc)(nh:=nh)
   (rest:=((bk,0%Z),Tint32)::rest)(next:=next)(bo:=bo)(saved_value:=saved_value);
   try eassumption.
   assert(CounterStorage:V293_owned_record_cell((bk,0%Z),Tint32,Vint32(Int.add c Int.one)) **V293_storage rest ==>
   V293_storage(((bk,0%Z),Tint32)::rest)).
   { cbn[V293_storage];apply astar_mono;[apply V293_exit_cell_to_storage|intros st H;exact H]. }
   unfold Owned in AfterOwned.
   eapply astar_mono in AfterOwned;[ |intros st H;exact H| ].
   2:{ do 4 (apply astar_mono;[intros st H;exact H| ]);exact CounterStorage. }
   exact AfterOwned.
Qed.
End OwnedChanged.
