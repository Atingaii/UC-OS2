(* Pull the existing switch simulation through the actual byte-copy steps. *)
Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Internal continuation lemma; the public interface below constructs its store
   and switch continuation from ownership instead of asking for either. *)
Lemma V293_copy_csteps_TaskSim : forall pc po pi ip ph Ch O li I Post t
 ge le M Mc ir ie ci high current target ks bc v,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evaltype(evar current)(ge,le,M)=Some Tint8 ->
 evaltype(evar high)(ge,le,M)=Some Tint8 ->
 evalval(evar high)(ge,le,M)=Some v ->
 evalval(eaddrof(evar current))(ge,le,M)=Some(Vptr(bc,Int.zero)) ->
 store Tint8 M(bc,0%Z)v=Some Mc ->
 satp(ge,le,M,ir,(ie,nil,ci))O(CurLINV li t) ->
 satp(ge,le,Mc,ir,(ie,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(curs(sprim(switch target)),(kenil,ks))
 (ge,le,Mc,ir,(ie,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(V293_interrupt_handoff high current target),(kenil,ks))
 (ge,le,M,ir,(ie,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ge le M Mc ir ie ci high current target ks bc v
 Inside CT HT HR CA Store Before After Tail.
 set(K:=kseq(sprim(switch target))ks).
 assert(Pull:forall Ci Cj Mi,
 callcont(snd(snd Ci))=callcont ks ->intcont(snd(snd Ci))=intcont ks ->~IsEnd Ci ->
 (forall Mf Mall,join Mi Mf Mall ->
 cstep(pumerge po pi)Ci(ge,le,Mall)Cj(ge,le,Mall)) ->
 satp(ge,le,Mi,ir,(ie,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))Cj(ge,le,Mi,ir,(ie,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))Ci(ge,le,Mi,ir,(ie,nil,ci))ph Ch O li I Post t).
 { intros[c[ke k]] Cj Mi Call Int End Steps Local Rest.
   eapply V293_invariant_cstep_TaskSim;[ |exact End| |exact Local|exact Rest].
   - eapply V293_context_inos;[exact Inside|exact Call|exact Int].
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];
     pose proof(Steps Mf Mall Join)as Step;split;[exact Step| ].
     intros Cf mf Other;destruct(cstep_idmove_deter _ _ _ _ _ _ Step Other)as[EC EM];split;symmetry;assumption. }
 assert(SkipSim:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,K))
 (ge,le,Mc,ir,(ie,nil,ci))ph Ch O li I Post t).
 { eapply Pull;[reflexivity|reflexivity| | |exact After|exact Tail].
   - intros[x E];discriminate E.
   - intros;eapply stmt_step;[reflexivity|apply sskip_step]. }
 assert(Write:TaskSim(pc,(po,pi,ip))
 (curs(sskip(Some(Vptr(bc,Int.zero)))),(kenil,kassignl v Tint8 K))
 (ge,le,M,ir,(ie,nil,ci))ph Ch O li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |exact After|exact SkipSim].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(lmachLib.store_mono _ _ _ _ _ _ _ Join Store)as[Mall' WholeStore].
     exists Mall';split.
     + apply map_join_comm;eapply join_store_join;[apply map_join_comm;exact Join|exact Store|exact WholeStore].
     + split.
       * eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact WholeStore.
       * intros;eapply V293_store_cstep_unique;[exact WholeStore|eassumption]. }
 eapply Pull with(Cj:=(curs(sassign(evar current)(evar high)),(kenil,K)));
 [reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply Pull with(Cj:=(cure(evar high),(kenil,kassignr(evar current)Tint8 K)));
   [reflexivity|reflexivity| | |exact Before| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity| ];eapply sassign_step.
     * rewrite(lmachLib.evaltype_irrev_mem _ _ _ _ M);exact CT.
     * rewrite(lmachLib.evaltype_irrev_mem _ _ _ _ M);exact HT.
     * apply eq_int;auto.
   + eapply Pull with(Cj:=(curs(sskip(Some v)),(kenil,kassignr(evar current)Tint8 K)));
     [reflexivity|reflexivity| | |exact Before| ].
     * intros[x E];discriminate E.
     * intros Mf Mall Join;eapply expr_step;[reflexivity|apply evar_step].
       rewrite(lmachLib.evalval_mono _ _ _ _ _ _ _ Join HR);exact HR.
     * eapply Pull with(Cj:=(cure(eaddrof(evar current)),(kenil,kassignl v Tint8 K)));
       [reflexivity|reflexivity| | |exact Before| ].
       -- intros[x E];discriminate E.
       -- intros;eapply stmt_step;[reflexivity|apply sassignrv_step].
       -- eapply Pull with(Cj:=(curs(sskip(Some(Vptr(bc,Int.zero)))),(kenil,kassignl v Tint8 K)));
         [reflexivity|reflexivity| | |exact Before|exact Write].
          ++ intros[x E];discriminate E.
          ++ intros Mf Mall Join;eapply expr_step;[reflexivity|apply eaddr_step].
             rewrite(lmachLib.evalval_mono _ _ _ _ _ _ _ Join CA);exact CA.
Qed.

Section OwnedCopy.
Variables br bg bp bc bh bo saved_block : block.
Variable rest : list(addr*type).
Variable target : var.
Variables next t : tid.
Variable nh : nat.
Variable saved_value : val.
Let Cells := ((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::rest.
Let G := V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Let Owned (cache:val) := Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bc,0%Z),Tint8,cache) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **V293_storage rest)))).

Lemma V293_copy_owned_local : forall ge le M ir aux O op cache,
 (ge,le,M,ir,aux,O,op)|=Owned cache ->
 satp(ge,le,M,ir,aux)O(CurLINV V293_shared_li t).
Proof.
 intros ge le M ir aux O op cache Held.
 eapply V293_pending_local with(op:=op).
 unfold Owned,SWINVt in Held;fold(CurTid t)in Held;sep auto.
Qed.

Lemma V293_copy_switch_resources : forall ge le M ir aux O op cache tasks,
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->indom tasks t ->V293_highest_ready tasks next ->
 (ge,le,M,ir,aux,O,op)|=Owned cache ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt G t //\\ SWPRE_NDEAD V293_scheduler target t).
Proof.
 intros ge le M ir aux O op cache tasks Target Map Member Highest Held.
 unfold Owned in Held;apply sat_split in Held.
 destruct Held as(Ms&Mc&Os&Oc&JM&JO&Saved&Raw).
 destruct Saved as[Cell Empty];change(Os=(emp:osabst))in Empty;subst Os.
 apply map_join_comm in JO;apply map_join_emp' in JO;subst Oc.
 assert(Read:load(Tptr V293_tcb_type)Mc(bo,0%Z)=Some(Vptr next)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mc,ir,aux,O,op))
 (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - sep auto. }
 assert(Store:V293_owned_record_cell((bc,0%Z),Tint8,cache) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **V293_storage rest) ==>
 V293_storage Cells).
 { cbn[Cells V293_storage];apply astar_mono;[apply V293_exit_cell_to_storage| ].
   apply astar_mono;[apply V293_exit_cell_to_storage|intros st H;exact H]. }
 assert(Named:forall m o,
 (ge,le,m,ir,aux,o,op)|=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) ->
 (ge,le,m,ir,aux,o,op)|=V293_dispatch_cell target V293_tcb_type).
 { intros m o H;apply astar_l_apure_elim in H;destruct H as[_ H].
   exists(Vptr next);apply astar_l_apure_intro;[ |reflexivity].
   exists bo;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;[reflexivity|exact Target]]. }
 assert(Parts:(ge,le,Mc,ir,aux,O,op)|=
 (V293_owned_record_cell((bc,0%Z),Tint8,cache) **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **V293_storage rest)) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 SWINVt(V293_ready_inv br bg bp)t))by(sep auto).
 eapply astar_mono in Parts;[ |exact Store|intros st H;exact H].
 apply sat_split in Parts;destruct Parts as(ma&mb&oa&ob&JMa&JOa&Storage&Parts).
 apply sat_split in Parts;destruct Parts as(mt&mr&ot&orr&JMb&JOb&Dispatch&Ready).
 apply Named in Dispatch.
 assert(Packed:(ge,le,Mc,ir,aux,O,op)|=V293_storage Cells **
 (V293_dispatch_cell target V293_tcb_type **SWINVt(V293_ready_inv br bg bp)t)).
 { apply sat_split';exists ma;exists mb;exists oa;exists ob.
   split;[exact JMa| ];split;[exact JOa| ];split;[exact Storage| ].
   apply sat_split';exists mt;exists mr;exists ot;exists orr.
   split;[exact JMb| ];split;[exact JOb| ];split;assumption. }
 assert(Shared:(ge,le,Mc,ir,aux,O,op)|=SWINVt G t).
 { unfold G;apply V293_ready_storage_switch_resources.
   unfold V293_ready_storage_extra;clear Raw;sep auto. }
 apply sat_split';exists Ms;exists Mc;exists(emp:osabst);exists O.
 split;[exact JM| ];split;[apply map_join_comm;apply map_join_emp| ];split.
 - split;[exact Cell|reflexivity].
 - eapply V293_storage_switch_pre;[exact Target|exact Read|exact Map|exact Member|exact Highest|exact Shared].
Qed.

(* One public resource-only entry: no step/store or simulation hypothesis. *)
Theorem V293_handoff_TaskSim : forall pc po pi ip A ge M ir top ci O op
 high current f body caller tail tau d1 d2 saved old tasks,
 getsched(pc,A)=V293_scheduler ->
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 nh<256 ->get(V293_cpu_lenv saved saved_block)high=None ->
 get(V293_cpu_lenv saved saved_block)current=None ->
 get ge high=Some(bh,Tint8) ->get ge current=Some(bc,Tint8) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 get O abstcblsid=Some(abstcblist tasks) ->indom tasks t ->V293_highest_ready tasks next ->
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=Owned old ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_interrupt_handoff high current target),
 (kenil,kseq(sprim excrit)(kseq sret(kcall f body caller tail))))
 (ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci))
 (pc,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir top ci O op high current f body caller tail tau d1 d2 saved old tasks
 Sched Bind Cases Range HN CN HG CG Target Map Member Highest Held.
 assert(High:load Tint8 M(bh,0%Z)=Some(V293_byteval nh)).
 { eapply V293_record_star_load_l with
 (s:=(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op))
 (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - unfold Owned in Held;sep auto. }
 assert(ToWrite:(ge,V293_cpu_lenv saved saved_block,M,ir,(false,nil,top::ci),O,op)|=
 V293_owned_record_cell((bc,0%Z),Tint8,old) **
 (Amapsto(saved_block,0%Z)Tint32 true saved_value **
 (SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **V293_storage rest)))))
 by(unfold Owned in Held;sep auto).
 destruct(V293_owned_record_cell_update _ _ _ (V293_byteval nh) _ _ _ _ _ _ _ _
 (V293_byte_type nh Range)ToWrite)as(Mc&Store&Written).
 assert(AfterOwned:(ge,V293_cpu_lenv saved saved_block,Mc,ir,(false,nil,top::ci),O,op)|=Owned(V293_byteval nh))
 by(unfold Owned;clear Held;sep auto).
 eapply V293_copy_csteps_TaskSim;[ | | | | |exact Store| | | ].
 - eapply V293_context_inos with(ks:=kcall f body caller tail);[eapply V293_bound_call_inos;exact Bind|reflexivity|reflexivity].
 - cbn[evaltype];rewrite CN,CG;reflexivity.
 - cbn[evaltype];rewrite HN,HG;reflexivity.
 - cbn[evalval evaltype get_lenv get_genv];rewrite HN,HG;cbn -[load];exact High.
 - cbn[evalval evaladdr evaltype get_lenv get_genv];rewrite CN,CG;reflexivity.
 - eapply V293_copy_owned_local;exact Held.
 - eapply V293_copy_owned_local;exact AfterOwned.
 - unfold G;eapply V293_storage_switch_TaskSim;[exact Sched|exact Bind|exact Cases| ].
   eapply V293_copy_switch_resources;[exact Target|exact Map|exact Member|exact Highest|exact AfterOwned].
Qed.
End OwnedCopy.
