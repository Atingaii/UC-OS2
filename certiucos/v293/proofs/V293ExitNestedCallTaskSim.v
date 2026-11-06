(* Original nested no-dispatch branch; same storage invariant, no abstract schedule. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Local Open Scope nat_scope.

Lemma V293_nested_nil_api_enter : forall pc A f ks t cst O,
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 htstep(pc,A)t(curs(sfexec f nil nil),(kenil,ks))cst O
 (curs(hapi_code(spec_done None)),(kenil,ks))cst O.
Proof.
 intros pc [[B C]D] f ks t cst O Bind.
 eapply hapi_step;[reflexivity| ].
 eapply hapienter_step with(vl:=nil)(tl:=nil)(tp:=Tvoid)
 (r:=fun _:vallist=>spec_done None);try reflexivity;exact Bind.
Qed.

Lemma V293_nested_nil_call_bridge : forall pc po pi ip A f ks o O li I Post t,
 ~InOS(curs(scall f nil),(kenil,ks))(pumerge po pi) ->
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 satp o O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,ks))o
 (pc,A)(SKIP,(kenil,ks))O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,ks))o
 (pc,A)(curs(scall f nil),(kenil,ks))O li I Post t.
Proof.
 intros pc po pi ip A f ks o O li I Post t Outside Bind Local API.
 apply task_sim.
 - intros Cf Ms Mf cst cst' ofull Os o2 OO Inv JM JO Low.
   destruct(V293_client_nil_call_low _ _ _ _ A _ _ _ _ _ _ _ OO _ Outside Low)
   as[Same[Code Match]];subst ofull Cf.
   exists(SKIP,(kenil,ks));
   exists OO;exists o;exists Ms;exists O;exists Os.
   split.
   + eapply ht_starS;[exact Match| ];eapply ht_starS;
     [apply V293_nested_nil_api_enter;exact Bind| ];eapply ht_starS;
     [eapply hapi_step;[reflexivity|apply hapiexit_step]|apply ht_starO].
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


Lemma V293_nested_zero_eval : forall ge le M x b n,
 0<n ->n<256 ->get le x=None ->get ge x=Some(b,Tint8) ->
 load Tint8 M(b,0%Z)=Some(V293_byteval n) ->
 evalval(V293_OSSched_zero x)(ge,le,M)=Some(Vint32 Int.zero).
Proof.
 intros ge le M x b n Pos Bound NL G Read.
 unfold V293_OSSched_zero;cbn[evalval evaltype get_lenv get_genv];rewrite NL,G.
 cbn -[load];rewrite Read;unfold V293_byteval.
 cbn[cast_eval bop_eval val_eq bop_type].
 rewrite V293_guard_eq_zero by exact Bound.
 assert(E:Nat.eqb n 0=false)by(apply Nat.eqb_neq;lia).
 rewrite E;reflexivity.
Qed.

(* Internal cut: concrete decrement and false outer guard; no lock lookup. *)
Lemma V293_nested_prefix_TaskSim : forall pc po pi ip ph Ch O I Post t ks
 ge le M ir ci op nesting lock bn bl n R dispatch,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 2<=n ->n<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 (R ==>CurTid t **Atrue) ->
 (ge,le,M,ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl n R ->
 (forall M',(ge,le,M',ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl(Nat.pred n)R ->
  TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))
  (ge,le,M',ir,(false,nil,ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(V293_OSIntExit_nesting_dispatch nesting lock dispatch),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge le M ir ci op nesting lock bn bl n R dispatch
 Inside Nested Bound NN NG Current Held Continue.
 assert(Before:satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact Current|exact Held]. }
 assert(NRead:load Tint8 M(bn,0%Z)=Some(V293_byteval n)).
 { change(load Tint8(assertion.getmem(ge,le,M,ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval n)).
   unfold V293_exit_guard_resource in Held;eapply V293_record_star_load_l;[ |exact Held];
   intros;eapply V293_owned_record_cell_load;eassumption. }
 destruct(V293_exit_decrement_eval ge le M nesting bn n Bound NN NG NRead)as[Positive Assignment].
 destruct(V293_owned_record_cell_update _ _ _ (V293_byteval(Nat.pred n)) _ _ _ _ _ _ _ _
  (V293_byte_type(Nat.pred n)ltac:(lia)) Held)as(M'&Store&Updated).
 assert(After:satp(ge,le,M',ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact Current|exact Updated]. }
 assert(NextRead:load Tint8 M'(bn,0%Z)=Some(V293_byteval(Nat.pred n))).
 { change(load Tint8(assertion.getmem(ge,le,M',ir,(false,nil,ci),O,op))(bn,0%Z)=Some(V293_byteval(Nat.pred n))).
   unfold V293_exit_guard_resource in Updated;eapply V293_record_star_load_l;[ |exact Updated];
   intros;eapply V293_owned_record_cell_load;eassumption. }
 assert(IsPos:Nat.eqb n 0=false)by(apply Nat.eqb_neq;lia).
 rewrite IsPos in Positive.
 unfold V293_OSIntExit_nesting_dispatch.
 eapply V293_changed_pure_TaskSim with(ks:=ks);
 [exact Inside|reflexivity|reflexivity| | |exact Before| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - unfold V293_OSIntExit_decrement.
   eapply V293_exit_ifthen_TaskSim with(v:=Vint32 Int.one)(take:=true);
   [eapply V293_context_inos;[exact Inside|reflexivity|reflexivity]|exact Before|exact Positive|reflexivity| ].
   destruct(Assignment ltac:(lia))as(TL&Addr&TR&Value).
   eapply V293_helper_assignment_TaskSim;
   [eapply V293_context_inos;[exact Inside|reflexivity|reflexivity]|exact TL|exact Addr|exact TR|exact Value|exact Store|exact Before|exact After| ].
   eapply V293_changed_pure_TaskSim with(ks:=ks);
   [exact Inside|reflexivity|reflexivity| | |exact After| ].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sskip_step].
   + unfold V293_OSIntExit_guards.
     eapply V293_changed_if_TaskSim with(v:=Vint32 Int.zero)(take:=false);
     [exact Inside|exact After|exact(V293_nested_zero_eval ge le M' nesting bn(Nat.pred n)ltac:(lia)ltac:(lia)NN NG NextRead)|reflexivity| ].
     apply Continue;exact Updated.
Qed.

Section NestedCall.
Variables br bg bp bt bc bh bo bk bn bl bu : block.
Variable rest : list(addr*type).
Variable target : var.
Variable t : tid.
Variable nc : nat.
Variable oldtarget : val.
Variable c : int32.
Let Res:=V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c.
Let Cells:=((bc,0%Z),Tint8)::((bh,0%Z),Tint8)::((bk,0%Z),Tint32)::
 (V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)++
 (((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::((bu,0%Z),Tint8)::rest)).
Let G:=V293_ready_storage_inv br bg bp target V293_tcb_type Cells.
Let Core:=V293_ready_storage_core br bg bp target V293_tcb_type Cells.

Lemma V293_nested_reclose : forall n hv ge le M ir aux O op,
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,le,M,ir,aux,O,op)|=Res n hv ->
 (ge,le,M,ir,aux,O,op)|=Core **CurTid t.
Proof.
 intros n hv ge le M ir aux O op Target Held.
 assert(CellsOwned:
 V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
 (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
 (V293_read_bytes bt 0%Z V293_ready_table **
 (V293_read_bytes bt 0%Z V293_ready_table **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **V293_storage rest))))))) ==>
 V293_storage Cells).
 { intros s H.
   assert(Pair:s|=(V293_read_bytes bt 0%Z V293_ready_table **
    V293_read_bytes bt 0%Z V293_ready_table) **
    (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
    (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
    (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
    (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
    (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
    (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **V293_storage rest)))))))by(sep auto).
   eapply astar_mono in Pair;[ |apply V293_helper_decoder_storage|intros st H';exact H'].
   assert(Pack:s|=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
    (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
    (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
    (V293_storage(V293_array_cells bt 0%Z 1%Z Tint8(length V293_ready_table)) **
    (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
    (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
    (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **V293_storage rest)))))))by(clear H;sep auto).
   unfold Cells;cbn[V293_storage].
   eapply astar_mono;[apply V293_exit_cell_to_storage| |exact Pack].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   intros st Owned;apply V293_storage_append.
   eapply astar_mono;[intros st' H';exact H'| |exact Owned].
   cbn[V293_storage];repeat apply astar_mono;try(intros st' H';exact H');
   apply V293_exit_cell_to_storage. }

 assert(Global:forall m o,
 (ge,le,m,ir,aux,o,op)|=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) ->
 (ge,le,m,ir,aux,o,op)|=V293_dispatch_cell target V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[Typed H].
   exists oldtarget;apply astar_l_apure_intro;[ |exact Typed].
   exists bo;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;[reflexivity|exact Target]]. }
 assert(Pack:(ge,le,M,ir,aux,O,op)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **V293_ready_storage_extra target V293_tcb_type Cells).
 { unfold Res,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame in Held.
   assert(Reorder:(ge,le,M,ir,aux,O,op)|=
    (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
    (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
    (V293_owned_record_cell((bk,0%Z),Tint32,Vint32 c) **
    (V293_read_bytes bt 0%Z V293_ready_table **
    (V293_read_bytes bt 0%Z V293_ready_table **
    (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
    (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
    (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **V293_storage rest)))))))) **
    (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
    SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t))by(sep auto).
   eapply astar_mono with(P':=V293_storage Cells)in Reorder;[ |exact CellsOwned|intros st H;exact H].
   apply sat_split in Reorder;destruct Reorder as(ms&mr&os&orr&JM&JO&Storage&Rest).
   apply sat_split in Rest;destruct Rest as(mt&mc&ot&oc&JM'&JO'&Cell&Ready).
   apply Global in Cell.
   unfold V293_ready_storage_extra.
   assert(All:(ge,le,M,ir,aux,O,op)|=V293_storage Cells **
    (V293_dispatch_cell target V293_tcb_type **SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t)).
   { apply sat_split';exists ms;exists mr;exists os;exists orr;repeat first[assumption|split].
     apply sat_split';exists mt;exists mc;exists ot;exists oc;repeat first[assumption|split]. }
   sep auto. }
 apply V293_ready_storage_switch_resources in Pack.
 unfold SWINVt in Pack;fold(CurTid t)in Pack.
 eapply astar_mono with(P':=V293_shared_flags **Core)in Pack;
 [ |apply V293_ready_storage_switch_open|intros st H;exact H].
 assert(Empty:V293_shared_flags ==>Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 apply astar_l_aemp_elim.
 eapply astar_mono;[exact Empty|intros st H;exact H| ].
 clear Empty;sep auto.
Qed.

Lemma V293_nested_saved_stack : forall n hv bs v ge le M ir ci ci' O op,
 (ge,le,M,ir,(false,nil,ci),O,op)|=Amapsto(bs,0%Z)Tint32 true v **Res n hv ->
 (ge,le,M,ir,(false,nil,ci'),O,op)|=Amapsto(bs,0%Z)Tint32 true v **Res n hv.
Proof.
 intros n hv bs v ge le M ir ci ci' O op Held.
 set(Tail:=Amapsto(bs,0%Z)Tint32 true v **
 (V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **
 (V293_read_bytes bt 0%Z V293_ready_table **
 V293_exit_active_frame bt bc bo bk rest nc oldtarget c)))))).
 assert(Pack:(ge,le,M,ir,(false,nil,ci),O,op)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv br bg bp)t **Tail).
 { unfold Tail,Res,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource in *;sep auto. }
 assert(Good:GoodInvAsrt Tail).
 { unfold Tail,V293_owned_record_cell;split;[cbn;auto| ];
   split;[cbn;auto| ];split;[cbn;auto| ];split;[cbn;auto| ];
   split;[cbn;auto| ];split;[apply V293_helper_read_good|apply V293_exit_active_frame_good]. }
 pose proof(V293_ready_critical_stack br bg bp t Tail ge le M ir nil ci ci' O op Good Pack)as Move.
 unfold Tail,Res,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource in *.
 clear Held Pack;sep auto.
Qed.

Lemma V293_nested_critical_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f body caller tail tau d1 d2 saved bs
 helper oldhigh nesting lock n,
 po f=Some(tau,d1,d2,body) ->V293_skip_client_state(SKIP,(kenil,tail)) ->
 2<=n ->n<256 ->saved<>nesting ->
 get ge nesting=Some(bn,Tint8) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Res n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter helper
 (V293_interrupt_handoff high current target)))(sprim excrit))),
 (kenil,kseq sret(kcall f body caller tail)))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f body caller tail tau d1 d2 saved bs
 helper oldhigh nesting lock n Bind Cases Nested Bound SN NG TG Held.
 assert(Inside:InOS(SKIP,(kenil,kcall f body caller tail))(pumerge po pi)).
 { eapply V293_bound_call_inos;exact Bind. }
 assert(Context:forall ks,callcont ks=callcont(kcall f body caller tail) ->
 intcont ks=intcont(kcall f body caller tail) ->InOS(SKIP,(kenil,ks))(pumerge po pi)).
 { intros;eapply V293_context_inos;eassumption. }
 set(R:=V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 1) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_helper_resource br bg bp bt bh t
 (V293_exit_active_frame bt bc bo bk rest nc oldtarget c)oldhigh)).
 assert(ResourceCurrent:R ==>CurTid t **Atrue).
 { unfold R;intros s H.
   apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in H;[sep auto|intros st H';exact Logic.I| ].
   intros st H';apply astar_mono with(P':=Atrue)(Q':=CurTid t **Atrue)in H';
   [sep auto|intros st' H0;exact Logic.I|apply V293_helper_resource_current]. }
 assert(Pack:(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=V293_exit_guard_resource bn bl n R).
 { unfold R,Res,V293_exit_active_resource,V293_exit_guard_resource in *;sep auto. }
 assert(Before:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact ResourceCurrent|exact Pack]. }
 assert(Entered:(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,false::ci),O,op)|=
 V293_exit_guard_resource bn bl n R).
 { pose proof(V293_nested_saved_stack n oldhigh bs(Vint32 Int.zero) _ _ _ _ ci(false::ci) _ _ Held)as Move.
   unfold R,Res,V293_exit_active_resource,V293_exit_guard_resource in *;clear Held Pack;sep auto. }
 assert(After:satp(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,false::ci))O(CurLINV V293_shared_li t)).
 { eapply V293_exit_guards_local;[exact ResourceCurrent|exact Entered]. }
 assert(Clear:forall i,ir i=false).
 { eapply(V293_shared_clear_state ge(V293_cpu_lenv saved bs)M ir(false,nil,ci)O op).
   assert(Switch:(ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
   SWINV(V293ReadyTaskInvariant.V293_ready_inv br bg bp) **Atrue).
   { unfold Res,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource,SWINVt in Held;clear -Held;sep auto. }
   eapply astar_mono in Switch;[ |apply V293_ready_switch_open|intros st H;exact H].
   unfold V293_shared_flags in Switch;sep normal in Switch;sep destruct Switch;clear -Switch;sep auto. }
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
       -- eapply V293_nested_prefix_TaskSim with(op:=op)(n:=n)(bn:=bn)(bl:=bl)(R:=R).
          ++ apply Context;reflexivity.
          ++ exact Nested.
          ++ exact Bound.
          ++ unfold V293_cpu_lenv;rewrite map_get_set' by congruence;apply map_emp_get.
          ++ exact NG.
          ++ exact ResourceCurrent.
          ++ exact Entered.
          ++ intros M' Ready.
             assert(Saved:(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,false::ci),O,op)|=
             Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Res(Nat.pred n)oldhigh).
             { unfold R,Res,V293_exit_active_resource,V293_exit_guard_resource in *;sep auto. }
             apply sat_split in Saved;destruct Saved as(ms&mr&os&orr&JM&JO&Cell&Active).
             pose proof(V293_nested_reclose(Nat.pred n)oldhigh _ _ _ _ _ _ _ TG Active)as Closed.
             assert(Final:(ge,V293_cpu_lenv saved bs,M',ir,(false,nil,false::ci),O,op)|=
             Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **(Core **CurTid t)).
             { apply sat_split';exists ms;exists mr;exists os;exists orr;repeat first[assumption|split]. }
             unfold G,Core in *.
             eapply V293_storage_pending_TaskSim;[exact Bind|exact Cases|exact Clear|exact Final].
Qed.
Lemma V293_nested_body_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved bs
 helper oldhigh running nesting lock n,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 2<=n ->n<256 ->saved<>running ->saved<>nesting ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true Vundef **Res n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target))caller tail))
 (ge,V293_cpu_lenv saved bs,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved bs
 helper oldhigh running nesting lock n Bind Cases Nested Bound SU SN UG NG TG Held.
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
 (Res n oldhigh) _ _ _ _ _ _ _ eq_refl Held)as(M'&Store&Updated).
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
          eapply V293_nested_critical_TaskSim with(oldhigh:=oldhigh)(n:=n)(op:=op);try eassumption.
          unfold V293_owned_record_cell in Updated;sep normal in Updated;sep destruct Updated;clear -Updated;sep auto.
Qed.

Lemma V293_nested_entry_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper oldhigh running nesting lock n,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 2<=n ->n<256 ->saved<>running ->saved<>nesting ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(sfexec f nil nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(SKIP,(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper oldhigh running nesting lock n Bind Cases Nested Bound SU SN UG NG TG Held.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)).
 set(k:=kcall f body caller tail).
 set(ph:=(pc,A):hprog).
 set(Ch:=(SKIP,(kenil,tail)):code).
 set(Post:=fun st:taskst*osabst=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil)).
 set(EntryRes:=Res n oldhigh).
 assert(Body:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint32 true Vundef **EntryRes ->
  TaskSim(pc,(po,pi,ip))(curs body,(kenil,k))
   (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci))
   ph Ch O V293_shared_li G Post t).
 { intros b Fresh Own;unfold body,k,ph,Ch,Post,EntryRes in *.
   eapply V293_nested_body_TaskSim with(op:=op)(oldhigh:=oldhigh);eassumption. }
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons saved Tint32 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k,body;eapply V293_bound_call_inos;exact Bind. }
 assert(CurrentRes:forall s,s|=EntryRes ->s|=CurTid t **Atrue).
 { unfold EntryRes;apply V293_exit_active_current. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply CurrentRes.
   eapply V293_exit_active_lenv;exact Held. }
 assert(Allocated:forall b,fresh M b ->
  (ge,V293_cpu_lenv saved b,allocb M b 0%Z(typelen Tint32),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint32 true Vundef **EntryRes).
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
Theorem V293_exit_nested_client_call_TaskSim : forall pc po pi ip A ge M ir ci O op
 table high current counter f caller tail saved
 helper oldhigh running nesting lock n,
 fst(fst A)f=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) ->
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter helper
 (V293_interrupt_handoff high current target)) ->
 V293_skip_client_state(SKIP,(kenil,tail)) ->
 2<=n ->n<256 ->saved<>running ->saved<>nesting ->
 get ge running=Some(bu,Tint8) ->get ge nesting=Some(bn,Tint8) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=Res n oldhigh ->
 TaskSim(pc,(po,pi,ip))
 (curs(scall f nil),(kenil,tail))
 (ge,caller,M,ir,(false,nil,ci))
 (pc,A)(curs(scall f nil),(kenil,tail))O V293_shared_li G
 (fun st=>satp(fst st)(snd st)(RDYINV G t **LINV V293_shared_li t nil))t.
Proof.
 intros pc po pi ip A ge M ir ci O op table high current counter f caller tail saved
 helper oldhigh running nesting lock n APIBind Bind Cases Nested Bound SU SN UG NG TG Held.
 eapply V293_nested_nil_call_bridge.
 - apply V293_client_nil_call_outside;exact Cases.
 - exact APIBind.
 - eapply V293_pending_local with(op:=op).
   eapply V293_exit_active_current;exact Held.
 - eapply V293_nested_entry_TaskSim with(op:=op)(oldhigh:=oldhigh)(n:=n);eassumption.
Qed.
End NestedCall.
