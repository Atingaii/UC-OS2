(* Original helper assignments, resource-preserving return and full call TaskSim. *)
Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.

Lemma V293_helper_assignment_TaskSim : forall pc po pi ip ph Ch O li I Post t ks
 ge le M M' ir ci e1 e2 b v,
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->
 evaltype e1(ge,le,M)=Some Tint8 ->
 evaladdr e1(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 evaltype e2(ge,le,M)=Some Tint8 ->evalval e2(ge,le,M)=Some v ->
 store Tint8 M(b,0%Z)v=Some M' ->
 satp(ge,le,M,ir,(false,nil,ci))O(CurLINV li t) ->
 satp(ge,le,M',ir,(false,nil,ci))O(CurLINV li t) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,le,M',ir,(false,nil,ci))ph Ch O li I Post t ->
 TaskSim(pc,(po,pi,ip))(curs(sassign e1 e2),(kenil,ks))
 (ge,le,M,ir,(false,nil,ci))ph Ch O li I Post t.
Proof.
 intros pc po pi ip ph Ch O li I Post t ks ge le M M' ir ci e1 e2 b v
 Context TL Addr TR Value Store Before After Tail.
 eapply V293_changed_pure_TaskSim with(ks:=ks)
 (C':=(cure e2,(kenil,kassignr e1 Tint8 ks)));
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
     (C':=(cure(eaddrof e1),(kenil,kassignl v Tint8 ks)));
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


Lemma V293_helper_read_good : forall vs b off,GoodInvAsrt(V293_read_bytes b off vs).
Proof. induction vs;intros;cbn;auto. Qed.

Definition V293_helper_resource br bg bp bt bh t R hv :=
 SWINVt(V293_ready_inv br bg bp)t **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **(V293_read_bytes bt 0%Z V293_ready_table **R)).

Lemma V293_helper_resource_lenv : forall br bg bp bt bh t R hv ge le M ir aux O op le',
 GoodInvAsrt R ->
 (ge,le,M,ir,aux,O,op)|=V293_helper_resource br bg bp bt bh t R hv ->
 (ge,le',M,ir,aux,O,op)|=V293_helper_resource br bg bp bt bh t R hv.
Proof.
 intros;unfold V293_helper_resource in *;eapply V293_ready_lenv_frame;[ |eassumption].
 split;[unfold V293_owned_record_cell;cbn;auto|split;[apply V293_helper_read_good|assumption]].
Qed.

Lemma V293_helper_cell_resource_lenv : forall br bg bp bt bh t R hv b v ge le M ir aux O op le',
 GoodInvAsrt R ->
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true v **V293_helper_resource br bg bp bt bh t R hv ->
 (ge,le',M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint8 true v **V293_helper_resource br bg bp bt bh t R hv.
Proof.
 intros br bg bp bt bh t R hv b v ge le M ir aux O op le' Good Held.
 assert(Reordered:(ge,le,M,ir,aux,O,op)|=
 SWINVt(V293_ready_inv br bg bp)t **
 (Amapsto(b,0%Z)Tint8 true v **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **(V293_read_bytes bt 0%Z V293_ready_table **R)))).
 { unfold V293_helper_resource in Held;sep auto. }
 assert(Changed:(ge,le',M,ir,aux,O,op)|=
 SWINVt(V293_ready_inv br bg bp)t **
 (Amapsto(b,0%Z)Tint8 true v **
 (V293_owned_record_cell((bh,0%Z),Tint8,hv) **(V293_read_bytes bt 0%Z V293_ready_table **R)))).
 { eapply V293_ready_lenv_frame;[ |exact Reordered].
   split;[exact Logic.I|split;[unfold V293_owned_record_cell;cbn;auto|split;[apply V293_helper_read_good|exact Good]]]. }
 unfold V293_helper_resource;clear Held Reordered;sep auto.
Qed.

Lemma V293_helper_resource_current : forall br bg bp bt bh t R hv s,
 s|=V293_helper_resource br bg bp bt bh t R hv ->s|=CurTid t **Atrue.
Proof. intros;unfold V293_helper_resource,SWINVt in H;fold(CurTid t)in H;sep auto. Qed.

Lemma V293_helper_ready_return_TaskSim : forall pc po pi ip ph Ch O I Post t
 ks ge caller M ir ci op R f unmap group rows high y b v br bg bp bt bh hv,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 GoodInvAsrt R ->
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true v **V293_helper_resource br bg bp bt bh t R hv ->
 (forall Mret,(ge,caller,Mret,ir,(false,nil,ci),O,op)|=V293_helper_resource br bg bp bt bh t R hv ->
  TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))
  ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq sret(kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks)))
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge caller M ir ci op R f unmap group rows high y b v br bg bp bt bh hv
 Bind Good Held Tail.
 set(le:=set(emp:env)y(b,Tint8)).
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(k:=kcall f body caller ks).
 assert(Before:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op).
   assert(Own:(ge,le',M,ir,(false,nil,ci),O,op)|=Amapsto(b,0%Z)Tint8 true v **V293_helper_resource br bg bp bt bh t R hv).
   { eapply V293_helper_cell_resource_lenv;[exact Good|exact Held]. }
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true v)(Q':=CurTid t **Atrue)in Own;
    [clear Held;sep auto|intros st H;exact H|intros st H;eapply V293_helper_resource_current;exact H]. }
 destruct(V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Held)as(Mret&Freed&Rest&Removed&Outside).
 assert(After:forall le',satp(ge,le',Mret,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);eapply V293_helper_resource_current.
   eapply V293_helper_resource_lenv;[exact Good|exact Rest]. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k;eapply V293_bound_call_inos;exact Bind. }
 assert(End:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))
 ph Ch O V293_shared_li I Post t).
 { apply Tail;eapply V293_helper_resource_lenv;[exact Good|exact Rest]. }
 assert(FreeEnd:TaskSim(pc,(po,pi,ip))(curs(sfree nil None),(kenil,k))
 (ge,le,Mret,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact End].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + unfold k;eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity.
     + intros;eapply V293_free_end_successor;eassumption. }
 assert(FreeCell:TaskSim(pc,(po,pi,ip))(curs(sfree((b,Tint8)::nil)None),(kenil,k))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply After|exact FreeEnd].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(free_mono _ _ _ _ _ _ Join Freed)as(Mall'&Free').
     exists Mall';split;[eapply join_free;eassumption| ];split.
     + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact Free'].
     + intros;eapply V293_free_one_successor;eassumption. }
 assert(Return:TaskSim(pc,(po,pi,ip))(curs sret,(kenil,k))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply Before|exact FreeCell].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs sret,(kenil,k))(ge,le,Mall)
      (curs(sfree((b,Tint8)::nil)None),(kenil,k))(ge,le,Mall)).
     { unfold k,le;eapply stmt_step;[reflexivity| ];eapply sret_step;
      [reflexivity|reflexivity|apply V293_helper_byte_layout]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Before|exact Return].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(SKIP,(kenil,kseq sret k))(ge,le,Mall)
    (curs sret,(kenil,k))(ge,le,Mall)).
   { eapply stmt_step;[reflexivity|apply sskip_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.

Lemma V293_helper_body_TaskSim : forall pc po pi ip ph Ch O I Post t
 ks ge caller M ir ci op R f unmap group rows high y br bg bp bt bh b oldy oldhigh,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->GoodInvAsrt R ->
 V293_sched_read_env ge(set(emp:env)y(b,Tint8))unmap group rows bt bg br ->
 get(set(emp:env)y(b,Tint8))high=None ->get ge high=Some(bh,Tint8) ->
 b<>bt ->b<>bg ->b<>br ->
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true oldy **V293_helper_resource br bg bp bt bh t R oldhigh ->
 (forall tasks lo hi entries next message Mret,
 get O abstcblsid=Some(abstcblist tasks) ->V293_ready_rel lo hi entries tasks ->
 get tasks next=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) ->
 (ge,caller,Mret,ir,(false,nil,ci),O,op)|=
 V293_helper_resource br bg bp bt bh t R(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))
 (curs(V293_OSSchedNew_body unmap group rows high y),
 (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))
 (ge,set(emp:env)y(b,Tint8),M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge caller M ir ci op R f unmap group rows high y br bg bp bt bh b oldy oldhigh
 Bind Good Env HN HG BT BG BR Held Tail.
 set(le:=set(emp:env)y(b,Tint8))in *.
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(k:=kcall f body caller ks).
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k;eapply V293_bound_call_inos;exact Bind. }
 assert(Ready:(ge,le,M,ir,(false,nil,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)t **Atrue).
 { unfold V293_helper_resource in Held;sep auto. }
 destruct(V293_ready_switch_selected br bg bp _ _ _ Ready)
 as(tasks&lo&hi&entries&next&message&Map&Rel&Loads&Task&Pointer&Sched).
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]].
 set(g:=V293_ready_group lo hi).
 set(ny:=V293_ready_lookup g).
 set(nh:=V293_ready_select lo hi g).
 assert(GB:g<256)by(unfold g,V293_ready_group;destruct(lo=?0);destruct(hi=?0);lia).
 assert(YB:ny<256)by(unfold ny;pose proof(proj1(V293_ready_row_spec g GB));lia).
 assert(HB:nh<13)by(unfold nh,g;apply V293_ready_selection_range;assumption||reflexivity).
 assert(Lookup:forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n N;eapply V293_record_star_load_l with(s:=(ge,le,M,ir,(false,nil,ci),O,op))
 (P:=V293_read_bytes bt 0%Z V293_ready_table)(Q:=Atrue).
 - intros st H;replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia.
   change(V293_ready_lookup n)with(nth n V293_ready_table 0).
   eapply V293_read_bytes_load;[change(n<256);exact N|pose proof(proj1(V293_ready_row_spec n N));unfold V293_ready_lookup in *;lia|exact H].
 - unfold V293_helper_resource in Held;clear Ready;sep auto. }
 assert(Reads:V293_sched_read_memory M bt bg br lo hi g).
 { destruct Loads as[L[H[G T]]];unfold V293_sched_read_memory;auto. }
 destruct(V293_OSSchedNew_row_eval ge le M unmap group rows bt bg br lo hi g Env Reads GB)as[VY TY].
 assert(First:(ge,le,M,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true oldy **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (SWINVt(V293_ready_inv br bg bp)t **(V293_read_bytes bt 0%Z V293_ready_table **R)))).
 { unfold V293_helper_resource in Held;clear Ready;sep auto. }
 pose proof(V293_tick_raw_owned_writable b Tint8 oldy _ _ _ _ _ _ _ _ First)as WY.
 destruct(WY 0 ltac:(cbn;lia))as(vy&WY0).
 change(get M(b,0%Z)=Some(true,vy))in WY0.
 destruct(V293_tick_raw_slot_update(b,0%Z)Tint8 oldy(V293_byteval ny)
 _ _ _ _ _ _ _ _(V293_byte_type _ YB)First)as(M1&StoreY&WrittenY).
 pose proof(V293_write_byte_store M b ny vy WY0)as StoreY'.
 assert(E1:M1=V293_write_byte M b ny)by congruence.
 assert(Second:(ge,le,M1,ir,(false,nil,ci),O,op)|=
 V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((b,0%Z),Tint8,V293_byteval ny) **
 (SWINVt(V293_ready_inv br bg bp)t **(V293_read_bytes bt 0%Z V293_ready_table **R)))).
 { clear First Held Ready;sep auto. }
 destruct(V293_owned_record_cell_update(bh,0%Z)Tint8 oldhigh(V293_byteval nh)
 _ _ _ _ _ _ _ _(V293_byte_type nh ltac:(lia))Second)as(M2&StoreH&WrittenH).
 assert(Reads1:V293_sched_read_memory M1 bt bg br lo hi g).
 { rewrite E1;apply V293_write_byte_reads;assumption. }
 assert(YLoad:load Tint8 M1(b,0%Z)=Some(V293_byteval ny)).
 { rewrite E1;apply V293_write_byte_load;exact YB. }
 destruct(V293_OSSchedNew_priority_eval ge le M1 unmap group rows y bt bg br b lo hi g
 Env Reads1 ltac:(unfold le;apply map_get_set)YLoad Lo Hi eq_refl Nonempty)as[VH TH].
 assert(Owned1:(ge,le,M1,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true(V293_byteval ny) **V293_helper_resource br bg bp bt bh t R oldhigh).
 { unfold V293_helper_resource,V293_owned_record_cell in *;clear First Held Ready;sep auto. }
 assert(Owned2:(ge,le,M2,ir,(false,nil,ci),O,op)|=
 Amapsto(b,0%Z)Tint8 true(V293_byteval ny) **V293_helper_resource br bg bp bt bh t R(V293_byteval nh)).
 { unfold V293_helper_resource,V293_owned_record_cell in *;clear First Held Ready;sep auto. }
 assert(Local0:satp(ge,le,M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true oldy)(Q':=CurTid t **Atrue)in Held;
   [clear - Held;sep auto|intros st H;exact H|intros st H;eapply V293_helper_resource_current;exact H]. }
 assert(Local1:satp(ge,le,M1,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true (V293_byteval ny))(Q':=CurTid t **Atrue)in Owned1;
   [clear - Owned1;sep auto|intros st H;exact H|intros st H;eapply V293_helper_resource_current;exact H]. }
 assert(Local2:satp(ge,le,M2,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { eapply V293_pending_local with(op:=op).
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true (V293_byteval ny))(Q':=CurTid t **Atrue)in Owned2;
   [clear - Owned2;sep auto|intros st H;exact H|intros st H;eapply V293_helper_resource_current;exact H]. }
 assert(Return:TaskSim(pc,(po,pi,ip))(SKIP,(kenil,kseq sret k))
 (ge,le,M2,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { unfold le,k,body;eapply V293_helper_ready_return_TaskSim
 with(R:=R)(op:=op)(v:=V293_byteval ny).
 - exact Bind.
 - exact Good.
 - exact Owned2.
 - intros Mret Rest;eapply Tail;[exact Map|exact(conj Lo(conj Hi(conj Nonempty(conj Bitmap Table))))|exact Task|exact Rest]. }
 assert(HighSim:TaskSim(pc,(po,pi,ip))
 (curs(sassign(evar high)(V293_OSSchedNew_priority_expr unmap rows y)),(kenil,kseq sret k))
 (ge,le,M1,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_helper_assignment_TaskSim;
 [ | | |exact TH|exact VH|exact StoreH|exact Local1|exact Local2|exact Return].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - cbn[evaltype];rewrite HN,HG;reflexivity.
 - cbn[evaladdr get_lenv get_genv];rewrite HN,HG;reflexivity. }
 assert(Between:TaskSim(pc,(po,pi,ip))
 (SKIP,(kenil,kseq(sassign(evar high)(V293_OSSchedNew_priority_expr unmap rows y))(kseq sret k)))
 (ge,le,M1,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_changed_pure_TaskSim with(ks:=k);[exact Inside|reflexivity|reflexivity| | |exact Local1|exact HighSim].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sskip_step]. }
 assert(RowSim:TaskSim(pc,(po,pi,ip))
 (curs(sassign(evar y)(V293_OSSchedNew_row_expr unmap group)),
 (kenil,kseq(sassign(evar high)(V293_OSSchedNew_priority_expr unmap rows y))(kseq sret k)))
 (ge,le,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_helper_assignment_TaskSim;
 [ | | |exact TY|exact VY|exact StoreY|exact Local0|exact Local1|exact Between].
 - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
 - cbn[evaltype];unfold le;rewrite map_get_set;reflexivity.
 - cbn[evaladdr get_lenv];unfold le;rewrite map_get_set;reflexivity. }
 unfold body,V293_OSSchedNew_body,V293_OSSchedNew_updates.
 eapply V293_changed_pure_TaskSim with(ks:=k);[exact Inside|reflexivity|reflexivity| | |exact Local0| ].
 - intros[x E];discriminate E.
 - intros;eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_changed_pure_TaskSim with(ks:=k);[exact Inside|reflexivity|reflexivity| | |exact Local0|exact RowSim].
   + intros[x E];discriminate E.
   + intros;eapply stmt_step;[reflexivity|apply sseq_step].
Qed.

Lemma V293_helper_fresh_byte_distinct : forall M b c off v,
 fresh M b ->load Tint8 M(c,off)=Some v ->b<>c.
Proof.
 intros M b c off v Fresh Loaded E;subst c.
 unfold load,loadm in Loaded;cbn[typelen loadbytes]in Loaded.
 unfold addr,offset in *.
 destruct(get M(b,off))as [[permission datum] | ] eqn:Get;[ |discriminate].
 exfalso;eapply Fresh;[reflexivity|exists(permission,datum);exact Get].
Qed.

(* Both original assignments, all fresh allocations, and the actual return.
   Only the restored caller continuation remains a composition premise. *)
Theorem V293_sched_helper_full_TaskSim : forall pc po pi ip ph Ch O I Post t
 ks ge caller M ir ci op R f unmap group rows high y br bg bp bt bh oldhigh,
 po f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->GoodInvAsrt R ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 (ge,caller,M,ir,(false,nil,ci),O,op)|=V293_helper_resource br bg bp bt bh t R oldhigh ->
 (forall tasks lo hi entries next message Mret,
 get O abstcblsid=Some(abstcblist tasks) ->V293_ready_rel lo hi entries tasks ->
 get tasks next=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) ->
 (ge,caller,Mret,ir,(false,nil,ci),O,op)|=
 V293_helper_resource br bg bp bt bh t R(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) ->
 TaskSim(pc,(po,pi,ip))(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t) ->
 TaskSim(pc,(po,pi,ip))(curs(scall f nil),(kenil,ks))
 (ge,caller,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t.
Proof.
 intros pc po pi ip ph Ch O I Post t ks ge caller M ir ci op R f unmap group rows high y br bg bp bt bh oldhigh
 Bind Context Good YT YG YR YH GT GG GR GH Held Tail.
 assert(Ready:(ge,caller,M,ir,(false,nil,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)t **Atrue).
 { unfold V293_helper_resource in Held;sep auto. }
 destruct(V293_ready_switch_selected br bg bp _ _ _ Ready)
 as(tasks&lo&hi&entries&next&message&Map&Rel&Loads&Task&Pointer&Sched).
 destruct Loads as[Row0[Row1[Group Table]]].
 assert(Lookup0:load Tint8 M(bt,0%Z)=Some(V293_byteval(V293_ready_lookup 0))).
 { eapply V293_record_star_load_l with(s:=(ge,caller,M,ir,(false,nil,ci),O,op))
   (P:=V293_read_bytes bt 0%Z V293_ready_table)(Q:=Atrue).
   - intros st H;change(0%Z)with(0+Z.of_nat 0)%Z.
     change(V293_ready_lookup 0)with(nth 0 V293_ready_table 0).
     eapply V293_read_bytes_load;[cbn;lia|cbn;lia|exact H].
   - unfold V293_helper_resource in Held;clear Ready;sep auto. }
 set(Res:=V293_helper_resource br bg bp bt bh t R oldhigh).
 assert(Current:forall s,s|=Res ->s|=CurTid t **Atrue).
 { intros st H;eapply V293_helper_resource_current;exact H. }
 assert(Body:forall b,fresh M b ->
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci),O,op)|=
    Amapsto(b,0%Z)Tint8 true Vundef **Res ->
  TaskSim(pc,(po,pi,ip))
   (curs(V293_OSSchedNew_body unmap group rows high y),
    (kenil,kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks))
   (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))
   ph Ch O V293_shared_li I Post t).
 { intros b Fresh Own;eapply V293_helper_body_TaskSim with(op:=op)(R:=R)(br:=br)(bg:=bg)(bp:=bp)(bt:=bt)(bh:=bh)(oldy:=Vundef)(oldhigh:=oldhigh).
   - exact Bind.
   - exact Good.
   - unfold V293_sched_read_env;repeat split;try assumption;rewrite map_get_set' by assumption;apply map_emp_get.
   - rewrite map_get_set' by exact YH;apply map_emp_get.
   - exact GH.
   - eapply V293_helper_fresh_byte_distinct;[exact Fresh|exact Lookup0].
   - eapply V293_helper_fresh_byte_distinct;[exact Fresh|exact Group].
   - eapply V293_helper_fresh_byte_distinct;[exact Fresh|exact Row0].
   - exact Own.
   - exact Tail. }
 set(body:=V293_OSSchedNew_body unmap group rows high y).
 set(k:=kcall f body caller ks).
 assert(Program:(pumerge po pi)f=Some(Tvoid,dnil,dcons y Tint8 dnil,body)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Inside:InOS(SKIP,(kenil,k))(pumerge po pi)).
 { unfold k;eapply V293_bound_call_inos;exact Bind. }
 assert(Local:forall le',satp(ge,le',M,ir,(false,nil,ci))O(CurLINV V293_shared_li t)).
 { intros le';eapply V293_pending_local with(op:=op);apply Current.
   eapply V293_helper_resource_lenv;[exact Good|exact Held]. }
 assert(Allocated:forall b,fresh M b ->
  (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci),O,op)|=
   Amapsto(b,0%Z)Tint8 true Vundef **Res).
 { intros b Fresh;eapply V293_tick_allocate_frame;[exact Fresh| ].
   eapply V293_helper_resource_lenv;[exact Good|exact Held]. }
 assert(AllocatedLocal:forall b,fresh M b ->
  satp(ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))O
   (CurLINV V293_shared_li t)).
 { intros b Fresh;eapply V293_pending_local with(op:=op).
   pose proof(Allocated b Fresh)as Own.
   apply astar_mono with(P':=Amapsto(b,0%Z)Tint8 true Vundef)(Q':=CurTid t **Atrue)in Own;
    [sep auto|intros st H;exact H|exact Current]. }
 assert(AllocatedEnd:forall b,fresh M b ->
  TaskSim(pc,(po,pi,ip))(curs(salloc nil dnil),(kenil,k))
   (ge,set(emp:env)y(b,Tint8),allocb M b 0%Z(typelen Tint8),ir,(false,nil,ci))
   ph Ch O V293_shared_li I Post t).
 { intros b Fresh;eapply V293_invariant_cstep_TaskSim;
    [ | | |apply AllocatedLocal;exact Fresh|apply Body;[exact Fresh|apply Allocated;exact Fresh]].
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ].
     assert(Next:cstep(pumerge po pi)(curs(salloc nil dnil),(kenil,k))
      (ge,set(emp:env)y(b,Tint8),Mall)(curs body,(kenil,k))(ge,set(emp:env)y(b,Tint8),Mall)).
     { unfold k;eapply stmt_step;[reflexivity|apply sallocend_step]. }
     split;[exact Next| ];intros Cf mf Other.
     destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption. }
 assert(Allocate:TaskSim(pc,(po,pi,ip))(curs(salloc nil(dcons y Tint8 dnil)),(kenil,k))
  (ge,(emp:env),M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_branching_cstep_TaskSim.
   - eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;destruct(memory_has_fresh_block Mall)as[b Fresh].
     exists(curs(salloc nil dnil),(kenil,k));
     exists(ge,set(emp:env)y(b,Tint8),allocb Mall b 0%Z(typelen Tint8)).
     eapply stmt_step;[reflexivity| ];eapply salloclv_step;[reflexivity|reflexivity| ].
     exists b;repeat split;try assumption;try reflexivity.
     intros[v E];rewrite map_emp_get in E;discriminate E.
   - intros Cf mf Step;destruct(V293_helper_byte_successor _ _ _ _ _ _ _ _ Step)
      as(b&Fresh&Absent&EC&EM);subst Cf mf.
     do 2 eexists;split;[reflexivity| ];split;
      [apply AllocatedLocal;exact Fresh|apply AllocatedEnd;exact Fresh]. }
 assert(Execute:TaskSim(pc,(po,pi,ip))(curs(sfexec f nil nil),(kenil,ks))
  (ge,caller,M,ir,(false,nil,ci))ph Ch O V293_shared_li I Post t).
 { eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Allocate].
   - eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
   - intros[x E];discriminate E.
   - intros Mf Mall Join;exists Mall;split;[exact Join| ];split.
     + eapply stmt_step;[reflexivity| ];eapply sfexec_step with(d1:=dnil)(d2:=dcons y Tint8 dnil);
       [reflexivity|reflexivity|exact Program|exact Logic.I|reflexivity].
     + intros;eapply V293_helper_exec_successor;[exact Program|eassumption]. }
 eapply V293_invariant_cstep_TaskSim;[ | | |apply Local|exact Execute].
 - eapply V293_context_inos;[exact Context|reflexivity|reflexivity].
 - intros[x E];discriminate E.
 - intros Mf Mall Join;exists Mall;split;[exact Join| ].
   assert(Next:cstep(pumerge po pi)(curs(scall f nil),(kenil,ks))(ge,caller,Mall)
    (curs(sfexec f nil nil),(kenil,ks))(ge,caller,Mall)).
   { eapply stmt_step;[reflexivity|apply snpcall_step]. }
   split;[exact Next| ];intros Cf mf Other.
   destruct(cstep_idmove_deter _ _ _ _ _ _ Next Other)as[EC EM];split;symmetry;assumption.
Qed.
