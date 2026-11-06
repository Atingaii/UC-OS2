(* Full normalized same-priority exit path. The scheduler is really called;
   only the unequal-priority handoff is unreachable under this contract. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_local_inv_frame : forall p, GoodLocalInvAsrt p -> GoodFrm p.
Proof.
 induction p;cbn;intros HG;try contradiction;try exact Logic.I;
 try (destruct HG;split;auto);auto.
Qed.
Lemma V293_current_inv_frame : forall li tid,
 GoodLInvAsrt li -> GoodFrm(CurLINV li tid).
Proof.
 intros li tid H. unfold CurLINV,CurTid,LINV,Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFrm]. intro lg. repeat split;try exact Logic.I.
 apply V293_local_inv_frame;exact(proj1(H tid lg)).
Qed.

(* The ordinary data is insensitive to IE/ISR/stacks; it owns no OS context. *)
Section SamePriority.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable li : LocalInv.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variables current counter running nesting lock saved : var.
Variables bcur bcounter brun bn bl bs : block.
Variable nc : nat.
Variable frame : asrt.
Definition V293_exit_same_core nest hv out c : asrt :=
 (V293_guard_cell running brun 1 **
  (((V293_sched_globals unmap group rows high bt bg br bh **
     V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi)) ** CurLINV li tid) **
   (PV(bh,Int.zero) @ Tint8 |-> hv **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc **
       V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)frame) **
     (V293_prefix_output tp bo out ** V293_counter_cell counter bcounter c))))).
Definition V293_exit_same_data nest hv out c value : asrt :=
 V293_time_cell true saved bs value ** V293_exit_same_core nest hv out c.
Definition V293_exit_same_result c value : asrt :=
 EX t:Modules.tid,[|V293_highest_ready tasks t|] **
 V293_exit_same_data 0 (V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))
  (Vptr t) c value.
Lemma V293_exit_same_data_good : forall nest hv out c value,
 GoodLInvAsrt li -> GoodFrm frame -> GoodFrm(V293_exit_same_data nest hv out c value).
Proof.
 intros nest hv out c value Hli GF.
 assert(B:forall b off vals,GoodFrm(V293_read_bytes b off vals)).
 { intros b off vals. revert off;induction vals;cbn;auto. }
 unfold V293_exit_same_data,V293_exit_same_core.
 split;[apply V293_time_cell_good| ].
 split;[apply V293_guard_cell_good| ].
 split.
 - split;[split|apply V293_current_inv_frame;exact Hli].
   + unfold V293_sched_globals;cbn[GoodFrm];tauto.
   + unfold V293_sched_inputs;repeat split;try apply B;exact Logic.I.
 - split;[exact Logic.I| ]. split.
   + apply V293_prefix_frame_good. split;[apply V293_guard_cell_good| ].
     unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFrm];tauto.
   + split;[exact Logic.I|apply V293_counter_cell_good].
Qed.
Lemma V293_exit_same_result_good : forall c value,
 GoodLInvAsrt li -> GoodFrm frame -> GoodFrm(V293_exit_same_result c value).
Proof.
 intros. unfold V293_exit_same_result. intro t;split;[exact Logic.I| ].
 apply V293_exit_same_data_good;assumption.
Qed.
Lemma V293_exit_same_data_local : forall nest hv out c value,
 V293_exit_same_data nest hv out c value ==> CurLINV li tid.
Proof.
 intros nest hv out c value s H.
 assert(C:s |= CurLINV li tid ** Atrue).
 { unfold V293_exit_same_data,V293_exit_same_core in H;clear -H;sep auto. }
 eapply V293_star_CurLINV_l;[ |exact C]. intros st Hst;exact Hst.
Qed.
Lemma V293_exit_same_result_local : forall c value,
 V293_exit_same_result c value ==> CurLINV li tid.
Proof.
 intros c value s[t H]. eapply V293_star_CurLINV_r;[ |exact H].
 apply V293_exit_same_data_local.
Qed.

(* Internally discharge the actual dispatch premise for its exact context. *)
Lemma V293_exit_same_middle : forall Spec sd I r ri ir si ci held sched nest hv out c value handoff
 (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<=1 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** (V293_exit_same_data nest hv out c value ** V293_sched_ISR_context I held ir si ci))
 (V293_OSIntExit_nesting_dispatch nesting lock
  (V293_exit_boundary_dispatch table high target current counter sched handoff))
 (<||aop||> ** (V293_exit_same_result c value ** V293_sched_ISR_context I held ir si ci)) tid.
Proof.
 intros Spec sd I r ri ir si ci held sched nest hv out c value handoff Hli
 Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 eapply conseq_rule with
 (p:=V293_exit_ready_pre unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter bn bl nc
  (V293_sched_ISR_context I held ir si ci **
   (V293_time_cell true saved bs value ** (V293_guard_cell running brun 1 ** frame))) nest 0 out c)
 (q:=V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc
  (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)
   (V293_sched_ISR_context I held ir si ci **
    (V293_time_cell true saved bs value ** (V293_guard_cell running brun 1 ** frame)))) c).
 - unfold V293_exit_same_data,V293_exit_same_core,V293_exit_ready_pre,V293_sched_internal_pre,
   V293_sched_internal_resource,V293_prefix_frame,V293_sched_ISR_context,
   V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells]. intros s H. clear -H Low High Ready;sep auto.
 - unfold V293_exit_same_result,V293_exit_same_data,V293_exit_same_core,V293_OSSched_tail_state,
   V293_sched_internal_post,V293_sched_internal_resource,V293_prefix_frame,
   V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells]. intros s[t H]. clear -H;sep auto.
 - apply V293_OSIntExit_context_same_dispatch with(Hli:=Hli);try assumption.
   + split;[apply V293_time_cell_good|split;[apply V293_guard_cell_good|exact GF]].
   + repeat apply V293_star_env_r;exact Env.
Qed.

Theorem V293_OSIntExit_same_critical : forall Spec sd I r ri enabled ir si ci sched nest hv out c value handoff
 (Hli:GoodLInvAsrt li),
 (gettopis si<=INUM)%nat -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<=1 -> V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
 GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_data nest hv out c value)
 (sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock
  (V293_exit_boundary_dispatch table high target current counter sched handoff))(sprim excrit)))
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_result c value) tid.
Proof.
 intros Spec sd I r ri enabled ir si ci sched nest hv out c value handoff Hli
 Bound Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 assert(GP:GoodFrm(V293_exit_same_data nest hv out c value))by(apply V293_exit_same_data_good;assumption).
 assert(GQ:GoodFrm(V293_exit_same_result c value))by(apply V293_exit_same_result_good;assumption).
 destruct enabled.
 - eapply seq_rule.
   + eapply conseq_rule with
     (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
       V293_exit_same_data nest hv out c value)
     (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
       V293_exit_same_data nest hv out c value).
     * intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
       pose proof(V293_time_topis si Atrue s S)as Top.
       apply astar_l_atopis_elim in Top as[Top _].
       pose proof(@astar_l_atopis_intro s (gettopis si) _ H Top)as HT.
       clear H;rename HT into H;sep auto.
     * intros s H;exact H.
     * apply encrit1_rule;exact GP.
   + eapply seq_rule.
     * eapply conseq_rule with
       (p:=<||aop||> ** (V293_exit_same_data nest hv out c value **
         V293_sched_ISR_context I true ir si (true::ci)))
       (q:=<||aop||> ** (V293_exit_same_result c value **
         V293_sched_ISR_context I true ir si (true::ci))).
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- apply V293_exit_same_middle with(Hli:=Hli);assumption.
     * eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
         V293_exit_same_result c value)
       (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_exit_same_result c value).
       -- intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
          pose proof(V293_time_topis si Atrue s S)as Top.
          apply astar_l_atopis_elim in Top as[Top _].
          pose proof(@astar_l_atopis_intro s (gettopis si) _ H Top)as HT.
          clear H;rename HT into H;sep auto.
       -- intros s H;exact H.
       -- apply excrit1_rule;try assumption;apply V293_exit_same_result_local.
 - eapply seq_rule.
   + apply encrit2_rule;exact GP.
   + eapply seq_rule.
     * eapply conseq_rule with
       (p:=<||aop||> ** (V293_exit_same_data nest hv out c value **
         V293_sched_ISR_context I false ir si (false::ci)))
       (q:=<||aop||> ** (V293_exit_same_result c value **
         V293_sched_ISR_context I false ir si (false::ci))).
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- apply V293_exit_same_middle with(Hli:=Hli);assumption.
     * eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,false,si,false::ci] ** V293_exit_same_result c value).
       -- intros s H;sep auto.
       -- intros s H;exact H.
       -- apply excrit2_rule;exact GQ.
Qed.

(* Stable full-body interface: there is no assumed body/callee proof. *)
Theorem V293_OSIntExit_same_priority_body : forall Spec sd I enabled ir si ci sched nest hv out c old handoff
 (Hli:GoodLInvAsrt li),
 (gettopis si<=INUM)%nat -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<=1 -> V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
 GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I
 (fun result=>[|result=None|] **
  (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_result c(Vint32 Int.zero))) Afalse
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_data nest hv out c old)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff)
 Afalse tid.
Proof.
 intros Spec sd I enabled ir si ci sched nest hv out c old handoff Hli
 Bound Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 unfold V293_exit_boundary_body.
 eapply seq_rule with(p':=<||aop||> ** OS[ir,enabled,si,ci] **
  V293_exit_same_data nest hv out c(Vint32 Int.zero)).
 - eapply conseq_rule;[ | |apply (V293_time_zero Spec sd li I _ _ tid aop
    (V293_exit_same_core nest hv out c ** OS[ir,enabled,si,ci]) saved bs old)].
   + unfold V293_exit_same_data;intros s H;sep auto.
   + unfold V293_exit_same_data;intros s H;sep auto.
   + intros s H. assert(C:s |= CurLINV li tid ** Atrue).
     { unfold V293_exit_same_core in H;clear -H;sep auto. }
     eapply V293_star_CurLINV_l;[ |exact C]. intros st Hst;exact Hst.
 - eapply seq_rule with(p':=<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_result c(Vint32 Int.zero)).
   + eapply V293_tick_known_ift_hoare with(flag:=true).
     * intros s H. assert(G:s |= V293_guard_cell running brun 1 ** Atrue).
       { unfold V293_exit_same_data,V293_exit_same_core in H;clear -H;sep auto. }
       destruct(V293_exit_running_eval running brun 1 Atrue s ltac:(lia) G)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * apply V293_OSIntExit_same_critical with(Hli:=Hli);assumption.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
End SamePriority.
