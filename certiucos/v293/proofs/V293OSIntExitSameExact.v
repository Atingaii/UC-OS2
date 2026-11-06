(* Exact resources through the real equal-priority interrupt exit body. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.

Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.

Section ExactReadyDispatch.
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
Variables current counter nesting lock : var.
Variables bcur bcounter bn bl : block.
Variable nc : nat.
Variable frame : asrt.
Definition V293_exit_ready_exact_pre nest locked old c : asrt :=
 V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop **
 (V293_prefix_frame table high target tp bp bo entries tasks
   (V293_guard_cell current bcur nc ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)frame) **
  (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)).
Let rest old c hv := frame **
 (V293_sched_exact_resource unmap group rows high bt bg br bh lo hi li tid hv **
  (V293_prefix_frame table high target tp bp bo entries tasks(V293_guard_cell current bcur nc ** Aemp) **
   (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c))).

Lemma V293_exit_ready_exact_reorder : forall nest locked old c,
 V293_exit_ready_exact_pre nest locked old c ==>
 EX hv : val, <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(rest old c hv).
Proof.
 intros nest locked old c s Hs.
 unfold V293_exit_ready_exact_pre,V293_sched_exact_pre,V293_prefix_frame in Hs.
 sep lift 2%nat in Hs. sep normal in Hs. destruct Hs as[hv Hs]. exists hv.
 unfold rest,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_ready_exact_restore : forall nest locked old c,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 (EX hv : val, <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(rest old c hv)) ==>
 V293_exit_ready_exact_pre nest locked old c.
Proof.
 intros nest locked old c Hlo Hhi Hr s[hv Hs].
 unfold V293_exit_ready_exact_pre,V293_sched_exact_pre. sep normal. exists hv.
 unfold rest,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_ready_exact_decrement : forall Spec sd I r ri nest locked old c,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nest<256 -> locked<256 ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 InfRules Spec sd li I r ri(V293_exit_ready_exact_pre nest locked old c)
 (V293_OSIntExit_decrement nesting)(V293_exit_ready_exact_pre(V293_exit_depth nest)locked old c)tid.
Proof.
 intros Spec sd I r ri nest locked old c Hlo Hhi Hr Hn Hl Env.
 eapply conseq_rule.
 - apply V293_exit_ready_exact_reorder.
 - apply V293_exit_ready_exact_restore;assumption.
 - apply ex_intro_rule. intro hv.
   eapply conseq_rule with(q:=<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)(rest old c hv)).
   + intros s Hs;exact Hs.
   + intros s Hs;exists hv;exact Hs.
   + eapply V293_OSIntExit_decrement_hoare;try eassumption.
     * intros s Hs. eapply V293_star_env_l;[exact Env|exact Hs].
     * unfold rest. apply V293_star_CurLINV_r. apply V293_star_CurLINV_l.
     apply V293_sched_exact_resource_local.
Qed.
Lemma V293_exit_ready_exact_guard_eval : forall nest locked old c s,
 nest<256 -> locked<256 ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 s |= V293_exit_ready_exact_pre nest locked old c ->
 (s |= Rv(V293_OSSched_zero nesting)@Tint32==Vint32(if Nat.eqb nest 0 then Int.one else Int.zero)) /\
 (s |= Rv(V293_OSSched_zero lock)@Tint32==Vint32(if Nat.eqb locked 0 then Int.one else Int.zero)).
Proof.
 intros nest locked old c s Hn Hl Env Hs.
 destruct(V293_exit_ready_exact_reorder nest locked old c s Hs)as[hv Owned].
 apply astar_l_aop'_elim in Owned as[_ Owned].
 assert(Env':forall st,st |= rest old c hv -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)).
 { intros st Hst. eapply V293_star_env_l;[exact Env|exact Hst]. }
 destruct(V293_exit_owned_eval _ _ _ _ _ _ _ s Hn Hl Env' Owned)as[_ [_ [_ [[N NT][L LT]]]]].
 split;split;[exact N|split;[exact NT|discriminate]|exact L|split;[exact LT|discriminate]].
Qed.

End ExactReadyDispatch.

Section ExactTail.
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
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.

Definition V293_OSSched_exact_tail_state c : asrt :=
  EX t : Modules.tid, [|V293_highest_ready tasks t|] **
    (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_guard_cell current bcur nc ** frame) **
        (V293_prefix_output tp bo (Vptr t) ** V293_counter_cell counter bcounter c))).

Lemma V293_exact_tail_reads : forall c,
 V293_OSSched_exact_tail_state c ==>
 V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter nc frame c.
Proof.
 intros c s [t H]. exists t.
 unfold V293_sched_exact_post,V293_sched_internal_post in *.
 eapply astar_mono;[intros st Hst;exact Hst| |exact H].
 apply astar_mono;[ |intros st Hst;exact Hst].
 apply astar_mono;[intros st Hst;exact Hst| ].
 apply astar_mono;[intros st Hst;exact Hst|apply V293_exact_prefix_read_resource].
Qed.
End ExactTail.

Section ExactExitContext.
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
Variables current counter nesting lock : var.
Variables bcur bcounter bn bl : block.
Variable nc : nat.
Variable frame : asrt.
Variable resourceI : Inv.
Variable held : bool.
Variable ir : isr.
Variable si : is.
Variable ci : cs.
Let context := V293_sched_ISR_context resourceI held ir si ci.
Let pre nest old c := V293_exit_ready_exact_pre unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter bn bl nc
 (context ** frame) nest 0 old c.
Let tail c := V293_OSSched_exact_tail_state unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter nc
 (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)(context ** frame)) c.

Theorem V293_OSIntExit_exact_context_same_dispatch : forall Spec sd RI r ri sched_id
 nest old c handoff (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<=1 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched_id=Some(V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li resourceI Hli,
  V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li resourceI Hli,(Tvoid,nil)) ->
 InfRules Spec sd li RI r ri (pre nest old c)
 (V293_OSIntExit_nesting_dispatch nesting lock
   (V293_exit_boundary_dispatch table high target current counter sched_id handoff))
 (tail c) tid.
Proof.
 intros Spec sd RI r ri sched_id nest old c handoff Hli
 Low High Ready Cur Nest Bitmap Table Frame Env Same Lookup.
 assert(Env':forall st,st |= context ** frame ->
  V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)).
 { eapply V293_star_env_r;exact Env. }
 assert(Zero:V293_exit_depth nest=0)by(unfold V293_exit_depth;lia).
 unfold V293_OSIntExit_nesting_dispatch.
 eapply seq_rule with(p':=pre 0 old c).
 - unfold pre. rewrite <-Zero at 2.
   apply V293_exit_ready_exact_decrement with(lock:=lock);try assumption;lia.
 - unfold V293_OSIntExit_guards.
   eapply V293_exit_known_if with(flag:=true).
   + intros st H. exact(proj1(V293_exit_ready_exact_guard_eval unmap group rows high
     bt bg br bh lo hi li tid aop table target tp bp bo entries tasks current counter
     nesting lock bcur bcounter bn bl nc (context ** frame) 0 0 old c st
     ltac:(lia) ltac:(lia) Env' H)).
   + eapply V293_exit_known_if with(flag:=true).
     * intros st H. exact(proj2(V293_exit_ready_exact_guard_eval unmap group rows high
       bt bg br bh lo hi li tid aop table target tp bp bo entries tasks current counter
       nesting lock bcur bcounter bn bl nc (context ** frame) 0 0 old c st
       ltac:(lia) ltac:(lia) Env' H)).
     * unfold V293_exit_boundary_dispatch. eapply seq_rule with(p':=tail c).
       -- eapply conseq_rule with
         (p:=(V293_sched_exact_pre unmap group rows high bt bg br bh lo hi li tid aop ** context) **
           (V293_prefix_frame table high target tp bp bo entries tasks
             (V293_guard_cell current bcur nc **
               (V293_counter_cell counter bcounter c **
                V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)frame)) **
            V293_prefix_output tp bo old))
         (q:=EX t:Modules.tid,[|V293_highest_ready tasks t|] **
           (V293_sched_exact_post unmap group rows high bt bg br bh lo hi li tid aop None **
             (V293_prefix_frame table high target tp bp bo entries tasks
               (context ** (V293_guard_cell current bcur nc **
                 (V293_counter_cell counter bcounter c **
                  V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)frame))) **
              V293_prefix_output tp bo(Vptr t)))).
          ++ unfold pre,V293_exit_ready_exact_pre,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells.
             cbn[V293_rdy_raw_cells]. intros st H;clear -H;sep auto.
          ++ unfold tail,V293_OSSched_exact_tail_state,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells.
             cbn[V293_rdy_raw_cells]. intros st[t H];exists t;clear -H;sep auto.
          ++ apply V293_OSSched_ISR_exact_prefix with(Hli:=Hli);try assumption.
             repeat split;try apply V293_guard_cell_good;try apply V293_counter_cell_good.
             unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFrm];tauto.
       -- eapply V293_exit_known_if with(flag:=false);[ |apply skip_rule].
          intros st H. destruct(V293_OSSched_priority_comparison unmap group rows high bt bg br bh lo hi li tid aop
           table target tp bp bo entries tasks current counter bcur bcounter nc
           (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)(context ** frame)) c st
           Low High Ready Cur (V293_exact_tail_reads unmap group rows high bt bg br bh lo hi li tid aop
           table target tp bp bo entries tasks current counter bcur bcounter nc
           (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)(context ** frame)) c st H))as[V T].
          rewrite Same,Nat.eqb_refl in V. split;[exact V|split;[exact T|discriminate]].
Qed.
End ExactExitContext.

Section SameExact.
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
Definition V293_exit_same_exact_core nest hv out c : asrt :=
 (V293_guard_cell running brun 1 **
  (((V293_sched_globals unmap group rows high bt bg br bh **
     V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi)) ** p_local li tid nil) **
   (PV(bh,Int.zero) @ Tint8 |-> hv **
    (V293_prefix_frame table high target tp bp bo entries tasks
      (V293_guard_cell current bcur nc **
       V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)frame) **
     (V293_prefix_output tp bo out ** V293_counter_cell counter bcounter c))))).
Definition V293_exit_same_exact_data nest hv out c value : asrt :=
 V293_time_cell true saved bs value ** V293_exit_same_exact_core nest hv out c.
Definition V293_exit_same_exact_result c value : asrt :=
 EX t:Modules.tid,[|V293_highest_ready tasks t|] **
 V293_exit_same_exact_data 0 (V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))
  (Vptr t) c value.
Lemma V293_exit_same_exact_data_good : forall nest hv out c value,
 GoodLInvAsrt li -> GoodFrm frame -> GoodFrm(V293_exit_same_exact_data nest hv out c value).
Proof.
 intros nest hv out c value Hli GF.
 assert(B:forall b off vals,GoodFrm(V293_read_bytes b off vals)).
 { intros b off vals. revert off;induction vals;cbn;auto. }
 unfold V293_exit_same_exact_data,V293_exit_same_exact_core.
 split;[apply V293_time_cell_good| ].
 split;[apply V293_guard_cell_good| ].
 split.
 - split;[split|apply V293_exact_local_frame;exact Hli].
   + unfold V293_sched_globals;cbn[GoodFrm];tauto.
   + unfold V293_sched_inputs;repeat split;try apply B;exact Logic.I.
 - split;[exact Logic.I| ]. split.
   + apply V293_prefix_frame_good. split;[apply V293_guard_cell_good| ].
     unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFrm];tauto.
   + split;[exact Logic.I|apply V293_counter_cell_good].
Qed.
Lemma V293_exit_same_exact_result_good : forall c value,
 GoodLInvAsrt li -> GoodFrm frame -> GoodFrm(V293_exit_same_exact_result c value).
Proof.
 intros. unfold V293_exit_same_exact_result. intro t;split;[exact Logic.I| ].
 apply V293_exit_same_exact_data_good;assumption.
Qed.
Lemma V293_exit_same_exact_data_local : forall nest hv out c value,
 V293_exit_same_exact_data nest hv out c value ==> CurLINV li tid.
Proof.
 intros nest hv out c value s H.
 assert(C:s |= p_local li tid nil ** Atrue).
 { unfold V293_exit_same_exact_data,V293_exit_same_exact_core in H;clear -H;sep auto. }
 eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
Qed.
Lemma V293_exit_same_exact_result_local : forall c value,
 V293_exit_same_exact_result c value ==> CurLINV li tid.
Proof.
 intros c value s[t H]. eapply V293_star_CurLINV_r;[ |exact H].
 apply V293_exit_same_exact_data_local.
Qed.

(* Internally discharge the actual dispatch premise for its exact context. *)
Lemma V293_exit_same_exact_middle : forall Spec sd I r ri ir si ci held sched nest hv out c value handoff
 (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<=1 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** (V293_exit_same_exact_data nest hv out c value ** V293_sched_ISR_context I held ir si ci))
 (V293_OSIntExit_nesting_dispatch nesting lock
  (V293_exit_boundary_dispatch table high target current counter sched handoff))
 (<||aop||> ** (V293_exit_same_exact_result c value ** V293_sched_ISR_context I held ir si ci)) tid.
Proof.
 intros Spec sd I r ri ir si ci held sched nest hv out c value handoff Hli
 Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 eapply conseq_rule with
 (p:=V293_exit_ready_exact_pre unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter bn bl nc
  (V293_sched_ISR_context I held ir si ci **
   (V293_time_cell true saved bs value ** (V293_guard_cell running brun 1 ** frame))) nest 0 out c)
 (q:=V293_OSSched_exact_tail_state unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc
  (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)
   (V293_sched_ISR_context I held ir si ci **
    (V293_time_cell true saved bs value ** (V293_guard_cell running brun 1 ** frame)))) c).
 - unfold V293_exit_same_exact_data,V293_exit_same_exact_core,V293_exit_ready_exact_pre,V293_sched_exact_pre,
   V293_sched_exact_resource,V293_prefix_frame,V293_sched_ISR_context,
   V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells]. intros s H. clear -H Low High Ready;sep auto.
 - unfold V293_exit_same_exact_result,V293_exit_same_exact_data,V293_exit_same_exact_core,V293_OSSched_exact_tail_state,
   V293_sched_exact_post,V293_sched_exact_resource,V293_prefix_frame,
   V293_exit_cells,V293_interrupt_cells.
   cbn[V293_rdy_raw_cells]. intros s[t H]. clear -H;sep auto.
 - apply V293_OSIntExit_exact_context_same_dispatch with(Hli:=Hli);try assumption.
   + split;[apply V293_time_cell_good|split;[apply V293_guard_cell_good|exact GF]].
   + repeat apply V293_star_env_r;exact Env.
Qed.

Theorem V293_OSIntExit_same_exact_critical : forall Spec sd I r ri enabled ir si ci sched nest hv out c value handoff
 (Hli:GoodLInvAsrt li),
 (gettopis si<=INUM)%nat -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<=1 -> V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
 GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_exact_data nest hv out c value)
 (sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock
  (V293_exit_boundary_dispatch table high target current counter sched handoff))(sprim excrit)))
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_exact_result c value) tid.
Proof.
 intros Spec sd I r ri enabled ir si ci sched nest hv out c value handoff Hli
 Bound Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 assert(GP:GoodFrm(V293_exit_same_exact_data nest hv out c value))by(apply V293_exit_same_exact_data_good;assumption).
 assert(GQ:GoodFrm(V293_exit_same_exact_result c value))by(apply V293_exit_same_exact_result_good;assumption).
 destruct enabled.
 - eapply seq_rule.
   + eapply conseq_rule with
     (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
       V293_exit_same_exact_data nest hv out c value)
     (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
       V293_exit_same_exact_data nest hv out c value).
     * intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
       pose proof(V293_time_topis si Atrue s S)as Top.
       apply astar_l_atopis_elim in Top as[Top _].
       pose proof(@astar_l_atopis_intro s (gettopis si) _ H Top)as HT.
       clear H;rename HT into H;sep auto.
     * intros s H;exact H.
     * apply encrit1_rule;exact GP.
   + eapply seq_rule.
     * eapply conseq_rule with
       (p:=<||aop||> ** (V293_exit_same_exact_data nest hv out c value **
         V293_sched_ISR_context I true ir si (true::ci)))
       (q:=<||aop||> ** (V293_exit_same_exact_result c value **
         V293_sched_ISR_context I true ir si (true::ci))).
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- apply V293_exit_same_exact_middle with(Hli:=Hli);assumption.
     * eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
         V293_exit_same_exact_result c value)
       (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_exit_same_exact_result c value).
       -- intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
          pose proof(V293_time_topis si Atrue s S)as Top.
          apply astar_l_atopis_elim in Top as[Top _].
          pose proof(@astar_l_atopis_intro s (gettopis si) _ H Top)as HT.
          clear H;rename HT into H;sep auto.
       -- intros s H;exact H.
       -- apply excrit1_rule;try assumption;apply V293_exit_same_exact_result_local.
 - eapply seq_rule.
   + apply encrit2_rule;exact GP.
   + eapply seq_rule.
     * eapply conseq_rule with
       (p:=<||aop||> ** (V293_exit_same_exact_data nest hv out c value **
         V293_sched_ISR_context I false ir si (false::ci)))
       (q:=<||aop||> ** (V293_exit_same_exact_result c value **
         V293_sched_ISR_context I false ir si (false::ci))).
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- unfold V293_sched_ISR_context;intros s H;sep auto.
       -- apply V293_exit_same_exact_middle with(Hli:=Hli);assumption.
     * eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,false,si,false::ci] ** V293_exit_same_exact_result c value).
       -- intros s H;sep auto.
       -- intros s H;exact H.
       -- apply excrit2_rule;exact GQ.
Qed.

(* Stable full-body interface: there is no assumed body/callee proof. *)
Theorem V293_OSIntExit_same_exact_priority_body : forall Spec sd I enabled ir si ci sched nest hv out c old handoff
 (Hli:GoodLInvAsrt li),
 (gettopis si<=INUM)%nat -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<=1 -> V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
 GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched=Some(V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 InfRules Spec sd li I
 (fun result=>[|result=None|] **
  (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_exact_result c(Vint32 Int.zero))) Afalse
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_exact_data nest hv out c old)
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff)
 Afalse tid.
Proof.
 intros Spec sd I enabled ir si ci sched nest hv out c old handoff Hli
 Bound Low High Ready Cur Nest Bitmap Table GF Env Same Lookup.
 unfold V293_exit_boundary_body.
 eapply seq_rule with(p':=<||aop||> ** OS[ir,enabled,si,ci] **
  V293_exit_same_exact_data nest hv out c(Vint32 Int.zero)).
 - eapply conseq_rule;[ | |apply (V293_time_zero Spec sd li I _ _ tid aop
    (V293_exit_same_exact_core nest hv out c ** OS[ir,enabled,si,ci]) saved bs old)].
   + unfold V293_exit_same_exact_data;intros s H;sep auto.
   + unfold V293_exit_same_exact_data;intros s H;sep auto.
   + intros s H. assert(C:s |= p_local li tid nil ** Atrue).
     { unfold V293_exit_same_exact_core in H;clear -H;sep auto. }
     eapply V293_star_CurLINV_l;[apply V293_exact_local_weakens|exact C].
 - eapply seq_rule with(p':=<||aop||> ** OS[ir,enabled,si,ci] ** V293_exit_same_exact_result c(Vint32 Int.zero)).
   + eapply V293_tick_known_ift_hoare with(flag:=true).
     * intros s H. assert(G:s |= V293_guard_cell running brun 1 ** Atrue).
       { unfold V293_exit_same_exact_data,V293_exit_same_exact_core in H;clear -H;sep auto. }
       destruct(V293_exit_running_eval running brun 1 Atrue s ltac:(lia) G)as[V T].
       split;[exact V|split;[exact T|discriminate]].
     * apply V293_OSIntExit_same_exact_critical with(Hli:=Hli);assumption.
   + apply ret_rule. intros s H. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
End SameExact.
