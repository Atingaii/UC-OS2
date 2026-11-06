Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Local Open Scope nat_scope.

Section ExitDispatch.
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

Let tail := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter nc frame.

(* The explicit else and empty trace belong to the fixed source. Only the
   actual interrupt-switch call remains open, with the updated resources. *)
Theorem V293_OSIntExit_dispatch_tail : forall Spec sd I r ri c int_switch q,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 ->
 (V293_ready_select lo hi (V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri (tail(Int.add c Int.one))(scall int_switch nil)q tid) ->
 InfRules Spec sd li I r ri (tail c)
  (sif (V293_OSSched_different high current)
    (sseq(V293_OSSched_increment counter)(sseq(sskip None)(scall int_switch nil)))(sskip None))
  (if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then tail c else q)tid.
Proof.
 intros Spec sd I r ri c int_switch q Hlo Hhi Hr Hnc Call.
 eapply V293_exit_known_if with(flag:=negb(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc)).
 - intros s Hs. destruct(V293_OSSched_priority_comparison unmap group rows high bt bg br bh lo hi li tid aop
     table target tp bp bo entries tasks current counter bcur bcounter nc frame c s Hlo Hhi Hr Hnc Hs)as[V T].
   destruct(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc);
    split;[exact V|split;[exact T|discriminate]|exact V|split;[exact T|discriminate]].
 - destruct(Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc)eqn:E;[apply skip_rule| ].
   eapply seq_rule with(p':=tail(Int.add c Int.one)).
   + apply V293_OSSched_tail_increment.
   + eapply seq_rule;[apply skip_rule| ]. apply Call. apply Nat.eqb_neq;exact E.
Qed.

Theorem V293_OSIntExit_dispatch_hoare : forall Spec sd I r ri sched_id old c int_switch q
    (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  (V293_ready_select lo hi (V293_ready_group lo hi) <> nc ->
    InfRules Spec sd li I r ri (tail (Int.add c Int.one)) (scall int_switch nil) q tid) ->
  InfRules Spec sd li I r ri
    (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_guard_cell current bcur nc ** frame) **
        (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)))
    (V293_OSIntExit_dispatch table high target current counter sched_id int_switch)
    (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then tail c else q) tid.
Proof.
  intros Spec sd I r ri sched_id old c int_switch q Hli Hlo Hhi Hr Hnc Hb Htable Hframe Hspec Hsuffix.
  unfold V293_OSIntExit_dispatch. eapply seq_rule with (p' := tail c).
  - eapply conseq_rule with
      (p := V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) **
          V293_prefix_output tp bo old))
      (q := EX t : Modules.tid, [|V293_highest_ready tasks t|] **
        (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
          (V293_prefix_frame table high target tp bp bo entries tasks
            (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) **
            V293_prefix_output tp bo (Vptr t)))).
    + unfold V293_prefix_frame. intros s Hs. sep auto.
    + unfold tail, V293_OSSched_tail_state, V293_prefix_frame. intros s [t Hs]. exists t. sep auto.
    + apply V293_OSSched_unlocked_prefix_hoare with (Hli := Hli); try assumption.
      repeat split; try apply V293_guard_cell_good; try apply V293_counter_cell_good; exact Hframe.
  - apply V293_OSIntExit_dispatch_tail; assumption.
Qed.
End ExitDispatch.

(* Writable depth/lock bytes coexist with all scheduler inputs, task-table
   ownership, target output, current priority and the counter. *)
Section ExitCountDispatch.
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
Definition V293_exit_ready_pre nest locked old c : asrt :=
 V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
 (V293_prefix_frame table high target tp bp bo entries tasks
   (V293_guard_cell current bcur nc ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)frame) **
  (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c)).
Let rest old c hv := frame **
 (V293_sched_internal_resource unmap group rows high bt bg br bh lo hi li tid hv **
  (V293_prefix_frame table high target tp bp bo entries tasks(V293_guard_cell current bcur nc ** Aemp) **
   (V293_prefix_output tp bo old ** V293_counter_cell counter bcounter c))).

Lemma V293_exit_ready_reorder : forall nest locked old c,
 V293_exit_ready_pre nest locked old c ==>
 EX hv : val, <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(rest old c hv).
Proof.
 intros nest locked old c s Hs.
 unfold V293_exit_ready_pre,V293_sched_internal_pre,V293_prefix_frame in Hs.
 sep lift 2%nat in Hs. sep normal in Hs. destruct Hs as[hv Hs]. exists hv.
 unfold rest,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_ready_restore : forall nest locked old c,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 (EX hv : val, <||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(rest old c hv)) ==>
 V293_exit_ready_pre nest locked old c.
Proof.
 intros nest locked old c Hlo Hhi Hr s[hv Hs].
 unfold V293_exit_ready_pre,V293_sched_internal_pre. sep normal. exists hv.
 unfold rest,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells in *.
 cbn[V293_rdy_raw_cells]in *. sep auto.
Qed.
Lemma V293_exit_ready_decrement : forall Spec sd I r ri nest locked old c,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nest<256 -> locked<256 ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 InfRules Spec sd li I r ri(V293_exit_ready_pre nest locked old c)
 (V293_OSIntExit_decrement nesting)(V293_exit_ready_pre(V293_exit_depth nest)locked old c)tid.
Proof.
 intros Spec sd I r ri nest locked old c Hlo Hhi Hr Hn Hl Env.
 eapply conseq_rule.
 - apply V293_exit_ready_reorder.
 - apply V293_exit_ready_restore;assumption.
 - apply ex_intro_rule. intro hv.
   eapply conseq_rule with(q:=<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)(rest old c hv)).
   + intros s Hs;exact Hs.
   + intros s Hs;exists hv;exact Hs.
   + eapply V293_OSIntExit_decrement_hoare;try eassumption.
     * intros s Hs. eapply V293_star_env_l;[exact Env|exact Hs].
     * unfold rest. apply V293_star_CurLINV_r. apply V293_star_CurLINV_l.
     apply V293_sched_internal_resource_CurLINV.
Qed.
Lemma V293_exit_ready_guard_eval : forall nest locked old c s,
 nest<256 -> locked<256 ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 s |= V293_exit_ready_pre nest locked old c ->
 (s |= Rv(V293_OSSched_zero nesting)@Tint32==Vint32(if Nat.eqb nest 0 then Int.one else Int.zero)) /\
 (s |= Rv(V293_OSSched_zero lock)@Tint32==Vint32(if Nat.eqb locked 0 then Int.one else Int.zero)).
Proof.
 intros nest locked old c s Hn Hl Env Hs.
 destruct(V293_exit_ready_reorder nest locked old c s Hs)as[hv Owned].
 apply astar_l_aop'_elim in Owned as[_ Owned].
 assert(Env':forall st,st |= rest old c hv -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)).
 { intros st Hst. eapply V293_star_env_l;[exact Env|exact Hst]. }
 destruct(V293_exit_owned_eval _ _ _ _ _ _ _ s Hn Hl Env' Owned)as[_ [_ [_ [[N NT][L LT]]]]].
 split;split;[exact N|split;[exact NT|discriminate]|exact L|split;[exact LT|discriminate]].
Qed.

Theorem V293_OSIntExit_ready_disabled : forall Spec sd I r ri nest locked old c dispatch,
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nest<256 -> locked<256 ->
 (2<=nest \/ 0<locked) ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 InfRules Spec sd li I r ri(V293_exit_ready_pre nest locked old c)
 (V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (V293_exit_ready_pre(V293_exit_depth nest)locked old c)tid.
Proof.
 intros Spec sd I r ri nest locked old c dispatch Hlo Hhi Hr Hn Hl Off Env.
 eapply conseq_rule.
 - apply V293_exit_ready_reorder.
 - apply V293_exit_ready_restore;assumption.
 - apply ex_intro_rule. intro hv.
   eapply conseq_rule with(q:=<||aop||> ** V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)(rest old c hv)).
   + intros s Hs;exact Hs.
   + intros s Hs;exists hv;exact Hs.
   + eapply V293_OSIntExit_disabled_hoare;try eassumption.
     * intros s Hs. eapply V293_star_env_l;[exact Env|exact Hs].
     * unfold rest. apply V293_star_CurLINV_r. apply V293_star_CurLINV_l.
     apply V293_sched_internal_resource_CurLINV.
Qed.

Theorem V293_OSIntExit_ready_dispatch : forall Spec sd I r ri sched_id int_switch old c nest locked q
 (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<256 -> locked<256 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 let posttail := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc
  (V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)frame) in
 (V293_exit_depth nest=0 -> locked=0 -> V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri(posttail(Int.add c Int.one))(scall int_switch nil)q tid) ->
 InfRules Spec sd li I r ri(V293_exit_ready_pre nest locked old c)
 (V293_OSIntExit_nesting_dispatch nesting lock
   (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
 (if V293_exit_enabled nest locked then
    if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then posttail c else q
  else V293_exit_ready_pre(V293_exit_depth nest)locked old c)tid.
Proof.
 intros Spec sd I r ri sched_id int_switch old c nest locked q Hli Hlo Hhi Hr Hnc Hn Hl Hb Htable Hframe Env Hspec posttail Call.
 unfold V293_OSIntExit_nesting_dispatch.
 eapply seq_rule with(p':=V293_exit_ready_pre(V293_exit_depth nest)locked old c).
 - apply V293_exit_ready_decrement;assumption.
 - assert(B:V293_exit_depth nest<256)by(unfold V293_exit_depth;lia).
   pose proof(V293_exit_ready_guard_eval(V293_exit_depth nest)locked old c)as Eval.
   unfold V293_OSIntExit_guards,V293_exit_enabled.
   eapply V293_exit_known_if with(flag:=Nat.eqb(V293_exit_depth nest)0).
   + intros s Hs. exact(proj1(Eval s B Hl Env Hs)).
   + destruct(Nat.eqb(V293_exit_depth nest)0)eqn:En;[ |apply skip_rule].
     eapply V293_exit_known_if with(flag:=Nat.eqb locked 0).
     * intros s Hs. exact(proj2(Eval s B Hl Env Hs)).
     * destruct(Nat.eqb locked 0)eqn:El;[ |apply skip_rule].
       apply V293_OSIntExit_dispatch_hoare with(Hli:=Hli);try assumption.
       -- unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFrm]. tauto.
       -- apply Call;apply Nat.eqb_eq;assumption.
Qed.
Theorem V293_OSIntExit_ready_dispatch_semantics : forall Spec sd I r ri sched_id int_switch old c nest locked q
 (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<256 -> locked<256 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil)) ->
 let posttail := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
  table target tp bp bo entries tasks current counter bcur bcounter nc
  (V293_rdy_raw_cells(V293_exit_cells bn bl(V293_exit_depth nest)locked)frame) in
 (V293_exit_depth nest=0 -> locked=0 -> V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I r ri(posttail(Int.add c Int.one))(scall int_switch nil)q tid) ->
 simulation.RuleSem Spec sd li I r ri(V293_exit_ready_pre nest locked old c)
 (V293_OSIntExit_nesting_dispatch nesting lock
   (V293_OSIntExit_dispatch table high target current counter sched_id int_switch))
 (if V293_exit_enabled nest locked then
    if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then posttail c else q
  else V293_exit_ready_pre(V293_exit_depth nest)locked old c)tid.
Proof. intros. apply RuleSound. eapply V293_OSIntExit_ready_dispatch;eassumption. Qed.
End ExitCountDispatch.
