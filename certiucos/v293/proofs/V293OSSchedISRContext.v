(* The real scheduler body preserves caller ISR state and acquired resources.
   OS resources belong inside its function contract, never in GoodFrm. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_sched_ISR_context (I:Inv) (held:bool) ir si ci : asrt :=
 OS[ir,false,si,ci] ** (if held then invlth_isr I 0 (gettopis si) else Aemp).
Lemma V293_sched_ISR_context_good : forall I held ir si ci,
 GoodFunAsrt(V293_sched_ISR_context I held ir si ci).
Proof.
 intros Inv held ir si ci. unfold V293_sched_ISR_context.
 split;[cbn[GoodFunAsrt];repeat split;exact Logic.I| ].
 destruct held;[unfold invlth_isr;apply V293_starinv_function_assertion|exact Logic.I].
Qed.
Lemma V293_sched_ISR_context_not_frame : forall I held ir si ci,
 ~GoodFrm(V293_sched_ISR_context I held ir si ci).
Proof. intros Inv held ir si ci H;cbn[V293_sched_ISR_context GoodFrm]in H;tauto. Qed.

Definition V293_ISR_sched_args (lg:list logicvar) :
 option(nat*nat*spec_code*bool*isr*is*cs) :=
 match lg with
 | cons (logic_lv (cons (Vint32 low) (cons (Vint32 upper) nil)))
    (cons (logic_code aop) (cons (logic_ie held)
    (cons (logic_isr ir) (cons (logic_is si) (cons (logic_cs ci) nil))))) =>
   Some(Z.to_nat(Int.unsigned low),Z.to_nat(Int.unsigned upper),aop,held,ir,si,ci)
 | _ => None
 end.
Definition V293_ISR_sched_pre unmap group rows high bt bg br bh li I tid lg :=
  match V293_ISR_sched_args lg with
  | Some (lo, hi, aop, held, ir, si, ci) =>
      V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
        V293_sched_ISR_context I held ir si ci
  | None => Afalse
  end.
Definition V293_ISR_sched_post unmap group rows high bt bg br bh li I tid lg result :=
  match V293_ISR_sched_args lg with
  | Some (lo, hi, aop, held, ir, si, ci) =>
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci
  | None => Afalse
  end.
Definition V293_ISR_sched_fpre (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpre.
Proof.
  intros vl lg tid. refine (@mkfunasrt
    (V293_ISR_sched_pre unmap group rows high bt bg br bh li I tid lg) _).
  unfold V293_ISR_sched_pre. destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ]; [ | exact Logic.I].
  split; [apply V293_sched_internal_pre_good; exact Hli | apply V293_sched_ISR_context_good].
Defined.
Definition V293_ISR_sched_fpost (unmap group rows high : var) (bt bg br bh : block) (li : LocalInv) (I : Inv)
    (Hli : GoodLInvAsrt li) : fpost.
Proof.
  intros vl result lg tid. refine (@mkfunasrt
    (V293_ISR_sched_post unmap group rows high bt bg br bh li I tid lg result) _).
  unfold V293_ISR_sched_post. destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ]; [ | exact Logic.I].
  split; [apply V293_sched_internal_post_good; exact Hli | apply V293_sched_ISR_context_good].
Defined.

(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_ISR_contract : forall P f Spec sd li I RI
    unmap group rows high y bt bg br bh (Hli : GoodLInvAsrt li) lg tid vl pre post,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  P f = Some (V293_OSSchedNew_function unmap group rows high y) ->
  Some pre = BuildPreI P f vl lg (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli) tid ->
  Some post = BuildRetI P f vl lg (V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli) tid ->
  InfRules Spec sd li RI post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
  intros P f Spec sd li I RI unmap group rows high y bt bg br bh Hli lg tid vl pre post
    Hu Hg Hr Hh Hcode Hpre Hpost.
  unfold BuildPreI in Hpre. rewrite Hcode in Hpre.
  destruct vl as [ | v vl].
  2: { assert (E : dl_vl_match dnil (rev (v :: vl)) = false).
       { destruct (rev (v :: vl)) eqn:Er; [ | reflexivity].
         apply (f_equal (@rev val)) in Er. rewrite rev_involutive in Er. discriminate. }
       unfold V293_OSSchedNew_function in Hpre. rewrite E in Hpre. discriminate. }
  change (Some pre = Some (((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_ISR_sched_pre unmap group rows high bt bg br bh li I tid lg ** V293_sched_local_domain y)) in Hpre.
  inversion Hpre; subst pre.
  unfold BuildRetI in Hpost. rewrite Hcode in Hpost.
  change (Some post = Some (fun result => ((EX v : val, LV y @ Tint8 |-> v) ** Aemp) **
    V293_ISR_sched_post unmap group rows high bt bg br bh li I tid lg result ** V293_sched_local_domain y)) in Hpost.
  inversion Hpost; subst post.
  unfold V293_ISR_sched_pre, V293_ISR_sched_post.
  destruct (V293_ISR_sched_args lg) as [[[[[[[lo hi] op] held] ir] si] ci] | ];
    [apply V293_sched_internal_payload; assumption | apply V293_sched_false_entry].
Qed.

Definition V293_ISR_sched_spec sched_id unmap group rows high bt bg br bh li I
    (Hli : GoodLInvAsrt li) : funspec :=
  fun f => if Z.eq_dec f sched_id then Some
    (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) else None.
(* Resource ownership I and ambient rule invariant RI need not coincide. *)
Theorem V293_OSSchedNew_ISR_WFFunEnv : forall sched_id unmap group rows high y bt bg br bh li I RI Hli sd,
  unmap <> y -> group <> y -> rows <> y -> high <> y ->
  WFFunEnv (V293_OSSchedNew_internal_unit sched_id unmap group rows high y)
    (V293_ISR_sched_spec sched_id unmap group rows high bt bg br bh li I Hli) sd li RI.
Proof.
  intros sched_id unmap group rows high y bt bg br bh li I RI Hli sd Hu Hg Hr Hh. split.
  - intros f. unfold V293_OSSchedNew_internal_unit, V293_ISR_sched_spec.
    destruct (Z.eq_dec f sched_id); split; intros [a H]; try discriminate; eexists; reflexivity.
  - intros f pre post t tl Hspec. unfold V293_ISR_sched_spec in Hspec.
    destruct (Z.eq_dec f sched_id); try discriminate. inversion Hspec; subst pre post t tl.
    exists dnil. exists (dcons y Tint8 dnil). exists (V293_OSSchedNew_body unmap group rows high y).
    split.
    + unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
    + split; [constructor | ]. split; [reflexivity | ].
      intros vl pre post lg tid Hpre Hpost.
      eapply V293_OSSchedNew_ISR_contract; try eassumption.
      unfold V293_OSSchedNew_internal_unit. destruct (Z.eq_dec f sched_id); [reflexivity | contradiction].
Qed.

Definition V293_ISR_sched_call_lg lo hi aop held ir si ci : list logicvar :=
 cons (logic_lv (cons (V293_byteval lo) (cons (V293_byteval hi) nil)))
  (cons (logic_code aop) (cons (logic_ie held)
  (cons (logic_isr ir) (cons (logic_is si) (cons (logic_cs ci) nil))))).
Lemma V293_ISR_sched_args_roundtrip : forall lo hi aop held ir si ci,
 lo<256 -> hi<256 ->
 V293_ISR_sched_args(V293_ISR_sched_call_lg lo hi aop held ir si ci)=
 Some(lo,hi,aop,held,ir,si,ci).
Proof.
 intros. unfold V293_ISR_sched_args,V293_ISR_sched_call_lg,V293_byteval.
 rewrite !V293_sched_snapshot_roundtrip by assumption;reflexivity.
Qed.
Theorem V293_OSSchedNew_ISR_call : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi held ir si ci (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
       V293_sched_ISR_context I held ir si ci) ** frame)
    (scall sched_id nil)
    (EX result : option val,
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci) ** frame) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi held ir si ci Hli
    Hlo Hhi Hframe Hspec.
  assert (Ep : getasrt (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli nil
    (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) =
    V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_ISR_context I held ir si ci).
  { change (V293_ISR_sched_pre unmap group rows high bt bg br bh li I tid
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) =
      V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** V293_sched_ISR_context I held ir si ci).
    unfold V293_ISR_sched_pre. rewrite V293_ISR_sched_args_roundtrip by assumption. reflexivity. }
  assert (Eq : forall result, getasrt (V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli nil result
    (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) =
    V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_ISR_context I held ir si ci).
  { intro. change (V293_ISR_sched_post unmap group rows high bt bg br bh li I tid
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) result =
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result ** V293_sched_ISR_context I held ir si ci).
    unfold V293_ISR_sched_post. rewrite V293_ISR_sched_args_roundtrip by assumption. reflexivity. }
  eapply conseq_rule with (q := EX result : option val,
    getasrt (V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli nil result
      (V293_ISR_sched_call_lg lo hi aop held ir si ci) tid) ** frame).
  - intros s H; exact H.
  - intros s [result Hs]. exists result. rewrite Eq in Hs. exact Hs.
  - eapply call_rule with
      (pre := V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli)
      (post := V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli)
      (vl := nil) (logicl := V293_ISR_sched_call_lg lo hi aop held ir si ci) (tp := Tvoid) (tl := nil).
    + exact Hframe.
    + exact Hspec.
    + rewrite Ep. intros s H; exact H.
    + intros s H. reflexivity.
    + reflexivity.
    + rewrite Ep. eapply V293_star_CurLINV_l. apply V293_sched_internal_pre_CurLINV.
    + intros s [result Hs]. rewrite Eq in Hs.
      eapply V293_star_CurLINV_l; [ | exact Hs]. apply V293_sched_internal_post_CurLINV.
Qed.

Theorem V293_OSSched_ISR_prefix : forall Spec sd li I RI r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks old
    held ir si ci (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
     V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli, (Tvoid, nil)) ->
  InfRules Spec sd li RI r ri
    ((V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
      V293_sched_ISR_context I held ir si ci) **
      (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old))
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (EX t : Modules.tid, [|V293_highest_ready tasks t|] **
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo (Vptr t)))) tid.
Proof.
  intros Spec sd li I RI r ri tid aop frame sched_id unmap group rows high bt bg br bh lo hi
    table target tp bp bo entries tasks old held ir si ci Hli Hlo Hhi Hr Hb Htable Hframe Hspec.
  destruct (V293_ready_selection_task lo hi entries tasks Hlo Hhi Hr Hb Htable)
    as [t [m [Ht [Hentry Hhighest]]]].
  unfold V293_OSSched_unlocked_prefix. eapply seq_rule with
    (p' := V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo old)).
  - eapply conseq_rule with (q := EX result : option val,
      (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        V293_sched_ISR_context I held ir si ci) **
        (V293_prefix_frame table high target tp bp bo entries tasks frame ** V293_prefix_output tp bo old)).
    + intros s Hs; exact Hs.
    + intros s [result Hs].
      assert (Hs' : s |= V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop result **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo old)).
      { unfold V293_prefix_frame in *. sep auto. }
      apply V293_prefix_call_post. exists result. exact Hs'.
    + apply V293_OSSchedNew_ISR_call with (Hli := Hli); try assumption.
      split; [apply V293_prefix_frame_good; exact Hframe | constructor].
  - eapply conseq_rule with (q :=
      V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
        (V293_prefix_frame table high target tp bp bo entries tasks
          (V293_sched_ISR_context I held ir si ci ** frame) ** V293_prefix_output tp bo (Vptr t))).
    + intros s Hs; exact Hs.
    + intros s Hs. exists t. apply astar_l_apure_intro; [exact Hs | exact Hhighest].
    + apply V293_OSSched_target_assign; assumption.
Qed.


(* Enabled dispatch is actually executed, including the internal call and
   pointer update. Equal priorities exclude only the handoff, not dispatch. *)
Section ExitContext.
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
Let pre nest old c := V293_exit_ready_pre unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter bn bl nc
 (context ** frame) nest 0 old c.
Let tail c := V293_OSSched_tail_state unmap group rows high bt bg br bh lo hi li tid aop
 table target tp bp bo entries tasks current counter bcur bcounter nc
 (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)(context ** frame)) c.

Theorem V293_OSIntExit_context_same_dispatch : forall Spec sd RI r ri sched_id
 nest old c handoff (Hli:GoodLInvAsrt li),
 lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) -> nc<256 -> nest<=1 ->
 V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
 (forall st,st |= frame -> V293_interrupt_env nesting lock bn bl(getgenv st)(getlenv st)) ->
 V293_ready_select lo hi(V293_ready_group lo hi)=nc ->
 Spec sched_id=Some(V293_ISR_sched_fpre unmap group rows high bt bg br bh li resourceI Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li resourceI Hli,(Tvoid,nil)) ->
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
   apply V293_exit_ready_decrement with(lock:=lock);try assumption;lia.
 - unfold V293_OSIntExit_guards.
   eapply V293_exit_known_if with(flag:=true).
   + intros st H. exact(proj1(V293_exit_ready_guard_eval unmap group rows high
     bt bg br bh lo hi li tid aop table target tp bp bo entries tasks current counter
     nesting lock bcur bcounter bn bl nc (context ** frame) 0 0 old c st
     ltac:(lia) ltac:(lia) Env' H)).
   + eapply V293_exit_known_if with(flag:=true).
     * intros st H. exact(proj2(V293_exit_ready_guard_eval unmap group rows high
       bt bg br bh lo hi li tid aop table target tp bp bo entries tasks current counter
       nesting lock bcur bcounter bn bl nc (context ** frame) 0 0 old c st
       ltac:(lia) ltac:(lia) Env' H)).
     * unfold V293_exit_boundary_dispatch. eapply seq_rule with(p':=tail c).
       -- eapply conseq_rule with
         (p:=(V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop ** context) **
           (V293_prefix_frame table high target tp bp bo entries tasks
             (V293_guard_cell current bcur nc **
               (V293_counter_cell counter bcounter c **
                V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)frame)) **
            V293_prefix_output tp bo old))
         (q:=EX t:Modules.tid,[|V293_highest_ready tasks t|] **
           (V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
             (V293_prefix_frame table high target tp bp bo entries tasks
               (context ** (V293_guard_cell current bcur nc **
                 (V293_counter_cell counter bcounter c **
                  V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)frame))) **
              V293_prefix_output tp bo(Vptr t)))).
          ++ unfold pre,V293_exit_ready_pre,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells.
             cbn[V293_rdy_raw_cells]. intros st H;clear -H;sep auto.
          ++ unfold tail,V293_OSSched_tail_state,V293_prefix_frame,V293_exit_cells,V293_interrupt_cells.
             cbn[V293_rdy_raw_cells]. intros st[t H];exists t;clear -H;sep auto.
          ++ apply V293_OSSched_ISR_prefix with(Hli:=Hli);try assumption.
             repeat split;try apply V293_guard_cell_good;try apply V293_counter_cell_good.
             unfold V293_exit_cells,V293_interrupt_cells;cbn[V293_rdy_raw_cells GoodFrm];tauto.
       -- eapply V293_exit_known_if with(flag:=false);[ |apply skip_rule].
          intros st H. destruct(V293_OSSched_priority_comparison unmap group rows high bt bg br bh lo hi li tid aop
           table target tp bp bo entries tasks current counter bcur bcounter nc
           (V293_rdy_raw_cells(V293_exit_cells bn bl 0 0)(context ** frame)) c st
           Low High Ready Cur H)as[V T].
          rewrite Same,Nat.eqb_refl in V. split;[exact V|split;[exact T|discriminate]].
Qed.
End ExitContext.
