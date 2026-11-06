(* Pre-start concrete initialization: no CurTid/CurLINV fiction.
   This proves uninterleaved cstepstar, not interrupt interference safety. *)
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Record V293_init_slot := { init_name : var; init_type : type; init_block : block }.
Definition V293_init_binding d :=
  Agvarenv (init_name d) (init_type d) (init_block d,0%Z) //\\ A_notin_lenv (init_name d).
Definition V293_init_memory d (zeroed : bool) :=
  if zeroed then Amapsto (init_block d,0%Z) (init_type d) true (Vint32 Int.zero)
  else EX old : val, Amapsto (init_block d,0%Z) (init_type d) true old.
Fixpoint V293_init_resources slots zeroed (frame : asrt) : asrt :=
  match slots with
  | [] => frame
  | d::tail => (V293_init_binding d ** V293_init_memory d zeroed) ** V293_init_resources tail zeroed frame
  end.
Definition V293_init_scalar d := init_type d = Tint8 \/ init_type d = Tint32.
Definition V293_init_program slots :=
  V293_init_zero_sequence (map (fun d => (init_name d,init_type d)) slots).

Lemma V293_init_binding_eval : forall d R ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_init_binding d ** R ->
  evaltype (evar (init_name d)) (ge,le,M) = Some (init_type d) /\
  evaladdr (evar (init_name d)) (ge,le,M) = Some (Vptr (init_block d,Int.zero)).
Proof.
  intros d R ge le M ir aux O op H.
  assert (E : get ge (init_name d) = Some (init_block d,init_type d) /\ get le (init_name d)=None).
  { change (get (getgenv (ge,le,M,ir,aux,O,op)) (init_name d) = Some (init_block d,init_type d) /\
      get (getlenv (ge,le,M,ir,aux,O,op)) (init_name d)=None).
    eapply V293_star_env_l; [ | exact H]. intros s [G [N _]].
    destruct G as [b [G [B _]]]. inversion B;subst b.
    split;[exact G | ]. destruct (get (getlenv s) (init_name d)) as [v | ] eqn:EV;[ | reflexivity].
    exfalso;apply N;exists v;exact EV. }
  destruct E as [G N]. cbn [evaltype evaladdr get_lenv get_genv]. rewrite N,G. split;reflexivity.
Qed.

Lemma V293_init_one : forall P ks d R ge le M ir aux O op,
  V293_init_scalar d ->
  (ge,le,M,ir,aux,O,op) |= (V293_init_binding d ** V293_init_memory d false) ** R ->
  exists Mf,
    cstepstar P (curs (V293_init_zero (init_name d) (init_type d)),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= (V293_init_binding d ** V293_init_memory d true) ** R.
Proof.
  intros P ks d R ge le M ir aux O op Scalar Owned.
  assert (Bind : (ge,le,M,ir,aux,O,op) |= V293_init_binding d ** Atrue).
  { clear -Owned. sep auto. }
  destruct (V293_init_binding_eval _ _ _ _ _ _ _ _ _ Bind) as [Ty Addr].
  assert (Raw : (ge,le,M,ir,aux,O,op) |= V293_init_memory d false ** (V293_init_binding d ** R)).
  { clear -Owned. sep auto. }
  cbn [V293_init_memory] in Raw. apply astar_l_aexists_elim in Raw. destruct Raw as [old Raw].
  assert (Valid : rule_type_val_match (init_type d) (Vint32 Int.zero)=true).
  { destruct Scalar as [T | T];rewrite T;reflexivity. }
  destruct (V293_tick_raw_slot_update _ _ _ _ _ _ _ _ _ _ _ _ Valid Raw)
    as (Mf & Store & Updated).
  exists Mf. split.
  - unfold V293_init_zero. eapply c_stepstarn.
    { eapply stmt_step; [reflexivity | ]. eapply sassign_step with (t2:=init_type d).
      - exact Ty.
      - cbn [evaltype]. destruct Scalar as [T | T];rewrite T;reflexivity.
      - destruct Scalar as [T | T];rewrite T;apply eq_int;auto. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps. apply evalval_imply_estepstar.
      cbn [evalval]. destruct Scalar as [T | T];rewrite T;reflexivity. }
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | constructor]. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq;[exact Ty | exact Addr]. }
    eapply c_stepstarn.
    { eapply stmt_step; [reflexivity | ]. eapply sassignend_step;try reflexivity. exact Store. }
    apply c_stepstar0.
  - unfold V293_init_memory. unfold V293_owned_record_cell in Updated.
    apply astar_assoc_elim in Updated. apply astar_l_apure_elim in Updated.
    destruct Updated as [_ Updated]. clear -Updated. sep auto.
Qed.

Lemma V293_init_frame_out : forall slots z A R,
  V293_init_resources slots z (A ** R) ==> A ** V293_init_resources slots z R.
Proof.
  induction slots as [ | d tail IH];intros z A R s H;cbn [V293_init_resources] in *.
  - exact H.
  - assert (K : s |= (V293_init_binding d ** V293_init_memory d z) **
      (A ** V293_init_resources tail z R)).
    { eapply astar_mono;[intros st Hst;exact Hst | apply IH | exact H]. }
    clear -K. sep auto.
Qed.
Lemma V293_init_frame_in : forall slots z A R,
  A ** V293_init_resources slots z R ==> V293_init_resources slots z (A ** R).
Proof.
  induction slots as [ | d tail IH];intros z A R s H;cbn [V293_init_resources] in *.
  - exact H.
  - eapply astar_mono;[intros st Hst;exact Hst | apply IH | ].
    clear -H. sep auto.
Qed.

(* R need not be empty, well-framed, or a running-task invariant. It is
   preserved in exactly the memory produced by all real stores. *)
Theorem V293_init_sequence_execution : forall slots P ks R ge le M ir aux O op,
  Forall V293_init_scalar slots ->
  (ge,le,M,ir,aux,O,op) |= V293_init_resources slots false R ->
  exists Mf,
    cstepstar P (curs (V293_init_program slots),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_init_resources slots true R.
Proof.
  induction slots as [ | d tail IH];intros P ks R ge le M ir aux O op Valid Owned.
  - exists M. split;[apply c_stepstar0 | exact Owned].
  - inversion Valid as [ | d' tail' HD HT];subst.
    destruct (V293_init_one P (kseq (V293_init_program tail) ks) d _ _ _ _ _ _ _ _ HD Owned)
      as (M1 & First & Updated).
    assert (Rest : (ge,le,M1,ir,aux,O,op) |= V293_init_resources tail false
      ((V293_init_binding d ** V293_init_memory d true) ** R)).
    { apply V293_init_frame_in. exact Updated. }
    destruct (IH P ks _ _ _ _ _ _ _ _ HT Rest) as (Mf & Last & Final).
    exists Mf. split.
    + cbn [V293_init_program V293_init_zero_sequence map].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact First | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      exact Last.
    + cbn [V293_init_resources]. apply V293_init_frame_out in Final. exact Final.
Qed.

Lemma V293_init_readback : forall slots R s,
  Forall V293_init_scalar slots -> s |= V293_init_resources slots true R ->
  forall d, In d slots -> load (init_type d) (getmem s) (init_block d,0%Z) = Some (Vint32 Int.zero).
Proof.
  induction slots as [ | d tail IH];intros R s Valid Owned target Member;[contradiction | ].
  inversion Valid as [ | d' tail' HD HT];subst.
  destruct Member as [Same | Member].
  - subst target. eapply V293_star_load_l;[ | exact Owned].
    intros st Hst. eapply V293_star_load_r;[ | exact Hst].
    intros st' [Points Empty]. eapply mapstoval_load;[ | exact Points].
    destruct HD as [T | T];rewrite T;reflexivity.
  - eapply V293_star_load_r;[ | exact Owned]. intros st Hst.
    exact (IH R st HT Hst target Member).
Qed.
Lemma V293_init_preserved_frame : forall slots z R,
  V293_init_resources slots z R ==> Atrue ** R.
Proof.
  induction slots as [ | d tail IH];intros z R s H;cbn [V293_init_resources] in H.
  - clear -H. sep auto.
  - assert (K : s |= (V293_init_binding d ** V293_init_memory d z) ** (Atrue ** R)).
    { eapply astar_mono;[intros st Hst;exact Hst | apply IH | exact H]. }
    clear -K. sep auto.
Qed.

Definition V293_InitMisc_slots time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs :=
  [Build_V293_init_slot time Tint32 bt; Build_V293_init_slot interrupt Tint8 bi;
   Build_V293_init_slot lock Tint8 bl; Build_V293_init_slot tasks Tint8 bk;
   Build_V293_init_slot running Tint8 br; Build_V293_init_slot switches Tint32 bc;
   Build_V293_init_slot idle Tint32 bd; Build_V293_init_slot idle_run Tint32 bdr;
   Build_V293_init_slot idle_max Tint32 bdm; Build_V293_init_slot stat_ready Tint8 bs].

Theorem V293_OS_InitMisc_execution : forall P ks R ge le M ir aux O op
    time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs,
  let slots := V293_InitMisc_slots time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs in
  (ge,le,M,ir,aux,O,op) |= V293_init_resources slots false R ->
  exists Mf,
    cstepstar P
      (curs (V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_init_resources slots true R.
Proof.
  intros. eapply (V293_init_sequence_execution slots);[ | exact H].
  unfold slots,V293_InitMisc_slots.
  repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil.
Qed.

(* The real no-argument/no-local function call and void return. The frame
   is deliberately interpreted in the callee's empty environment, not silently
   transported from an arbitrary caller environment. Readback can subsequently
   be transported for memory-only properties; R itself is not asserted there. *)
Theorem V293_OS_InitMisc_call_return : forall P ks R ge caller M ir aux O op f
    time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs,
  P f = Some (V293_InitMisc_function time interrupt lock tasks running switches idle idle_run idle_max stat_ready) ->
  let slots := V293_InitMisc_slots time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs in
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false R ->
  exists Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |= V293_init_resources slots true R.
Proof.
  intros P ks R ge caller M ir aux O op f time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs Program slots Owned.
  set (body := sseq (V293_InitMisc_updates time interrupt lock tasks running switches idle idle_run idle_max stat_ready) sret).
  destruct (V293_OS_InitMisc_execution P (kseq sret (kcall f body caller ks)) R
    ge emp M ir aux O op time interrupt lock tasks running switches idle idle_run idle_max stat_ready
    bt bi bl bk br bc bd bdr bdm bs Owned) as (Mf & Exec & Final).
  exists Mf. split;[ | exact Final].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply snpcall_step]. }
  eapply c_stepstarn.
  { eapply stmt_step;[reflexivity | ]. eapply sfexec_step with (d1:=dnil) (d2:=dnil);
    [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
  eapply V293_cstepstar_trans;[exact Exec | ].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
  eapply c_stepstarn.
  { eapply stmt_step;[reflexivity | ]. eapply sret_step;[reflexivity | reflexivity | reflexivity]. }
  eapply c_stepstarn.
  { eapply stmt_step;[reflexivity | ]. eapply sfreeend_step;[reflexivity | reflexivity | reflexivity]. }
  apply c_stepstar0.
Qed.
Print Assumptions V293_OS_InitMisc_execution.
Print Assumptions V293_OS_InitMisc_call_return.
