(* Pre-start resources and actual two-iteration loop. No running-task premise. *)
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Fixpoint V293_rdy_raw_cells (cells : list V293_record_cell) (R : asrt) : asrt :=
  match cells with
  | [] => R
  | (a,tp,v)::tail => Amapsto a tp true v ** V293_rdy_raw_cells tail R
  end.
Lemma V293_rdy_cell_out : forall before a tp v after R,
  V293_rdy_raw_cells (before++(a,tp,v)::after) R ==>
    Amapsto a tp true v ** V293_rdy_raw_cells (before++after) R.
Proof.
  induction before as [ | [[b t] w] tail IH];intros a tp v after R s H;cbn [V293_rdy_raw_cells app] in *.
  - exact H.
  - assert (K : s |= Amapsto b t true w **
      (Amapsto a tp true v ** V293_rdy_raw_cells (tail++after) R)).
    { eapply astar_mono;[intros st HS;exact HS | apply IH | exact H]. }
    clear -K. sep auto.
Qed.
Lemma V293_rdy_cell_in : forall before a tp v after R,
  Amapsto a tp true v ** V293_rdy_raw_cells (before++after) R ==>
    V293_rdy_raw_cells (before++(a,tp,v)::after) R.
Proof.
  induction before as [ | [[b t] w] tail IH];intros a tp v after R s H;cbn [V293_rdy_raw_cells app] in *.
  - exact H.
  - eapply astar_mono;[intros st HS;exact HS | apply IH | ]. clear -H. sep auto.
Qed.
Lemma V293_rdy_raw_load : forall cells R a tp v s,
  In (a,tp,v) cells -> rule_type_val_match tp v=true ->
  s |= V293_rdy_raw_cells cells R -> load tp (getmem s) a=Some v.
Proof.
  induction cells as [ | [[b t] w] tail IH];intros R a tp v s Member Valid Owned;[contradiction | ].
  destruct Member as [E | Member].
  - inversion E;subst. eapply V293_star_load_l;[ | exact Owned].
    intros st [Points Empty]. eapply mapstoval_load;[exact Valid | exact Points].
  - eapply V293_star_load_r;[ | exact Owned]. intros st Hst. eapply IH;eauto.
Qed.
Lemma V293_rdy_assign : forall before a tp old after replacement e1 e2 rt R P ge le M ir aux O op,
  evaltype e1 (ge,le,M)=Some tp -> evaladdr e1 (ge,le,M)=Some (Vptr (fst a,Int.repr (snd a))) ->
  Int.unsigned (Int.repr (snd a))=snd a ->
  evaltype e2 (ge,le,M)=Some rt -> assign_type_match tp rt ->
  evalval e2 (ge,le,M)=Some replacement -> rule_type_val_match tp replacement=true ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (before++(a,tp,old)::after) R ->
  exists Mf,
    (forall ks, cstepstar P (curs (sassign e1 e2),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (before++(a,tp,replacement)::after) R.
Proof.
  intros before a tp old after replacement e1 e2 rt R P ge le M ir aux O op Ty Addr Offset RT Match Value Valid Owned.
  apply V293_rdy_cell_out in Owned.
  destruct (V293_tick_raw_slot_update _ _ _ _ _ _ _ _ _ _ _ _ Valid Owned) as (Mf & Store & Updated).
  exists Mf. split.
  - intro ks. eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply sassign_step; eauto. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps;apply evalval_imply_estepstar;exact Value. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
    eapply V293_cstepstar_trans.
    { apply V293_expr_steps;apply evalval_imply_estepstar. eapply evaladdr_val_eq;eauto. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply sassignend_step;try reflexivity.
      unfold addrval_to_addr. rewrite Offset. destruct a;exact Store. }
    apply c_stepstar0.
  - apply V293_rdy_cell_in. unfold V293_owned_record_cell in Updated.
    apply astar_assoc_elim in Updated. apply astar_l_apure_elim in Updated.
    destruct Updated as [_ Updated]. exact Updated.
Qed.
Definition V293_rdy_env ge le group rows prio high top current i bg br bp bh bt bc bi :=
  get le i=Some (bi,Tint8) /\
  get le group=None /\ get ge group=Some (bg,Tint8) /\
  get le rows=None /\ get ge rows=Some (br,Tarray Tint8 2) /\
  get le prio=None /\ get ge prio=Some (bp,Tint8) /\
  get le high=None /\ get ge high=Some (bh,Tint8) /\
  get le top=None /\ get ge top=Some (bt,Tptr V293_tcb_type) /\
  get le current=None /\ get ge current=Some (bc,Tptr V293_tcb_type).
Definition V293_rdy_cells bg br bp bh bt bc bi vg vlo vhi vp vh vt vc vi : list V293_record_cell :=
  [((bg,0%Z),Tint8,vg);((br,0%Z),Tint8,vlo);((br,1%Z),Tint8,vhi);
   ((bp,0%Z),Tint8,vp);((bh,0%Z),Tint8,vh);
   ((bt,0%Z),Tptr V293_tcb_type,vt);((bc,0%Z),Tptr V293_tcb_type,vc);((bi,0%Z),Tint8,vi)].
Definition V293_rdy_final_cells bg br bp bh bt bc bi :=
  V293_rdy_cells bg br bp bh bt bc bi (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero)
    (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull (Vint32 (Int.repr 2)).
Lemma V293_rdy_while_false : forall P ks ge le M e body,
  evalval e (ge,le,M)=Some (Vint32 Int.zero) ->
  cstepstar P (curs (swhile e body),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros. eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply swhile_step]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps;apply evalval_imply_estepstar;exact H. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply svwhilef_step;reflexivity]. }
  apply c_stepstar0.
Qed.
Lemma V293_rdy_while_true : forall P ks ge le M M1 M2 e body,
  evalval e (ge,le,M)=Some (Vint32 Int.one) ->
  (forall tail, cstepstar P (curs body,(kenil,tail)) (ge,le,M)
    (curs (sskip None),(kenil,tail)) (ge,le,M1)) ->
  cstepstar P (curs (swhile e body),(kenil,ks)) (ge,le,M1)
    (curs (sskip None),(kenil,ks)) (ge,le,M2) ->
  cstepstar P (curs (swhile e body),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M2).
Proof.
  intros P ks ge le M M1 M2 e body Guard Body Rest.
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply swhile_step]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps;apply evalval_imply_estepstar;exact Guard. }
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply svwhilet_step;reflexivity]. }
  eapply V293_cstepstar_trans;[apply Body | ].
  eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
  exact Rest.
Qed.
Ltac V293_rdy_eval :=
  cbn [evaltype evalval evaladdr get_lenv get_genv get_mem];
  cbv delta [env var memory.ident Modules.ident] in *;
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  reflexivity.
Ltac V293_rdy_write P H n lhs rhs value next step owned :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let before := eval cbn in (firstn n cells) in
    let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
    let after := eval cbn in (skipn (S n) cells) in
    lazymatch cell with (?a,?tp,?old) =>
    let updated := eval cbn [app] in (before++(a,tp,value)::after) in
    let T := fresh "Write" in
    assert (T : exists Mf,
      (forall ks, cstepstar P (curs (sassign lhs rhs),(kenil,ks)) (ge,le,M)
        (curs (sskip None),(kenil,ks)) (ge,le,Mf)) /\
      (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells updated R);
    [ eapply (V293_rdy_assign before a tp old after value lhs rhs tp R P ge le M ir aux O op);
      [V293_rdy_eval | V293_rdy_eval | reflexivity | V293_rdy_eval |
       first [solve [apply eq_int;auto] | apply eq_vptr;do 2 eexists;split;reflexivity] |
       V293_rdy_eval | reflexivity | exact H] |
      destruct T as (next & step & owned)]
    end
  end.
Ltac V293_rdy_i_read H name :=
  lazymatch type of H with
  | (?ge,?le,?M,?ir,?aux,?O,?op) |= V293_rdy_raw_cells ?cells ?R =>
    let cell := eval cbn in (nth 7 cells ((1%positive,0%Z),Tint8,Vundef)) in
    lazymatch cell with (?a,?tp,?v) =>
    assert (name : load tp M a=Some v);
    [change (load tp (getmem (ge,le,M,ir,aux,O,op)) a=Some v);
     eapply (V293_rdy_raw_load cells R a tp v (ge,le,M,ir,aux,O,op));
     [do 7 right;left;reflexivity | reflexivity | exact H] | ]
    end
  end.
Theorem V293_OS_InitRdyList_execution : forall P ks ge le M ir aux O op R
  group rows prio high top current i bg br bp bh bt bc bi vg vlo vhi vp vh vt vc vi,
  V293_rdy_env ge le group rows prio high top current i bg br bp bh bt bc bi ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_rdy_cells bg br bp bh bt bc bi vg vlo vhi vp vh vt vc vi) R ->
  exists Mf,
    cstepstar P (curs (V293_InitRdyList_updates group rows prio high top current i),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= V293_rdy_raw_cells (V293_rdy_final_cells bg br bp bh bt bc bi) R.
Proof.
  intros P ks ge le M ir aux O op R group rows prio high top current i bg br bp bh bt bc bi
    vg vlo vhi vp vh vt vc vi Env Owned.
  destruct Env as (Li & Ng & Gg & Nr & Gr & Np & Gp & Nh & Gh & Nt & Gt & Nc & Gc).
  unfold V293_rdy_cells in Owned.
  unfold V293_rdy_zero.
  V293_rdy_write P Owned 0 (evar group) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M1 Sg H1.
  V293_rdy_write P H1 7 (evar i) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M2 Si H2.
  V293_rdy_i_read H2 I0.
  assert (G0 : evalval (V293_rdy_guard i) (ge,le,M2)=Some (Vint32 Int.one)).
  { unfold V293_rdy_guard. V293_rdy_eval. }
  V293_rdy_write P H2 1 (earrayelem (evar rows) (evar i)) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M3 Sr0 H3.
  V293_rdy_i_read H3 I0'.
  V293_rdy_write P H3 7 (evar i) (ecast (ebinop oplus (ecast (evar i) Tint32) (econst32 Int.one)) Tint8)
    (Vint32 Int.one) M4 In1 H4.
  V293_rdy_i_read H4 I1.
  assert (G1 : evalval (V293_rdy_guard i) (ge,le,M4)=Some (Vint32 Int.one)).
  { unfold V293_rdy_guard. V293_rdy_eval. }
  V293_rdy_write P H4 2 (earrayelem (evar rows) (evar i)) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M5 Sr1 H5.
  V293_rdy_i_read H5 I1'.
  V293_rdy_write P H5 7 (evar i) (ecast (ebinop oplus (ecast (evar i) Tint32) (econst32 Int.one)) Tint8)
    (Vint32 (Int.repr 2)) M6 In2 H6.
  V293_rdy_i_read H6 I2.
  assert (G2 : evalval (V293_rdy_guard i) (ge,le,M6)=Some (Vint32 Int.zero)).
  { unfold V293_rdy_guard. V293_rdy_eval. }
  V293_rdy_write P H6 3 (evar prio) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M7 Sp H7.
  V293_rdy_write P H7 4 (evar high) (ecast (econst32 Int.zero) Tint8) (Vint32 Int.zero) M8 Sh H8.
  V293_rdy_write P H8 5 (evar top) (ecast enull (Tptr V293_tcb_type)) Vnull M9 St H9.
  V293_rdy_write P H9 6 (evar current) (ecast enull (Tptr V293_tcb_type)) Vnull M10 Sc H10.
  assert (Loop : forall tail, cstepstar P (curs (V293_rdy_loop rows i),(kenil,tail)) (ge,le,M2)
    (curs (sskip None),(kenil,tail)) (ge,le,M6)).
  { intro tail. unfold V293_rdy_loop,V293_rdy_increment,V293_rdy_zero.
    eapply V293_rdy_while_true;[exact G0 | | ].
    - intro cont. eapply V293_rekey_sequence_execution;[exact Sr0 | apply In1].
    - eapply V293_rdy_while_true;[exact G1 | | ].
      + intro cont. eapply V293_rekey_sequence_execution;[exact Sr1 | apply In2].
      + apply V293_rdy_while_false;exact G2. }
  exists M10. split;[ | exact H10].
  unfold V293_InitRdyList_updates,V293_rdy_zero.
  eapply V293_rekey_sequence_execution;[exact Sg | ].
  eapply V293_rekey_sequence_execution;[exact Si | ].
  eapply V293_rekey_sequence_execution;[exact Loop | ].
  eapply V293_rekey_sequence_execution;[exact Sp | ].
  eapply V293_rekey_sequence_execution;[exact Sh | ].
  eapply V293_rekey_sequence_execution;[exact St | apply Sc].
Qed.
Print Assumptions V293_OS_InitRdyList_execution.

Definition V293_rdy_locals (i : var) bi : env := set emp i (bi,Tint8).
Definition V293_rdy_globals bg br bp bh bt bc vg vlo vhi vp vh vt vc :=
  firstn 7 (V293_rdy_cells bg br bp bh bt bc 1%positive vg vlo vhi vp vh vt vc Vundef).
Lemma V293_rdy_local_addresses : forall i bi,
  getaddr (V293_rdy_locals i bi) = [(bi,Tint8)].
Proof.
  intros. unfold V293_rdy_locals.
  change (getaddr (EnvMod.set EnvMod.emp i (bi,Tint8)) = [(bi,Tint8)]).
  reflexivity.
Qed.
(* R is interpreted in the final callee environment. After free we expose
   exact byte preservation outside the allocated local block, not an
   unjustified transport of arbitrary environment-sensitive R to caller. *)
Theorem V293_OS_InitRdyList_call_return : forall P ks ge caller M ir aux O op R f
  group rows prio high top current i bg br bp bh bt bc bi vg vlo vhi vp vh vt vc,
  P f=Some (V293_InitRdyList_function group rows prio high top current i) ->
  fresh M bi ->
  V293_rdy_env ge (V293_rdy_locals i bi) group rows prio high top current i bg br bp bh bt bc bi ->
  (ge,V293_rdy_locals i bi,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_rdy_globals bg br bp bh bt bc vg vlo vhi vp vh vt vc) R ->
  exists Ms Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,V293_rdy_locals i bi,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_rdy_final_cells bg br bp bh bt bc bi) R /\
    (forall b off, b<>bi -> get Mf (b,off)=get Ms (b,off)) /\
    get Mf (bi,0%Z)=None.
Proof.
  intros P ks ge caller M ir aux O op R f group rows prio high top current i bg br bp bh bt bc bi
    vg vlo vhi vp vh vt vc Program Fresh Env Frame.
  pose proof (V293_tick_allocate_frame _ _ _ _ _ _ _ bi Tint8 _ Fresh Frame) as Allocated.
  assert (Start : (ge,V293_rdy_locals i bi,allocb M bi 0%Z 1,ir,aux,O,op) |=
    V293_rdy_raw_cells (V293_rdy_cells bg br bp bh bt bc bi vg vlo vhi vp vh vt vc Vundef) R).
  { change ((ge,V293_rdy_locals i bi,allocb M bi 0%Z 1,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_rdy_globals bg br bp bh bt bc vg vlo vhi vp vh vt vc ++
        [((bi,0%Z),Tint8,Vundef)]) R).
    apply V293_rdy_cell_in. exact Allocated. }
  set (body := sseq (V293_InitRdyList_updates group rows prio high top current i) sret).
  destruct (V293_OS_InitRdyList_execution P (kseq sret (kcall f body caller ks))
    ge (V293_rdy_locals i bi) (allocb M bi 0%Z 1) ir aux O op R
    group rows prio high top current i bg br bp bh bt bc bi vg vlo vhi vp vh vt vc Vundef Env Start)
    as (Ms & Exec & Final).
  assert (LocalCell : (ge,V293_rdy_locals i bi,Ms,ir,aux,O,op) |=
    Amapsto (bi,0%Z) Tint8 true (Vint32 (Int.repr 2)) ** Atrue).
  { change ((ge,V293_rdy_locals i bi,Ms,ir,aux,O,op) |=
      V293_rdy_raw_cells (V293_rdy_globals bg br bp bh bt bc
        (Vint32 Int.zero) (Vint32 Int.zero) (Vint32 Int.zero)
        (Vint32 Int.zero) (Vint32 Int.zero) Vnull Vnull ++
        [((bi,0%Z),Tint8,Vint32 (Int.repr 2))]) R) in Final.
    apply V293_rdy_cell_out in Final. clear -Final. sep auto. }
  pose proof (V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ LocalCell) as Writable.
  destruct (V293_tick_void_return P (kcall f body caller ks) ge (V293_rdy_locals i bi)
    caller Ms f body ks) as (Mf & Return & Preserve & Removed).
  - reflexivity.
  - rewrite V293_rdy_local_addresses. repeat constructor;cbn;tauto.
  - rewrite V293_rdy_local_addresses. intros b t [E | Bad];[inversion E;subst;exact Writable | contradiction].
  - exists Ms. exists Mf. split.
    + eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply snpcall_step]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply sfexec_step with (d1:=dnil) (d2:=dcons i Tint8 dnil);
        [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
        exists bi. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_emp_get in E. discriminate. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans;[exact Exec | ].
      eapply c_stepstarn. { eapply stmt_step;[reflexivity | constructor]. }
      exact Return.
    + split;[exact Final | ]. split.
      * intros b off Away. apply Preserve. rewrite V293_rdy_local_addresses. cbn.
        intros [E | Bad];[apply Away;congruence | contradiction].
      * change (get Mf (bi,Z.of_nat 0)=None). apply (Removed bi Tint8 0).
        -- rewrite V293_rdy_local_addresses. left;reflexivity.
        -- cbn;auto.
Qed.
Print Assumptions V293_OS_InitRdyList_call_return.
