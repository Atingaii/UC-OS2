(* Fixed V2.93.01 OSTimeGet/OSTimeSet, manual source-body mapping.
   encrit/excrit are the ADR0005 normalization, NOT port implementations.
   Body contracts start with allocated local ownership, not a linked API. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition V293_time_binding (local : bool) x b : asrt :=
  if local then Alvarenv x Tint32 (b,0%Z) else V293_counter_bindings x b.
Definition V293_time_cell local x b v : asrt :=
  V293_time_binding local x b ** PV (b,Int.zero) @ Tint32 |-> v.

Lemma V293_time_cell_good : forall local x b v,
  GoodFrm (V293_time_cell local x b v).
Proof.
  intros. destruct local; cbn [V293_time_cell V293_time_binding
    V293_counter_bindings Aptrmapsto GoodFrm]; tauto.
Qed.

Lemma V293_time_binding_env : forall local x b R s,
  s |= V293_time_binding local x b ** R ->
  get (getlenv s) x = Some (b,Tint32) \/
  (get (getlenv s) x = None /\ get (getgenv s) x = Some (b,Tint32)).
Proof.
  intros local x b R s H.
  eapply V293_star_env_l; [ | exact H]. intros s0 H0. destruct local.
  - left. destruct H0 as [b' [E [B _]]]. inversion B;subst b'. exact E.
  - right. destruct (V293_counter_env x b s0 H0);auto.
Qed.

Lemma V293_time_binding_star : forall local x b R s,
  s |= V293_time_binding local x b ** R ->
  evaladdr (evar x) (getsmem s) = Some (Vptr (b,Int.zero)) /\
  evaltype (evar x) (getsmem s) = Some Tint32.
Proof.
  intros local x b R s H.
  pose proof (V293_time_binding_env local x b R s H) as E.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  cbn [getlenv getgenv get_smem get_lenv get_genv] in E.
  cbn [getsmem get_smem evaladdr evaltype get_lenv get_genv].
  destruct E as [E | [N G]]; [rewrite E;auto | rewrite N,G;auto].
Qed.

Lemma V293_time_cell_read : forall local x b c R s,
  s |= V293_time_cell local x b (Vint32 c) ** R ->
  evalval (evar x) (getsmem s) = Some (Vint32 c) /\
  evaltype (evar x) (getsmem s) = Some Tint32.
Proof.
  intros local x b c R s H.
  assert (B : s |= V293_time_binding local x b **
    (PV (b,Int.zero) @ Tint32 |-> Vint32 c ** R)).
  { unfold V293_time_cell in H. sep auto. }
  destruct (V293_time_binding_star local x b _ s B) as [Address Ty].
  assert (L : load Tint32 (getmem s) (b,0%Z) = Some (Vint32 c)).
  { eapply V293_star_load_l; [ | exact H]. intros s0 H0.
    eapply V293_star_load_r; [ | exact H0]. intros s1 [Points _].
    eapply mapstoval_load; [reflexivity | exact Points]. }
  pose proof (V293_time_binding_env local x b _ s B) as E.
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  cbn [getmem get_smem get_mem] in L.
  cbn [getlenv getgenv get_smem get_lenv get_genv] in E.
  cbn [getsmem get_smem evalval evaltype get_lenv get_genv get_mem].
  destruct E as [E | [N G]]; [rewrite E;split;[exact L | reflexivity] |
    rewrite N,G;split;[exact L | reflexivity]].
Qed.

(* Copy from owned bytes, not from an expression-evaluation premise. *)
Theorem V293_time_copy : forall Spec sd li I r ri tid aop frame
    dl dst bd old sl src bs c,
  (frame ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** (V293_time_cell dl dst bd old **
      (V293_time_cell sl src bs (Vint32 c) ** frame)))
    (sassign (evar dst) (evar src))
    (<||aop||> ** (V293_time_cell dl dst bd (Vint32 c) **
      (V293_time_cell sl src bs (Vint32 c) ** frame))) tid.
Proof.
  intros Spec sd li I r ri tid aop frame dl dst bd old sl src bs c Inv.
  eapply conseq_rule with
    (p := <||aop||> ** ((V293_time_binding dl dst bd **
      (V293_time_cell sl src bs (Vint32 c) ** frame)) ** PV (bd,Int.zero) @ Tint32 |-> old))
    (q := <||aop||> ** ((V293_time_binding dl dst bd **
      (V293_time_cell sl src bs (Vint32 c) ** frame)) ** PV (bd,Int.zero) @ Tint32 |-> Vint32 c)).
  - unfold V293_time_cell. intros s H;sep auto.
  - unfold V293_time_cell. intros s H;sep auto.
  - eapply assign_rule with (tp2:=Tint32).
    + apply eq_int;auto.
    + intros s H. assert (B : s |= V293_time_binding dl dst bd ** Atrue).
      { clear -H. sep auto. }
      assert (C : s |= V293_time_cell sl src bs (Vint32 c) ** Atrue).
      { clear -H. sep auto. }
      destruct (V293_time_binding_star dl dst bd _ s B) as [Addr Ty].
      destruct (V293_time_cell_read sl src bs c _ s C) as [Value SType].
      split; [split;assumption | split;[exact Value | split;[exact SType | discriminate]]].
    + intros s H. apply V293_CurLINV_extend with (extra:=Atrue).
      eapply astar_mono; [exact Inv | intros s0 H0;exact H0 | ].
      clear -H. sep auto.
Qed.

Lemma V293_time_zero : forall Spec sd li I r ri tid aop frame saved bs old,
  (frame ==> CurLINV li tid) ->
  InfRules Spec sd li I r ri
    (<||aop||> ** (V293_time_cell true saved bs old ** frame))
    (sassign (evar saved) (econst32 Int.zero))
    (<||aop||> ** (V293_time_cell true saved bs (Vint32 Int.zero) ** frame)) tid.
Proof.
  intros Spec sd li I r ri tid aop frame saved bs old Inv.
  unfold V293_time_cell.
  eapply conseq_rule with
    (p:=<||aop||> ** ((V293_time_binding true saved bs ** frame) ** PV (bs,Int.zero) @ Tint32 |-> old))
    (q:=<||aop||> ** ((V293_time_binding true saved bs ** frame) ** PV (bs,Int.zero) @ Tint32 |-> Vint32 Int.zero)).
  - intros s H;sep auto.
  - intros s H;sep auto.
  - eapply assign_rule with (tp2:=Tint32).
    + apply eq_int;auto.
    + intros s H. assert (B : s |= V293_time_binding true saved bs ** Atrue).
      { clear -H. sep auto. }
      destruct (V293_time_binding_star true saved bs _ s B).
      split; [split;assumption | destruct s as [[[[[[ge le] M] ir] aux] O] op];repeat split;try reflexivity;discriminate].
    + intros s H. apply V293_CurLINV_extend with (extra:=Atrue).
      eapply astar_mono; [exact Inv | intros s0 H0;exact H0 | ]. clear -H. sep auto.
Qed.

Definition V293_TimeGet_body now ticks saved : stmts :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (sseq (sprim encrit)
      (sseq (sassign (evar ticks) (evar now)) (sprim excrit)))
      (srete (evar ticks))).
Definition V293_TimeSet_body now ticks saved : stmts :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (sseq (sprim encrit)
      (sseq (sassign (evar now) (evar ticks)) (sprim excrit))) sret).

Definition V293_time_payload now ticks saved bn bt bs clock tmp save frame : asrt :=
  V293_time_cell false now bn (Vint32 clock) **
    (V293_time_cell true ticks bt tmp ** (V293_time_cell true saved bs save ** frame)).

Lemma V293_time_topis : forall si R,
  Ais si ** R ==> ATopis (gettopis si) ** (Ais si ** R).
Proof.
  intros si R s H. apply astar_l_atopis_intro; [exact H | ].
  destruct s as [[[[[[ge le] M] ir] [[ie actual] cs]] O] op].
  apply sat_split in H.
  destruct H as (m1 & m2 & o1 & o2 & JM & JO & [E Empty] & Rest).
  cbn in E |- *. rewrite E. reflexivity.
Qed.

(* One wrapper for the two real critical paths. The body proof must preserve
   an arbitrary extra resource, including the actual acquired ISR invariant;
   the wrapper never substitutes True for I or assumes an execution result. *)
Theorem V293_time_critical : forall Spec sd li I r ri tid aop enabled ir si ci p q body,
  (gettopis si <= INUM)%nat -> GoodFrm p -> GoodFrm q ->
  (q ==> CurLINV li tid) ->
  (forall extra, InfRules Spec sd li I r ri (<||aop||> ** (p ** extra))
    body (<||aop||> ** (q ** extra)) tid) ->
  InfRules Spec sd li I r ri (<||aop||> ** OS[ir,enabled,si,ci] ** p)
    (sseq (sprim encrit) (sseq body (sprim excrit)))
    (<||aop||> ** OS[ir,enabled,si,ci] ** q) tid.
Proof.
  intros Spec sd li I r ri tid aop enabled ir si ci p q body Bound GP GQ Inv Body.
  destruct enabled.
  - eapply seq_rule.
    + eapply conseq_rule with
        (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis (gettopis si) ** [| (gettopis si <= INUM)%nat |] ** p)
        (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si) ** p).
      * intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
        pose proof (V293_time_topis si Atrue s S) as Top.
        apply astar_l_atopis_elim in Top. destruct Top as [Top _].
        pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
      * intros s H;exact H.
      * apply encrit1_rule;exact GP.
    + eapply seq_rule.
      * eapply conseq_rule; [ | | apply (Body (OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si)))];
          intros s H;sep auto.
      * eapply conseq_rule with
          (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis (gettopis si) ** invlth_isr I 0 (gettopis si) ** q)
          (q:=<||aop||> ** OS[ir,true,si,ci] ** q).
        -- intros s H. assert (S : s |= Ais si ** Atrue) by (sep auto).
           pose proof (V293_time_topis si Atrue s S) as Top.
           apply astar_l_atopis_elim in Top. destruct Top as [Top _].
           pose proof (@astar_l_atopis_intro s (gettopis si) _ H Top) as HT.
        clear H. rename HT into H. sep auto.
        -- intros s H;exact H.
        -- apply excrit1_rule;assumption.
  - eapply seq_rule.
    + apply encrit2_rule;exact GP.
    + eapply seq_rule.
      * eapply conseq_rule with (p:=<||aop||> ** p ** OS[ir,false,si,false::ci])
          (q:=<||aop||> ** q ** OS[ir,false,si,false::ci])
          (q':=<||aop||> ** OS[ir,false,si,false::ci] ** q);
        [ | | apply (Body (OS[ir,false,si,false::ci]))];
          intros s H;sep auto.
      * apply excrit2_rule;exact GQ.
Qed.


Lemma V293_time_payload_good : forall now ticks saved bn bt bs clock tmp save frame,
  GoodFrm frame -> GoodFrm (V293_time_payload now ticks saved bn bt bs clock tmp save frame).
Proof.
  intros. unfold V293_time_payload.
  cbn [GoodFrm V293_time_cell V293_time_binding V293_counter_bindings Aptrmapsto]. tauto.
Qed.
Lemma V293_time_payload_inv : forall now ticks saved bn bt bs clock tmp save frame li tid,
  (frame ==> CurLINV li tid) ->
  V293_time_payload now ticks saved bn bt bs clock tmp save frame ==> CurLINV li tid.
Proof.
  intros. unfold V293_time_payload in H0.
  eapply V293_star_CurLINV_r; [ | exact H0].
  eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r. exact H.
Qed.

(* Stable body contracts: allocated locals and owned global clock are required.
   The latter has NOT yet been moved into a system-wide IRQ invariant. *)
Theorem V293_OSTimeGet_body_hoare : forall Spec sd li I tid aop enabled ir si ci
    now ticks saved bn bt bs clock tmp save frame,
  (gettopis si <= INUM)%nat -> GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li I
    (fun result => [| result = Some (Vint32 clock) |] **
      (<||aop||> ** OS[ir,enabled,si,ci] **
        V293_time_payload now ticks saved bn bt bs clock (Vint32 clock) (Vint32 Int.zero) frame))
    Afalse
    (<||aop||> ** OS[ir,enabled,si,ci] **
      V293_time_payload now ticks saved bn bt bs clock tmp save frame)
    (V293_TimeGet_body now ticks saved) Afalse tid.
Proof.
  intros Spec sd li I tid aop enabled ir si ci now ticks saved bn bt bs clock tmp save frame Bound GF Inv.
  unfold V293_TimeGet_body.
  eapply seq_rule with (p':=<||aop||> ** OS[ir,enabled,si,ci] **
      V293_time_payload now ticks saved bn bt bs clock tmp (Vint32 Int.zero) frame).
  - eapply conseq_rule; [ | | apply (V293_time_zero _ _ _ _ _ _ _ aop
      (V293_time_cell false now bn (Vint32 clock) **
        (V293_time_cell true ticks bt tmp ** (frame ** OS[ir,enabled,si,ci]))) saved bs save)].
    + unfold V293_time_payload. intros s H;sep auto.
    + unfold V293_time_payload. intros s H;sep auto.
    + eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_l. exact Inv.
  - eapply seq_rule with (p':=<||aop||> ** OS[ir,enabled,si,ci] **
        V293_time_payload now ticks saved bn bt bs clock (Vint32 clock) (Vint32 Int.zero) frame).
    + eapply V293_time_critical; try exact Bound;
        try (apply V293_time_payload_good;exact GF);
        try (apply V293_time_payload_inv;exact Inv).
      intro extra. eapply conseq_rule; [ | | apply (V293_time_copy _ _ _ _ _ _ _ aop
        (V293_time_cell true saved bs (Vint32 Int.zero) ** (frame ** extra))
        true ticks bt tmp false now bn clock)].
      * unfold V293_time_payload. intros s H;sep auto.
      * unfold V293_time_payload. intros s H;sep auto.
      * eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_l. exact Inv.
    + eapply rete_rule with (v:=Vint32 clock) (t:=Tint32).
      intros s H. split.
      * apply astar_l_apure_intro; [exact H | reflexivity].
      * assert (C : s |= V293_time_cell true ticks bt (Vint32 clock) ** Atrue).
        { unfold V293_time_payload in H. clear -H. sep auto. }
        destruct (V293_time_cell_read true ticks bt clock Atrue s C) as [Value Ty].
        split; [exact Value | split;[exact Ty | discriminate]].
Qed.

Theorem V293_OSTimeSet_body_hoare : forall Spec sd li I tid aop enabled ir si ci
    now ticks saved bn bt bs old new save frame,
  (gettopis si <= INUM)%nat -> GoodFrm frame -> (frame ==> CurLINV li tid) ->
  InfRules Spec sd li I
    (fun result => [| result = None |] **
      (<||aop||> ** OS[ir,enabled,si,ci] **
        V293_time_payload now ticks saved bn bt bs new (Vint32 new) (Vint32 Int.zero) frame))
    Afalse
    (<||aop||> ** OS[ir,enabled,si,ci] **
      V293_time_payload now ticks saved bn bt bs old (Vint32 new) save frame)
    (V293_TimeSet_body now ticks saved) Afalse tid.
Proof.
  intros Spec sd li I tid aop enabled ir si ci now ticks saved bn bt bs old new save frame Bound GF Inv.
  unfold V293_TimeSet_body.
  eapply seq_rule with (p':=<||aop||> ** OS[ir,enabled,si,ci] **
      V293_time_payload now ticks saved bn bt bs old (Vint32 new) (Vint32 Int.zero) frame).
  - eapply conseq_rule; [ | | apply (V293_time_zero _ _ _ _ _ _ _ aop
      (V293_time_cell false now bn (Vint32 old) **
        (V293_time_cell true ticks bt (Vint32 new) ** (frame ** OS[ir,enabled,si,ci]))) saved bs save)].
    + unfold V293_time_payload. intros s H;sep auto.
    + unfold V293_time_payload. intros s H;sep auto.
    + eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_r.
      eapply V293_star_CurLINV_l. exact Inv.
  - eapply seq_rule with (p':=<||aop||> ** OS[ir,enabled,si,ci] **
        V293_time_payload now ticks saved bn bt bs new (Vint32 new) (Vint32 Int.zero) frame).
    + eapply V293_time_critical; try exact Bound;
        try (apply V293_time_payload_good;exact GF);
        try (apply V293_time_payload_inv;exact Inv).
      intro extra. eapply conseq_rule; [ | | apply (V293_time_copy _ _ _ _ _ _ _ aop
        (V293_time_cell true saved bs (Vint32 Int.zero) ** (frame ** extra))
        false now bn (Vint32 old) true ticks bt new)].
      * unfold V293_time_payload. intros s H;sep auto.
      * unfold V293_time_payload. intros s H;sep auto.
      * eapply V293_star_CurLINV_r. eapply V293_star_CurLINV_l. exact Inv.
    + apply ret_rule. intros s FinalOwned.
      apply astar_l_apure_intro; [exact FinalOwned | reflexivity].
Qed.

Print Assumptions V293_OSTimeGet_body_hoare.
Print Assumptions V293_OSTimeSet_body_hoare.
