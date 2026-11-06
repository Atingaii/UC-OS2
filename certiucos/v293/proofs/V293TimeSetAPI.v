(* Actual framework API builders for the unchanged shared OSTimeSet body.
   Global-name knowledge comes from the local invariant, not clock ownership.
   The framework API rule covers allocated argument/local resources; no new
   independent concrete call-to-return execution trace is claimed here. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_TimeSet_function now ticks saved : function :=
  (Tvoid,dcons ticks Tint32 dnil,dcons saved Tint32 dnil,
    V293_TimeSet_body now ticks saved).
Definition V293_TimeSet_api : osapi :=
  (fun vl => match vl with
    | (Vint32 n)::nil => V293_time_set_action n
    | _ => END None
    end,(Tvoid,Tint32::nil)).
Definition V293_TimeSet_api_unit (fset : fid) now ticks saved : progunit :=
  fun f => if Z.eq_dec f fset then Some (V293_TimeSet_function now ticks saved) else None.
Definition V293_TimeSet_api_spec (fset : fid) : osapispec :=
  fun f => if Z.eq_dec f fset then Some V293_TimeSet_api else None.
Definition V293_time_api_domain ticks saved :=
  A_dom_lenv ((ticks,Tint32)::(saved,Tint32)::nil).
Definition V293_time_api_frame li tid lg ticks saved :=
  p_local li tid lg ** V293_time_api_domain ticks saved.

Lemma V293_time_api_local_good : forall p,
  GoodLocalInvAsrt p -> GoodFrm p.
Proof.
  induction p; simpl;intros Good;try exact I;try contradiction;
    try (destruct Good;split;auto);auto.
Qed.
Lemma V293_time_api_frame_good : forall li tid lg ticks saved,
  GoodLInvAsrt li -> GoodFrm (V293_time_api_frame li tid lg ticks saved).
Proof.
  intros. unfold V293_time_api_frame,p_local,LINV,CurTid,Agvarmapsto,Aptrmapsto.
  simpl. repeat split;try exact I. apply V293_time_api_local_good. exact (proj1 (H tid lg)).
Qed.
Lemma V293_time_api_frame_local : forall li tid lg ticks saved,
  V293_time_api_frame li tid lg ticks saved ==> CurLINV li tid.
Proof.
  intros li tid lg ticks saved s H. unfold V293_time_api_frame,p_local,CurLINV in *.
  exists lg. sep auto.
Qed.

Lemma V293_time_api_bind : forall now ticks saved bn,
  now <> ticks -> now <> saved ->
  Agvarenv now Tint32 (bn,0%Z) ** V293_time_api_domain ticks saved ==>
  V293_time_binding false now bn ** V293_time_api_domain ticks saved.
Proof.
  intros now ticks saved bn NT NS s H.
  unfold V293_time_api_domain in *. apply astar_comm in H.
  apply astar_l_adomlenv_elim in H. destruct H as [Dom G].
  assert (NotLocal : ~ indom (getlenv s) now).
  { intros [[b tp] E].
    pose proof (proj2 (Dom now tp) (ex_intro _ b E)) as Found.
    simpl in Found. destruct Found as [Eq | [Eq | F]];try contradiction;inversion Eq;congruence. }
  apply astar_comm. apply astar_l_adomlenv_intro;[ | exact Dom].
  unfold V293_time_binding,V293_counter_bindings. split;[exact G | ].
  apply anotinlenv_intro;[ | exact NotLocal].
  apply agvarenv_elim in G. exact (proj2 G).
Qed.

Lemma V293_time_api_entry : forall now ticks saved bn li tid lg n,
  now <> ticks -> now <> saved ->
  (p_local li tid lg ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li tid lg) ->
  ((<||V293_time_set_action n||> ** p_local li tid lg **
      ((LV ticks @ Tint32 |-> Vint32 n) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved) ==>
  EX bt : block, EX bs : block, EX save : val,
    <||V293_time_set_action n||> ** OS[empisr,true,nil,nil] **
      V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) save
        (V293_time_api_frame li tid lg ticks saved).
Proof.
  intros now ticks saved bn li tid lg n NT NS Globals s H.
  assert (Split : s |= (p_local li tid lg ** V293_time_api_domain ticks saved) **
    (<||V293_time_set_action n||> **
      ((LV ticks @ Tint32 |-> Vint32 n) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr)) by (sep auto).
  clear H.
  eapply astar_mono in Split.
  2: { apply astar_mono;[exact Globals | intros st H;exact H]. }
  2: { intros st H;exact H. }
  assert (Names : s |= (Agvarenv now Tint32 (bn,0%Z) ** V293_time_api_domain ticks saved) **
    (p_local li tid lg ** (<||V293_time_set_action n||> **
      ((LV ticks @ Tint32 |-> Vint32 n) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr))) by (sep auto).
  clear Split.
  eapply astar_mono in Names;[ | apply V293_time_api_bind;assumption | intros st H;exact H].
  unfold Alvarmapsto,Alvarenv' in Names.
  unfold V293_time_shared_locals,V293_time_cell,V293_time_api_frame.
  cbn [V293_time_binding]. sep auto.
Qed.

Lemma V293_time_api_release_cell : forall x b v,
  V293_time_cell true x b v ==> EX old : val, LV x @ Tint32 |-> old.
Proof.
  intros x b v s H. exists v. unfold Alvarmapsto,Alvarenv'. exists b. exact H.
Qed.

Lemma V293_time_api_return : forall now ticks saved bn bt bs li tid lg n result,
  [| result=None |] ** (<||END None||> ** OS[empisr,true,nil,nil] **
    V293_time_shared_locals now ticks saved bn bt bs (Vint32 n) (Vint32 Int.zero)
      (V293_time_api_frame li tid lg ticks saved)) ==>
  ((<||spec_done result||> ** p_local li tid lg **
    ((EX v : val, LV ticks @ Tint32 |-> v) ** ((EX v : val, LV saved @ Tint32 |-> v) ** Aemp)) **
    Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved).
Proof.
  intros now ticks saved bn bt bs li tid lg n result s H.
  apply astar_l_apure_elim in H. destruct H as [E H]. subst result.
  unfold V293_time_shared_locals,V293_time_api_frame in H.
  (* Name-only resource is duplicable/erasable, never a discarded clock byte. *)
  assert (Pack : s |= V293_time_binding false now bn **
    ((<||END None||> ** p_local li tid lg **
      (V293_time_cell true ticks bt (Vint32 n) **
        (V293_time_cell true saved bs (Vint32 Int.zero) ** Aemp)) **
      Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** V293_time_api_domain ticks saved)) by (sep auto).
  clear H. destruct s as [[[[[[ge le] M] ir] aux] O] op]. apply sat_split in Pack.
  destruct Pack as (m1 & m2 & o1 & o2 & JM & JO & Name & Rest).
  destruct Name as [[b [GE [Eq [EM EO]]]] _].
  change (m1=emp) in EM. change (o1=emp) in EO. subst m1 o1.
  apply map_join_comm in JM. apply map_join_emp' in JM.
  apply map_join_comm in JO. apply map_join_emp' in JO. subst m2 o2.
  assert (Cells : (ge,le,M,ir,aux,O,op) |=
    (V293_time_cell true ticks bt (Vint32 n) ** V293_time_cell true saved bs (Vint32 Int.zero)) **
      (<||END None||> ** p_local li tid lg ** Aie true ** Ais nil ** Acs nil ** Aisr empisr **
        V293_time_api_domain ticks saved)) by (sep auto).
  clear Rest. eapply astar_mono in Cells.
  2: { apply astar_mono;apply V293_time_api_release_cell. }
  2: { intros st H;exact H. }
  sep auto.
Qed.

Lemma V293_time_api_args : forall ticks vl,
  dl_vl_match (dcons ticks Tint32 dnil) (rev vl)=true ->
  exists n, vl=(Vint32 n)::nil.
Proof.
  intros ticks vl Match. destruct (rev vl) as [ | v rest] eqn:E;[discriminate | ].
  destruct v;try discriminate. destruct rest;try discriminate.
  apply (f_equal (@rev val)) in E. rewrite rev_involutive in E.
  exists i. exact E.
Qed.

(* The stable interface uses the builders themselves. It quantifies over all
   input lists and their real builder-success equations, not a renamed subset. *)
Theorem V293_TimeSet_api_contract : forall P f Spec sd li lg tid vl pre post now ticks saved bn,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  P f=Some (V293_TimeSet_function now ticks saved) ->
  Some pre=BuildPreA' P f V293_TimeSet_api vl li tid lg ->
  Some post=BuildRetA' P f V293_TimeSet_api vl li tid lg ->
  InfRules Spec sd li (V293_time_shared_inv bn) post Afalse pre
    (V293_TimeSet_body now ticks saved) Afalse tid.
Proof.
  intros P f Spec sd li lg tid vl pre post now ticks saved bn TS NT NS Good NA Globals Code Pre Post.
  unfold BuildPreA' in Pre. rewrite Code in Pre.
  cbn [V293_TimeSet_function] in Pre.
  destruct (dl_vl_match (dcons ticks Tint32 dnil) (rev vl)) eqn:Match;[ | discriminate].
  destruct (V293_time_api_args ticks vl Match) as [n E]. subst vl.
  assert (TSb : Zeq_bool ticks saved=false).
  { destruct (Zeq_bool ticks saved) eqn:E;[apply Zeq_bool_eq in E;contradiction | reflexivity]. }
  cbn [dladd revlcons buildp good_decllist in_decllist] in Pre. rewrite TSb in Pre.
  cbn [V293_TimeSet_api fst] in Pre. inversion Pre;subst pre.
  unfold BuildRetA' in Post. rewrite Code in Post.
  cbn [V293_TimeSet_function dladd revlcons buildq good_decllist in_decllist] in Post. rewrite TSb in Post.
  cbn in Post. inversion Post;subst post.
  eapply conseq_rule;[apply (V293_time_api_entry now ticks saved bn li tid lg n NT NS (Globals tid lg)) | intros s H;exact H | ].
  apply ex_intro_rule. intro bt. apply ex_intro_rule. intro bs. apply ex_intro_rule. intro save.
  eapply r_conseq_rule.
  3: { apply V293_OSTimeSet_shared_body;
    [exact NA | reflexivity | cbn;lia | apply V293_time_api_frame_good;exact Good | apply V293_time_api_frame_local]. }
  - intro result. apply V293_time_api_return.
  - intros s H;exact H.
Qed.

Lemma V293_TimeSet_api_domains : forall fset now ticks saved,
  EqDomAPI (V293_TimeSet_api_unit fset now ticks saved) (V293_TimeSet_api_spec fset).
Proof.
  intros. split.
  - intros f. unfold V293_TimeSet_api_unit,V293_TimeSet_api_spec.
    destruct (Z.eq_dec f fset);split;intros [x H];try discriminate;eexists;reflexivity.
  - intros f fd fs Code Spec. unfold V293_TimeSet_api_unit in Code.
    unfold V293_TimeSet_api_spec in Spec. destruct (Z.eq_dec f fset);try discriminate.
    inversion Code;inversion Spec;subst. split;simpl;auto.
Qed.

Theorem V293_TimeSet_api_rule : forall fset now ticks saved bn Spec sd li lg,
  ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==> Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  APIRule (V293_TimeSet_api_unit fset now ticks saved) (V293_TimeSet_api_spec fset)
    Spec sd li (V293_time_shared_inv bn) lg.
Proof.
  intros fset now ticks saved bn Spec sd li lg TS NT NS Good NA Globals.
  apply api_rule;[apply V293_TimeSet_api_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_TimeSet_api_spec in API. destruct (Z.eq_dec f fset);try discriminate.
  inversion API;subst ab ft.
  exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
  exists (V293_TimeSet_body now ticks saved). split.
  - unfold V293_TimeSet_api_unit. destruct (Z.eq_dec f fset);[reflexivity | contradiction].
  - eapply V293_TimeSet_api_contract;try eassumption.
    unfold V293_TimeSet_api_unit. destruct (Z.eq_dec f fset);[reflexivity | contradiction].
Qed.

Print Assumptions V293_time_api_entry.
Print Assumptions V293_TimeSet_api_contract.
Print Assumptions V293_TimeSet_api_rule.
