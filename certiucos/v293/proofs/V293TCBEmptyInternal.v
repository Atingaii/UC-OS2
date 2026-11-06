(* Exact framework builders for the empty-free-list domain of OS_TCBInit.
   All seven parameter cells and both locals are returned to buildq. This
   restricted contract is not the nonempty contract or a WFIFun theorem. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import Coq.Lists.List.
Import ListNotations.

Definition V293_tcb_internal_declarations :=
 revlcons V293_TCBInit_parameters V293_TCBInit_locals.
Definition V293_tcb_internal_domain :=
 A_dom_lenv (getlenvdom V293_tcb_internal_declarations).
Definition V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 :=
 LV 107%Z @ Tint16 |-> v7 ** (LV 106%Z @ Tptr Tvoid |-> v6 **
 (LV 105%Z @ Tint32 |-> v5 ** (LV 104%Z @ Tint16 |-> v4 **
 (LV 103%Z @ Tptr Tint32 |-> v3 ** (LV 102%Z @ Tptr Tint32 |-> v2 **
 (LV 101%Z @ Tint8 |-> v1 ** Aemp)))))).
Definition V293_tcb_internal_locals :=
 (EX pc : val, LV 108%Z @ Tptr V293_tcb_type |-> pc) **
 ((EX cpu : val, LV 109%Z @ Tint32 |-> cpu) ** Aemp).
Definition V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 :=
 LV 107%Z @ Tint16 |-> v7 ** (LV 106%Z @ Tptr Tvoid |-> v6 **
 (LV 105%Z @ Tint32 |-> v5 ** (LV 104%Z @ Tint16 |-> v4 **
 (LV 103%Z @ Tptr Tint32 |-> v3 ** (LV 102%Z @ Tptr Tint32 |-> v2 **
 (LV 101%Z @ Tint8 |-> v1 ** V293_tcb_internal_locals)))))).
Definition V293_tcb_internal_post_cells :=
 (EX v : val, LV 107%Z @ Tint16 |-> v) **
 ((EX v : val, LV 106%Z @ Tptr Tvoid |-> v) **
 ((EX v : val, LV 105%Z @ Tint32 |-> v) **
 ((EX v : val, LV 104%Z @ Tint16 |-> v) **
 ((EX v : val, LV 103%Z @ Tptr Tint32 |-> v) **
 ((EX v : val, LV 102%Z @ Tptr Tint32 |-> v) **
 ((EX v : val, LV 101%Z @ Tint8 |-> v) ** V293_tcb_internal_locals)))))).

Lemma V293_tcb_internal_buildp : forall v1 v2 v3 v4 v5 v6 v7,
 buildp V293_tcb_internal_declarations [v7;v6;v5;v4;v3;v2;v1] =
 Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7).
Proof. reflexivity. Qed.
Lemma V293_tcb_internal_buildq :
 buildq V293_tcb_internal_declarations = Some V293_tcb_internal_post_cells.
Proof. reflexivity. Qed.
Lemma V293_tcb_internal_parameter_frame : forall v1 v2 v3 v4 v5 v6 v7,
 GoodFrm (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ** V293_tcb_internal_domain).
Proof.
 intros. cbn [V293_tcb_internal_parameters V293_tcb_internal_domain GoodFrm Alvarmapsto Alvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.

(* This is the actual declaration domain, not an independent no-shadow oracle. *)
Lemma V293_tcb_internal_no_shadow : forall le,
 eq_dom_env le (getlenvdom V293_tcb_internal_declarations) -> get le 91%Z=None.
Proof.
 intros le Domain. destruct (get le 91%Z) as [[b tp] | ] eqn:E;[ |reflexivity].
 exfalso. pose proof (proj2(Domain 91%Z tp)(ex_intro _ b E)) as Bad.
 cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals
 revlcons getlenvdom] in Bad. repeat destruct Bad as [Bad|Bad];try discriminate;contradiction.
Qed.

Definition V293_tcb_empty_external bf R aop isr is cs :=
 Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z) **
 (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull **
 (<||aop||> ** OS[isr,false,is,cs] ** R)).
Lemma V293_tcb_empty_external_good : forall bf R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_tcb_empty_external bf R aop isr is cs).
Proof. intros. cbn [V293_tcb_empty_external GoodFunAsrt]. tauto. Qed.
Definition V293_tcb_empty_fpre bf R aop isr is cs (good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => @mkfunasrt (V293_tcb_empty_external bf R aop isr is cs)
 (V293_tcb_empty_external_good bf R aop isr is cs good).
Definition V293_tcb_empty_fpost bf R aop isr is cs (good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_empty_external bf R aop isr is cs)
 (conj I (V293_tcb_empty_external_good bf R aop isr is cs good)).

Definition V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R :=
 V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ** (V293_tcb_internal_domain ** R).
Lemma V293_tcb_empty_internal_frame_good : forall v1 v2 v3 v4 v5 v6 v7 R,
 GoodFrm R -> GoodFrm(V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R).
Proof.
 intros. unfold V293_tcb_empty_internal_frame.
 pose proof(V293_tcb_internal_parameter_frame v1 v2 v3 v4 v5 v6 v7).
 cbn [GoodFrm] in *. tauto.
Qed.
Lemma V293_tcb_empty_internal_frame_linv : forall v1 v2 v3 v4 v5 v6 v7 R li tid,
 (R ==> CurLINV li tid) ->
 V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R ==> CurLINV li tid.
Proof. intros v1 v2 v3 v4 v5 v6 v7 R li tid HR. unfold V293_tcb_empty_internal_frame. apply V293_star_CurLINV_r. apply V293_star_CurLINV_r. assumption. Qed.

Lemma V293_tcb_empty_internal_unpack : forall v1 v2 v3 v4 v5 v6 v7 Q,
 V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 ** Q ==>
 EX pc : val, EX cpu : val, EX bp : block, EX bc : block,
 (Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** (Amapsto (bc,0%Z) Tint32 true cpu **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ** Q))))).
Proof.
 intros v1 v2 v3 v4 v5 v6 v7 Q. unfold V293_tcb_internal_pre_cells,V293_tcb_internal_locals,
 V293_tcb_internal_parameters,Alvarmapsto,Alvarenv',Aptrmapsto. sep auto.
Qed.

Lemma V293_tcb_empty_internal_bindings : forall bf bp bc,
 (Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z))) **
 V293_tcb_internal_domain ==>
 V293_tcb_empty_bindings bf bp bc ** V293_tcb_internal_domain.
Proof.
 intros bf bp bc s H. unfold V293_tcb_internal_domain in *.
 apply astar_comm in H. apply astar_l_adomlenv_elim in H. destruct H as [Domain H].
 apply astar_comm. apply astar_l_adomlenv_intro;[ |exact Domain].
 assert (N : ~ indom (getlenv s) 91%Z).
 { intros [v E]. rewrite (V293_tcb_internal_no_shadow _ Domain) in E. discriminate. }
 unfold V293_tcb_empty_bindings. sep auto.
 split;[apply alvarenv_intro;[exact H|exact H0]| ].
 split;[apply alvarenv_intro;[exact H|exact H1]| ].
 split;[apply agvarenv_intro;[exact H|exact H2]| ].
 apply anotinlenv_intro;[exact H|exact N].
Qed.

Lemma V293_tcb_empty_internal_entry : forall bf bp bc pc cpu v1 v2 v3 v4 v5 v6 v7 R aop isr is cs,
 Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** (Amapsto (bc,0%Z) Tint32 true cpu **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (V293_tcb_empty_external bf R aop isr is cs ** V293_tcb_internal_domain))))) ==>
 V293_tcb_empty_state bf bp bc pc cpu
 (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs.
Proof.
 intros bf bp bc pc cpu v1 v2 v3 v4 v5 v6 v7 R aop isr is cs s HS. unfold V293_tcb_empty_external in HS.
 assert (Reordered : s |=
 ((Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z))) **
 V293_tcb_internal_domain) **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Amapsto (bc,0%Z) Tint32 true cpu **
 (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull **
 (<||aop||> ** OS[isr,false,is,cs] **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ** R)))))).
 { clear -HS. sep auto. }
 eapply astar_mono in Reordered.
 2: { apply V293_tcb_empty_internal_bindings. }
 2: { intros st H;exact H. }
 unfold V293_tcb_empty_state,V293_tcb_empty_resources,V293_tcb_empty_internal_frame.
 clear -Reordered. sep auto.
Qed.

Definition V293_tcb_internal_parameter_post :=
 (EX v : val, LV 107%Z @ Tint16 |-> v) **
 ((EX v : val, LV 106%Z @ Tptr Tvoid |-> v) **
 ((EX v : val, LV 105%Z @ Tint32 |-> v) **
 ((EX v : val, LV 104%Z @ Tint16 |-> v) **
 ((EX v : val, LV 103%Z @ Tptr Tint32 |-> v) **
 ((EX v : val, LV 102%Z @ Tptr Tint32 |-> v) **
 ((EX v : val, LV 101%Z @ Tint8 |-> v) ** Aemp)))))).
Lemma V293_tcb_internal_parameter_return : forall v1 v2 v3 v4 v5 v6 v7,
 V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 ==> V293_tcb_internal_parameter_post.
Proof.
 intros v1 v2 v3 v4 v5 v6 v7.
 unfold V293_tcb_internal_parameters,V293_tcb_internal_parameter_post.
 repeat apply astar_mono;intros s H;try (eexists;exact H);exact H.
Qed.
Lemma V293_tcb_internal_local_return : forall x tp b v,
 Alvarenv x tp (b,0%Z) ** Amapsto (b,0%Z) tp true v ==>
 EX v' : val, LV x @ tp |-> v'.
Proof.
 intros x tp b v s H. exists v. unfold Alvarmapsto,Alvarenv',Aptrmapsto.
 exists b. exact H.
Qed.

Lemma V293_tcb_empty_internal_return_bindings : forall bf bp bc,
 V293_tcb_empty_bindings bf bp bc ==>
 Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 (Alvarenv 109%Z Tint32 (bc,0%Z) ** Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z)).
Proof.
 intros bf bp bc s [P [C [G N]]].
 apply alvarenv_elim in P. apply alvarenv_elim in C.
 apply astar_l_alvarenv_intro;[ |exact (proj1 P)].
 apply astar_l_alvarenv_intro;[exact G|exact (proj1 C)].
Qed.

Lemma V293_tcb_empty_internal_exit : forall bf bp bc v1 v2 v3 v4 v5 v6 v7 R aop isr is cs result,
 V293_tcb_empty_post bf bp bc
 (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs result ==>
 V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_empty_external bf R aop isr is cs) **
 V293_tcb_internal_domain.
Proof.
 intros bf bp bc v1 v2 v3 v4 v5 v6 v7 R aop isr is cs result s H.
 unfold V293_tcb_empty_post in H. apply astar_l_apure_elim in H.
 destruct H as [Code H].
 unfold V293_tcb_empty_state,V293_tcb_empty_resources,V293_tcb_empty_internal_frame in H.
 assert (EnvFrame : s |= V293_tcb_empty_bindings bf bp bc **
 (<||aop||> ** OS[isr,false,is,cs] **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull **
 (Amapsto (bc,0%Z) Tint32 true (Vint32 Int.zero) **
 (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull **
 (V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (V293_tcb_internal_domain ** R))))))).
 { clear -H. sep auto. }
 eapply astar_mono in EnvFrame.
 2: { apply V293_tcb_empty_internal_return_bindings. }
 2: { intros st HS;exact HS. }
 clear H. rename EnvFrame into H.
 assert (Reordered : s |= V293_tcb_internal_parameters v1 v2 v3 v4 v5 v6 v7 **
 (((Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) **
 Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull) **
 ((Alvarenv 109%Z Tint32 (bc,0%Z) **
 Amapsto (bc,0%Z) Tint32 true (Vint32 Int.zero)) ** Aemp)) **
 (V293_tcb_empty_external bf R aop isr is cs ** V293_tcb_internal_domain))).
 { unfold V293_tcb_empty_external. clear -H. sep auto. }
 eapply astar_mono in Reordered.
 2: { apply V293_tcb_internal_parameter_return. }
 2: { apply astar_mono;[ |intros st HS;exact HS].
      apply astar_mono;[apply V293_tcb_internal_local_return| ].
      apply astar_mono;[apply V293_tcb_internal_local_return|intros st HS;exact HS]. }
 unfold V293_tcb_internal_parameter_post,V293_tcb_internal_post_cells,V293_tcb_internal_locals in *.
 clear -Reordered Code. sep auto.

Qed.

Theorem V293_OS_TCBInit_empty_internal_resources : forall Spec sd li I tid hi hc bf R aop isr is cs
 v1 v2 v3 v4 v5 v6 v7,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I
 (fun result => V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_empty_external bf R aop isr is cs) **
 V293_tcb_internal_domain) Afalse
 (V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 V293_tcb_empty_external bf R aop isr is cs ** V293_tcb_internal_domain)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc bf R aop isr is cs v1 v2 v3 v4 v5 v6 v7 Frame HR.
 eapply conseq_rule.
 - intros s H. exact (V293_tcb_empty_internal_unpack v1 v2 v3 v4 v5 v6 v7
   (V293_tcb_empty_external bf R aop isr is cs ** V293_tcb_internal_domain) s H).
 - intros s H;exact H.
 - apply ex_intro_rule. intro pc. apply ex_intro_rule. intro cpu.
   apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   eapply conseq_rule;[apply V293_tcb_empty_internal_entry|intros s H;exact H| ].
   eapply r_conseq_rule with (r:=V293_tcb_empty_post bf bp bc
    (V293_tcb_empty_internal_frame v1 v2 v3 v4 v5 v6 v7 R) aop isr is cs) (ri:=Afalse).
   + intro result. apply V293_tcb_empty_internal_exit.
   + intros s H;exact H.
   + apply V293_OS_TCBInit_empty_body_hoare.
     * apply V293_tcb_empty_internal_frame_good;assumption.
     * apply V293_tcb_empty_internal_frame_linv;assumption.
Qed.

(* The public interface uses the real builders, with arbitrary well-typed C
   arguments and arbitrary logic arguments. Caller-visible specs name no local
   identifier or local address. Success on a nonempty list is not covered. *)
Theorem V293_OS_TCBInit_empty_internal_contract : forall P f Spec sd li I tid hi hc
 bf R aop isr is cs (good:GoodFunAsrt R) vl lg pre post,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_empty_fpre bf R aop isr is cs good) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_empty_fpost bf R aop isr is cs good) tid ->
 InfRules Spec sd li I post Afalse pre (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros P f Spec sd li I tid hi hc bf R aop isr is cs good vl lg pre post Frame HR Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre.
 cbn [V293_TCBInit_function] in Pre.
 destruct (dl_vl_match V293_TCBInit_parameters (rev vl)) eqn:Typed;[ |discriminate].
 pose proof(dl_vl_match_dv_same_length _ _ Typed) as Length.
 rewrite rev_length in Length. cbn [V293_TCBInit_parameters decllen] in Length.
 destruct vl as [ |v7 vl];[discriminate Length| ].
 destruct vl as [ |v6 vl];[discriminate Length| ].
 destruct vl as [ |v5 vl];[discriminate Length| ].
 destruct vl as [ |v4 vl];[discriminate Length| ].
 destruct vl as [ |v3 vl];[discriminate Length| ].
 destruct vl as [ |v2 vl];[discriminate Length| ].
 destruct vl as [ |v1 vl];[discriminate Length| ].
 destruct vl;[ |discriminate Length].
 fold V293_tcb_internal_declarations in Pre.
 rewrite V293_tcb_internal_buildp in Pre.
 change (Some pre=Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 V293_tcb_empty_external bf R aop isr is cs ** V293_tcb_internal_domain)) in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change (Some post=Some(fun result => V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] ** V293_tcb_empty_external bf R aop isr is cs) **
 V293_tcb_internal_domain)) in Post.
 inversion Post;subst post.
 apply V293_OS_TCBInit_empty_internal_resources;assumption.
Qed.
