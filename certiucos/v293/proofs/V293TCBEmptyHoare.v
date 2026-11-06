(* The actual complete body, restricted to the empty-free-list case and an
   already disabled interrupt state. Hooks remain in the syntax but unreachable.
   This is a body Hoare theorem, not WFIFun or a call-allocation/free theorem. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import Coq.Lists.List.
Import ListNotations.

Definition V293_tcb_empty_bindings bf bp bc :=
 Alvarenv 108%Z (Tptr V293_tcb_type) (bp,0%Z) //\\
 Alvarenv 109%Z Tint32 (bc,0%Z) //\\
 Agvarenv 91%Z (Tptr V293_tcb_type) (bf,0%Z) //\\ A_notin_lenv 91%Z.
Definition V293_tcb_empty_resources bf bp bc pc cpu R :=
 V293_tcb_empty_bindings bf bp bc **
 (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
 (Amapsto (bc,0%Z) Tint32 true cpu **
 (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** R))).
Definition V293_tcb_empty_state bf bp bc pc cpu R aop isr is cs :=
 <||aop||> ** OS[isr,false,is,cs] **
 V293_tcb_empty_resources bf bp bc pc cpu R.
Definition V293_tcb_empty_post bf bp bc R aop isr is cs result :=
 [|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_empty_state bf bp bc Vnull (Vint32 Int.zero) R aop isr is cs.

Lemma V293_tcb_empty_good_frame : forall bf bp bc pc cpu R,
 GoodFrm R -> GoodFrm (V293_tcb_empty_resources bf bp bc pc cpu R).
Proof. intros. cbn [V293_tcb_empty_resources V293_tcb_empty_bindings GoodFrm]. tauto. Qed.
Lemma V293_tcb_empty_env : forall bf bp bc s,
 s |= V293_tcb_empty_bindings bf bp bc ** Atrue ->
 get (getlenv s) 108%Z=Some(bp,Tptr V293_tcb_type) /\
 get (getlenv s) 109%Z=Some(bc,Tint32) /\
 get (getlenv s) 91%Z=None /\
 get (getgenv s) 91%Z=Some(bf,Tptr V293_tcb_type).
Proof.
 intros bf bp bc s HS. eapply V293_star_env_l;[ |exact HS].
 intros st [LP [LC [GF [NF _]]]].
 destruct LP as [b [E [B _]]]. inversion B;subst b.
 destruct LC as [b [E' [B2 _]]]. inversion B2;subst b.
 destruct GF as [b [G [B3 _]]]. inversion B3;subst b.
 repeat split;try assumption.
 destruct (get (getlenv st) 91%Z) eqn:N;[ |reflexivity].
 exfalso. apply NF. exists p. exact N.
Qed.
Lemma V293_tcb_empty_free_eval : forall bf bp bc pc cpu R s,
 s |= V293_tcb_empty_resources bf bp bc pc cpu R ->
 evalval (evar 91%Z) (getsmem s)=Some Vnull /\
 evaltype (evar 91%Z) (getsmem s)=Some(Tptr V293_tcb_type).
Proof.
 intros bf bp bc pc cpu R s HS.
 assert (B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue).
 { unfold V293_tcb_empty_state,V293_tcb_empty_resources in HS. clear -HS. sep auto. }
 destruct (V293_tcb_empty_env _ _ _ _ B) as (_&_&N&G).
 assert (L:load (Tptr V293_tcb_type) (getmem s) (bf,0%Z)=Some Vnull).
 { eapply V293_star_load_l with (p:=Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull) (q:=Atrue).
   - intros st [H _]. eapply mapstoval_load;[reflexivity|exact H].
   - change (s |= Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** Atrue).
     unfold V293_tcb_empty_state,V293_tcb_empty_resources in HS. clear -HS. sep auto. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getlenv getgenv getmem getsmem get_smem get_lenv get_genv get_mem] in *.
 cbn [evalval evaltype get_lenv get_genv get_mem]. cbv delta [env var memory.ident Modules.ident] in *. rewrite N,G,L. split;reflexivity.
Qed.
Lemma V293_tcb_empty_guard_eval : forall bf bp bc cpu R aop isr is cs s,
 s |= V293_tcb_empty_state bf bp bc Vnull cpu R aop isr is cs ->
 evalval (eunop oppsite (V293_task_prio_null_test(evar 108%Z))) (getsmem s)=Some(Vint32 Int.zero) /\
 evaltype (eunop oppsite (V293_task_prio_null_test(evar 108%Z))) (getsmem s)=Some Tint32.
Proof.
 intros bf bp bc cpu R aop isr is cs s HS.
 assert (B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue).
 { unfold V293_tcb_empty_state,V293_tcb_empty_resources in HS. clear -HS. sep auto. }
 destruct (V293_tcb_empty_env _ _ _ _ B) as (P&_).
 assert (L:load (Tptr V293_tcb_type) (getmem s) (bp,0%Z)=Some Vnull).
 { eapply V293_star_load_l with (p:=Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull) (q:=Atrue).
   - intros st [H _]. eapply mapstoval_load;[reflexivity|exact H].
   - change (s |= Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull ** Atrue).
     unfold V293_tcb_empty_state,V293_tcb_empty_resources in HS. clear -HS. sep auto. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getlenv getmem getsmem get_smem get_lenv get_genv get_mem] in *.
 cbn [V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem].
 cbv delta [env var memory.ident Modules.ident] in *. rewrite P,L. split;reflexivity.
Qed.

Lemma V293_tcb_empty_cpu_hoare : forall Spec sd li I r ri tid bf bp bc pc cpu R aop isr is cs,
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_empty_state bf bp bc pc cpu R aop isr is cs)
 (sassign (evar 109%Z) (econst32 Int.zero))
 (V293_tcb_empty_state bf bp bc pc (Vint32 Int.zero) R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu R aop isr is cs HR.
 unfold V293_tcb_empty_state,V293_tcb_empty_resources. eapply conseq_rule with
 (p:=<||aop||> ** (OS[isr,false,is,cs] **
  (V293_tcb_empty_bindings bf bp bc **
  (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
  (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** R)))) **
  Amapsto (bc,0%Z) Tint32 true cpu)
 (q:=<||aop||> ** (OS[isr,false,is,cs] **
  (V293_tcb_empty_bindings bf bp bc **
  (Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc **
  (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** R)))) **
  Amapsto (bc,0%Z) Tint32 true (Vint32 Int.zero)).
 - intros s HS. clear -HS. sep auto.
 - intros s HS. clear -HS. sep auto.
 - eapply assign_rule with (tp2:=Tint32) (l:=(bc,Int.zero)).
   + apply eq_int;auto.
   + intros s HS.
     assert (B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue) by (clear -HS;sep auto).
     destruct (V293_tcb_empty_env _ _ _ _ B) as (_&C&_).
     destruct s as [[[[[[ge le] M] ir] aux] O] op].
     change (get le 109%Z=Some(bc,Tint32)) in C. cbn [sat getsmem evaladdr evaltype evalval get_smem get_lenv].
     cbv delta [env var memory.ident Modules.ident] in *. rewrite C. repeat split;try reflexivity;discriminate.
   + apply V293_star_CurLINV_l.
     repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_tcb_empty_pointer_hoare : forall Spec sd li I r ri tid bf bp bc pc cpu R aop isr is cs,
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_empty_state bf bp bc pc cpu R aop isr is cs)
 (sassign (evar 108%Z) (evar 91%Z))
 (V293_tcb_empty_state bf bp bc Vnull cpu R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid bf bp bc pc cpu R aop isr is cs HR.
 unfold V293_tcb_empty_state,V293_tcb_empty_resources. eapply conseq_rule with
 (p:=<||aop||> ** (OS[isr,false,is,cs] **
  (V293_tcb_empty_bindings bf bp bc **
  (Amapsto (bc,0%Z) Tint32 true cpu **
  (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** R)))) **
  Amapsto (bp,0%Z) (Tptr V293_tcb_type) true pc)
 (q:=<||aop||> ** (OS[isr,false,is,cs] **
  (V293_tcb_empty_bindings bf bp bc **
  (Amapsto (bc,0%Z) Tint32 true cpu **
  (Amapsto (bf,0%Z) (Tptr V293_tcb_type) false Vnull ** R)))) **
  Amapsto (bp,0%Z) (Tptr V293_tcb_type) true Vnull).
 - intros s HS. clear -HS. sep auto.
 - intros s HS. clear -HS. sep auto.
 - eapply assign_rule with (tp2:=Tptr V293_tcb_type) (l:=(bp,Int.zero)).
   + apply eq_vptr. eexists. eexists. split;reflexivity.
   + intros s HS.
     assert (B:s |= V293_tcb_empty_bindings bf bp bc ** Atrue) by (clear -HS;sep auto).
     destruct (V293_tcb_empty_env _ _ _ _ B) as (P&_).
     assert (K:s |= V293_tcb_empty_resources bf bp bc pc cpu R).
     { unfold V293_tcb_empty_state,V293_tcb_empty_resources. clear -HS. sep auto. }
     destruct (V293_tcb_empty_free_eval _ _ _ _ _ _ _ K) as (V&T).
     split.
     * destruct s as [[[[[[ge le] M] ir] aux] O] op].
       change (get le 108%Z=Some(bp,Tptr V293_tcb_type)) in P. cbn [sat getsmem evaladdr evaltype get_smem get_lenv]. cbv delta [env var memory.ident Modules.ident] in *. rewrite P. auto.
     * cbn [sat]. split;[exact V | ]. split;[exact T|discriminate].
   + apply V293_star_CurLINV_l.
     repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Theorem V293_OS_TCBInit_empty_body_hoare : forall Spec sd li I tid hi hc
 bf bp bc pc cpu R aop isr is cs,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I (V293_tcb_empty_post bf bp bc R aop isr is cs) Afalse
 (V293_tcb_empty_state bf bp bc pc cpu R aop isr is cs)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc bf bp bc pc cpu R aop isr is cs Frame HR.
 unfold V293_TCBInit_function_body.
 eapply seq_rule;[apply V293_tcb_empty_cpu_hoare;exact HR | ].
 unfold V293_TCBInit_prefix. eapply seq_rule.
 - unfold V293_tcb_empty_state. apply encrit2_rule.
   apply V293_tcb_empty_good_frame. exact Frame.
 - eapply seq_rule;[apply V293_tcb_empty_pointer_hoare;exact HR | ].
   eapply seq_rule with
    (p':=V293_tcb_empty_state bf bp bc Vnull (Vint32 Int.zero) R aop isr is (false::cs)).
   + eapply ift_rule with (tp:=Tint32).
     * intros s HS. exists(Vint32 Int.zero).
       destruct (V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ HS) as (V&T).
       cbn [sat]. split;[exact V | ]. split;[exact T|discriminate].
     * intros s [HS _]. exact HS.
     * eapply conseq_rule with (p:=Afalse) (q:=Afalse).
       -- intros s [HS [v [V B]]].
          destruct (V293_tcb_empty_guard_eval _ _ _ _ _ _ _ _ _ _ HS) as [Z _].
          rewrite Z in V. inversion V;subst v. discriminate B.
       -- intros s HS. contradiction.
       -- apply pfalse_rule.
   + unfold V293_TCBInit_empty. eapply seq_rule.
     * unfold V293_tcb_empty_state. apply excrit2_rule.
       apply V293_tcb_empty_good_frame. exact Frame.
     * apply rete_rule with (v:=Vint32(Int.repr 66)) (t:=Tint32).
       intros s HS. split.
       -- unfold V293_tcb_empty_post. apply astar_l_apure_intro;[exact HS|reflexivity].
       -- destruct s as [[[[[[ge le] M] ir] aux] O] op].
          cbn [sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.

Theorem V293_OS_TCBInit_empty_body_semantics : forall Spec sd li I tid hi hc
 bf bp bc pc cpu R aop isr is cs,
 GoodFrm R -> (R ==> CurLINV li tid) ->
 simulation.RuleSem Spec sd li I (V293_tcb_empty_post bf bp bc R aop isr is cs) Afalse
 (V293_tcb_empty_state bf bp bc pc cpu R aop isr is cs)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof. intros. apply RuleSound. apply V293_OS_TCBInit_empty_body_hoare;assumption. Qed.
Print Assumptions V293_OS_TCBInit_empty_body_hoare.
Print Assumptions V293_OS_TCBInit_empty_body_semantics.
