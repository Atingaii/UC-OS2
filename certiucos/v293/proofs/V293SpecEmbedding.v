(* Preserve void-call derivations under an exact logical-argument embedding.
   Value-call rules require retpost globally and are deliberately excluded. *)
Require Import CertiOS.framework.include_frm.
Require Import Coq.Logic.FunctionalExtensionality Coq.Lists.List.

Fixpoint V293_void_calls (s:stmts) : Prop :=
 match s with
 | scalle _ _ _ => False
 | sif _ s1 s2 | sseq s1 s2 => V293_void_calls s1 /\ V293_void_calls s2
 | sifthen _ body | swhile _ body => V293_void_calls body
 | _ => True
 end.

Definition V293_spec_embedding (source target:funspec) : Prop :=
 forall f pre post tp tl,
 source f = Some(pre,post,(tp,tl)) ->
 exists (pre':fpre) (post':fpost) (embed:list logicvar -> list logicvar),
 target f = Some(pre',post',(tp,tl)) /\
 (forall vl lg t, getasrt(pre' vl (embed lg) t)=getasrt(pre vl lg t)) /\
 (forall vl result lg t, getasrt(post' vl result (embed lg) t)=getasrt(post vl result lg t)).

Theorem V293_InfRules_spec_embedding : forall source sd li Inv r ri p body q t,
 InfRules source sd li Inv r ri p body q t ->
 forall target, V293_spec_embedding source target -> V293_void_calls body ->
 InfRules target sd li Inv r ri p body q t.
Proof.
 intros source sd li Inv r ri p body q t H.
 induction H; intros target HE HC; cbn[V293_void_calls] in HC;
 try contradiction;
 try match type of HC with _ /\ _ => destruct HC as [HC1 HC2] end;
 try solve [econstructor; eauto].
 destruct (HE f pre post tp tl H0) as [pre' [post' [embed [HL [HP HQ]]]]].
 assert (EQ:(EX v:option val, getasrt(post' vl v (embed logicl) t) ** p)=
            (EX v:option val, getasrt(post vl v logicl t) ** p)).
 { f_equal. apply functional_extensionality. intros v. rewrite HQ. reflexivity. }
 rewrite <- EQ.
 eapply call_rule with (pre:=pre') (logicl:=embed logicl); eauto.
 - rewrite HP. exact H1.
 - rewrite HP. exact H4.
 - assert (EQ':(EX v:option val, getasrt(post' vl v (embed logicl) t))=
                  (EX v:option val, getasrt(post vl v logicl t))).
   { f_equal. apply functional_extensionality. intros v. apply HQ. }
   rewrite EQ'. exact H5.
Qed.

Definition V293_spec_override (Spec:funspec) f pre post signature : funspec :=
 fun g=>if Z.eq_dec g f then Some(pre,post,signature) else Spec g.

Lemma V293_override_embedding : forall Spec f pre post pre' post' signature embed,
 Spec f=Some(pre',post',signature) ->
 (forall vl lg t, getasrt(pre' vl (embed lg) t)=getasrt(pre vl lg t)) ->
 (forall vl result lg t, getasrt(post' vl result (embed lg) t)=getasrt(post vl result lg t)) ->
 V293_spec_embedding (V293_spec_override Spec f pre post signature) Spec.
Proof.
 intros Spec f pre post pre' post' signature embed Lookup HP HQ g p q tp tl HG.
 unfold V293_spec_override in HG;destruct(Z.eq_dec g f)as[E|NE].
 - subst g;inversion HG;subst p q signature.
   exists pre';exists post';exists embed;auto.
 - exists p;exists q;exists (fun lg:list logicvar=>lg);auto.
Qed.
