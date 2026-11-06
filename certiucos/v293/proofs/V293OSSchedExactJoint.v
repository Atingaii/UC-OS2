(* One scheduler keeps exact local resources on the critical arm and retains
   the original ISR arm.
   The tag changes only proof-level arguments, never the runtime program. *)
Require Import CertiOS.certiucos.v293.proofs.V293SpecEmbedding.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.

Section ExactJointScheduler.
Variables unmap group rows high:var.
Variables bt bg br bh:block.
Variable li:LocalInv.
Variables CI II:Inv.
Variable Hli:GoodLInvAsrt li.
Let cfp:=V293_sched_exact_fpre unmap group rows high bt bg br bh li CI Hli.
Let cfq:=V293_sched_exact_fpost unmap group rows high bt bg br bh li CI Hli.
Let ifp:=V293_ISR_sched_fpre unmap group rows high bt bg br bh li II Hli.
Let ifq:=V293_ISR_sched_fpost unmap group rows high bt bg br bh li II Hli.
Definition V293_exact_joint_sched_fpre:fpre:=fun vl lg t=>
 match V293_exit_path lg with
 | Some(true,rest)=>cfp vl rest t
 | Some(false,rest)=>ifp vl rest t
 | None=>@mkfunasrt Afalse Logic.I end.
Definition V293_exact_joint_sched_fpost:fpost:=fun vl result lg t=>
 match V293_exit_path lg with
 | Some(true,rest)=>cfq vl result rest t
 | Some(false,rest)=>ifq vl result rest t
 | None=>@mkfunasrt Afalse Logic.I end.

Lemma V293_exact_critical_to_joint : forall Spec f,
 Spec f=Some(V293_exact_joint_sched_fpre,V293_exact_joint_sched_fpost,(Tvoid,nil)) ->
 V293_spec_embedding (V293_spec_override Spec f cfp cfq (Tvoid,nil)) Spec.
Proof.
 intros Spec f H; eapply V293_override_embedding with(embed:=fun lg=>logic_ie true::lg);
 [exact H|intros;reflexivity|intros;reflexivity].
Qed.
Lemma V293_ISR_to_exact_joint : forall Spec f,
 Spec f=Some(V293_exact_joint_sched_fpre,V293_exact_joint_sched_fpost,(Tvoid,nil)) ->
 V293_spec_embedding (V293_spec_override Spec f ifp ifq (Tvoid,nil)) Spec.
Proof.
 intros Spec f H; eapply V293_override_embedding with(embed:=fun lg=>logic_ie false::lg);
 [exact H|intros;reflexivity|intros;reflexivity].
Qed.

Theorem V293_OSSchedNew_exact_joint_contract : forall P f Spec sd RI y lg tid vl pre post,
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 P f=Some(V293_OSSchedNew_function unmap group rows high y) ->
 Some pre=BuildPreI P f vl lg V293_exact_joint_sched_fpre tid ->
 Some post=BuildRetI P f vl lg V293_exact_joint_sched_fpost tid ->
 InfRules Spec sd li RI post Afalse pre (V293_OSSchedNew_body unmap group rows high y) Afalse tid.
Proof.
 intros P f Spec sd RI y lg tid vl pre post U G R H Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_OSSchedNew_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(((EX v:val,LV y@Tint8|->v)**Aemp)**
 getasrt(V293_exact_joint_sched_fpre nil lg tid)**V293_sched_local_domain y))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>((EX v:val,LV y@Tint8|->v)**Aemp)**
 getasrt(V293_exact_joint_sched_fpost nil result lg tid)**V293_sched_local_domain y))in Post.
 unfold V293_exact_joint_sched_fpre in Pre;unfold V293_exact_joint_sched_fpost in Post.
 destruct(V293_exit_path lg)as[[critical rest]| ]eqn:Path.
 - destruct critical.
   + eapply (V293_OSSchedNew_exact_contract P f Spec sd li CI RI
       unmap group rows high y bt bg br bh Hli rest tid nil pre post);try eassumption.
     * unfold BuildPreI;rewrite Code;exact Pre.
     * unfold BuildRetI;rewrite Code;exact Post.
   + eapply (V293_OSSchedNew_ISR_contract P f Spec sd li II RI
       unmap group rows high y bt bg br bh Hli rest tid nil pre post);try eassumption.
     * unfold BuildPreI;rewrite Code;exact Pre.
     * unfold BuildRetI;rewrite Code;exact Post.
 - inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st HS;apply astar_comm in HS;apply astar_assoc_elim in HS;
     apply astar_l_afalse_elim in HS;exact HS.
   + intros st HS;exact HS.
   + apply pfalse_rule.
Qed.
End ExactJointScheduler.
