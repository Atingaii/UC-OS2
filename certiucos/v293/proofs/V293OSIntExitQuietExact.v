(* Quiet Exit keeps the exact local footprint through the real body and builders. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.

Lemma V293_exact_local_frame : forall li t,
 GoodLInvAsrt li -> GoodFrm(p_local li t nil).
Proof.
 intros li t H;unfold p_local,LINV,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto.
 cbn[GoodFrm];repeat split;try exact Logic.I.
 apply V293_local_inv_frame;exact(proj1(H t nil)).
Qed.

Section ExactQuietBuilders.
Variables running nesting lock saved:var.
Variables brun bn bl:block.
Variable li:LocalInv.
Variable extra:asrt.
Variable Hli:GoodLInvAsrt li.
Variable EG:GoodFunAsrt extra.
Let qglobals:=V293_quiet_globals running nesting lock brun bn bl.
Let qbindings:=V293_quiet_bindings running nesting lock brun bn bl.
Definition V293_quiet_exact_external run nest locked aop enabled ir si ci t :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 (qglobals ** (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 (V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(p_local li t nil ** extra)))).
Lemma V293_quiet_exact_external_good : forall run nest locked aop enabled ir si ci t,
 GoodFunAsrt(V293_quiet_exact_external run nest locked aop enabled ir si ci t).
Proof.
 intros;unfold V293_quiet_exact_external,qglobals,V293_exit_cells,V293_interrupt_cells.
 cbn[V293_rdy_raw_cells GoodFunAsrt]. repeat split;try exact Logic.I;try exact EG;
 apply V293_exact_local_good;exact Hli.
Qed.
Definition V293_quiet_exact_exit_pre lg t :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci) =>
 [|V293_quiet_exit_valid run nest locked si|] **
 V293_quiet_exact_external run nest locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_quiet_exact_exit_post lg t(result:option val) :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci) =>[|result=None|] **
 V293_quiet_exact_external run(V293_exit_quiet_depth run nest)locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_quiet_exact_exit_fpre : fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_quiet_exact_exit_pre lg t)_).
 unfold V293_quiet_exact_exit_pre;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_quiet_exact_external_good]|exact Logic.I].
Defined.
Definition V293_quiet_exact_exit_fpost : fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_quiet_exact_exit_post lg t result)_).
 unfold V293_quiet_exact_exit_post;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_quiet_exact_external_good]|exact Logic.I].
Defined.
Let frame t := V293_exit_guard_bindings nesting lock bn bl **
 (p_local li t nil ** (extra ** V293_exit_builder_domain saved)).
Let data run nest locked bs value t :=
 V293_exit_quiet_data running brun run bn bl nest locked saved bs value(frame t).
Lemma V293_quiet_exact_builder_unpack : forall run nest locked aop enabled ir si ci t,
 running<>saved ->nesting<>saved ->lock<>saved ->
 V293_exit_builder_cells saved **
 V293_quiet_exact_external run nest locked aop enabled ir si ci t ** V293_exit_builder_domain saved ==>
 EX old:val,EX bs:block,<||aop||> ** OS[ir,enabled,si,ci] ** data run nest locked bs old t.
Proof.
 intros run nest locked aop enabled ir si ci t R N L s Held.
 assert(U:s |= (qglobals ** V293_exit_builder_domain saved) **
 (V293_exit_builder_cells saved ** (<||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(p_local li t nil ** extra))))).
 { unfold V293_quiet_exact_external in Held;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_quiet_builder_names;assumption. }
 2:{ intros st Hst;exact Hst. }
 unfold data,V293_exit_quiet_data,qbindings,V293_quiet_bindings,frame,V293_exit_builder_cells,
 V293_time_cell,V293_time_binding,V293_guard_cell,Alvarmapsto,Alvarenv',Aptrmapsto in *.
 clear -U;sep normal in U;destruct U as[old[bs U]];exists old;exists bs.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
 sep normal in U;sep normal;cbn[addrval_to_addr]in *.
 sep rearr in U with(1::6::7::8::9::10::2::3::11::12::13::4::14::15::5::nil). exact U.
Qed.
Lemma V293_quiet_exact_builder_pack : forall run nest locked aop enabled ir si ci t bs value(result:option val),
 [|result=None|] ** (<||aop||> ** OS[ir,enabled,si,ci] ** data run nest locked bs value t) ==>
 V293_exit_builder_cells saved ** ([|result=None|] **
 V293_quiet_exact_external run nest locked aop enabled ir si ci t) ** V293_exit_builder_domain saved.
Proof.
 intros run nest locked aop enabled ir si ci t bs value result s Held.
 assert(U:s |= qbindings ** ([|result=None|] **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (V293_time_cell true saved bs value **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 (V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(p_local li t nil ** extra) ** V293_exit_builder_domain saved)))))).
 { unfold data,V293_exit_quiet_data,frame,V293_guard_cell,qbindings,V293_quiet_bindings in *.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_quiet_forget_names. }
 2:{ intros st Hst;exact Hst. }
 unfold V293_quiet_exact_external,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto in *;clear -U;sep auto.
Qed.
Theorem V293_OSIntExit_quiet_exact_builder_contract : forall P f Spec sd I
 table high target current counter sched handoff vl lg t pre post,
 running<>saved ->nesting<>saved ->lock<>saved ->GoodFrm extra ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff) ->
 Some pre=BuildPreI P f vl lg V293_quiet_exact_exit_fpre t ->
 Some post=BuildRetI P f vl lg V293_quiet_exact_exit_fpost t ->
 InfRules Spec sd li I post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff) Afalse t.
Proof.
 intros P f Spec sd I table high target current counter sched handoff vl lg t pre post R N L GF Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved ** V293_quiet_exact_exit_pre lg t ** V293_exit_builder_domain saved))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_quiet_exact_exit_post lg t result ** V293_exit_builder_domain saved))in Post.
 inversion Post;subst post.
 unfold V293_quiet_exact_exit_pre,V293_quiet_exact_exit_post.
 destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ]eqn:Index.
 - eapply conseq_rule with(p:=(V293_exit_builder_cells saved **
   V293_quiet_exact_external run nest locked aop enabled ir si ci t ** V293_exit_builder_domain saved) **
   [|V293_quiet_exit_valid run nest locked si|]).
   + intros st Hst;clear -Hst;sep auto.
   + intros st Hst;exact Hst.
   + apply pure_split_rule;intros[Bound[Run[Nest[Lock Off]]]].
     eapply conseq_rule;[apply V293_quiet_exact_builder_unpack;assumption|intros st Hst;exact Hst| ].
     apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
     eapply r_conseq_rule with(r:=fun result=>[|result=None|] **
     (<||aop||> ** OS[ir,enabled,si,ci] ** data run(V293_exit_quiet_depth run nest)locked bs(Vint32 Int.zero)t)).
     * intro result;apply V293_quiet_exact_builder_pack.
     * intros st Hst;exact Hst.
     * unfold data;apply V293_OSIntExit_nondispatch_body;try assumption.
       -- unfold frame,V293_exit_guard_bindings,V293_exit_builder_domain;cbn[GoodFrm];
          repeat split;try exact Logic.I;try exact GF;apply V293_exact_local_frame;exact Hli.
       -- unfold frame;apply V293_star_CurLINV_r;apply V293_star_CurLINV_l;apply V293_exact_local_weakens.
       -- unfold frame;intros st Hst;eapply V293_star_env_l;[apply V293_exit_guard_bindings_env|exact Hst].
 - eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st Hst;apply astar_comm in Hst;apply astar_assoc_elim in Hst;
     apply astar_l_afalse_elim in Hst;exact Hst.
   + intros st Hst;exact Hst.
   + apply pfalse_rule.
Qed.
End ExactQuietBuilders.
