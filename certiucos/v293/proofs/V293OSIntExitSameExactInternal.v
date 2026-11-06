(* Exact same-priority function boundary using the original snapshot codec. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
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

Section SameExactBuilders.
Variables unmap group rows high table target current counter nesting lock running saved : var.
Variables bt bg br bh bp bo bcur bcounter bn bl brun : block.
Variable tp : type.
Variable li : LocalInv.
Variable extra : asrt.
Variable Hli : GoodLInvAsrt li.
Variable EG : GoodFunAsrt extra.
Let globals := V293_exit_builder_globals table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun.
Let caller := V293_exit_caller_bindings high table target tp bp bo current counter nesting lock bcur bcounter bn bl.
Let frame := V293_exit_guard_bindings nesting lock bn bl ** (extra ** V293_exit_builder_domain saved).

(* No local binding, OS state, or abstract operation is hidden in this memory. *)
Definition V293_same_exact_exit_memory lo hi entries tasks nc nest hv out c t : asrt :=
 (((V293_sched_globals unmap group rows high bt bg br bh **
    V293_sched_inputs bt bg br lo hi(V293_ready_group lo hi)) ** p_local li t nil) **
   PV(bh,Int.zero)@Tint8|->hv) **
 (((V293_read_pointers tp bp 0 entries ** Aabsdata abstcblsid(abstcblist tasks)) **
   (Amapsto(bcur,0%Z)Tint8 false(V293_byteval nc) **
    V293_rdy_raw_cells(V293_exit_cells bn bl nest 0)Aemp)) **
  (V293_prefix_output tp bo out ** PV(bcounter,Int.zero)@Tint32|->Vint32 c)).
Lemma V293_same_exact_exit_memory_good : forall lo hi entries tasks nc nest hv out c t,
 GoodFunAsrt(V293_same_exact_exit_memory lo hi entries tasks nc nest hv out c t).
Proof.
 intros. assert(P:GoodFunAsrt(V293_read_pointers tp bp 0 entries)).
 { generalize 0%Z;induction entries;intros;cbn[V293_read_pointers GoodFunAsrt];auto. }
 unfold V293_same_exact_exit_memory,V293_sched_globals,V293_sched_inputs,V293_prefix_output,
  V293_exit_cells,V293_interrupt_cells.
 cbn[V293_rdy_raw_cells Aptrmapsto GoodFunAsrt]. repeat split;try exact Logic.I;
 try apply V293_read_bytes_function_assertion;try exact P;
 apply V293_exact_local_good;exact Hli.
Qed.
Definition V293_same_exact_exit_external enabled ir si ci lo hi entries tasks nc nest hv out c aop t :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 (V293_same_exact_exit_memory lo hi entries tasks nc nest hv out c t **
  (globals ** (Amapsto(brun,0%Z)Tint8 false(V293_byteval 1) ** extra))).
Lemma V293_same_exact_exit_external_good : forall enabled ir si ci lo hi entries tasks nc nest hv out c aop t,
 GoodFunAsrt(V293_same_exact_exit_external enabled ir si ci lo hi entries tasks nc nest hv out c aop t).
Proof.
 intros. unfold V293_same_exact_exit_external. split;[exact Logic.I| ].
 split;[cbn[GoodFunAsrt];tauto| ].
 split;[apply V293_same_exact_exit_memory_good| ].
 split;[apply V293_exit_builder_globals_good|split;[exact Logic.I|exact EG]].
Qed.
Definition V293_same_exact_exit_pre lg t :=
 match V293_same_exit_index lg with
 | Some(enabled,ir,si,ci,x) => [|V293_same_exit_valid si x|] **
   (EX hv:val,V293_same_exact_exit_external enabled ir si ci(V293_xlo x)(V293_xhi x)
    (V293_xentries x)(V293_xtasks x)(V293_xcurrent x)(V293_xnest x)hv(V293_xold x)(V293_xcounter x)(V293_xaop x)t)
 | None => Afalse
 end.
Definition V293_same_exact_exit_post lg t (result:option val) :=
 match V293_same_exit_index lg with
 | Some(enabled,ir,si,ci,x) => [|result=None|] **
   (EX selected:Modules.tid,[|V293_highest_ready(V293_xtasks x)selected|] **
    V293_same_exact_exit_external enabled ir si ci(V293_xlo x)(V293_xhi x)
     (V293_xentries x)(V293_xtasks x)(V293_xcurrent x)0
     (V293_byteval(V293_ready_select(V293_xlo x)(V293_xhi x)(V293_ready_group(V293_xlo x)(V293_xhi x))))
     (Vptr selected)(V293_xcounter x)(V293_xaop x)t)
 | None => Afalse
 end.
Definition V293_same_exact_exit_fpre : fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_same_exact_exit_pre lg t)_).
 unfold V293_same_exact_exit_pre;destruct(V293_same_exit_index lg)as[[[[[enabled ir]si]ci]x]| ];[ |exact Logic.I].
 split;[exact Logic.I|intro hv;apply V293_same_exact_exit_external_good].
Defined.
Definition V293_same_exact_exit_fpost : fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_same_exact_exit_post lg t result)_).
 unfold V293_same_exact_exit_post;destruct(V293_same_exit_index lg)as[[[[[enabled ir]si]ci]x]| ];[ |exact Logic.I].
 split;[exact Logic.I|intro selected;split;[exact Logic.I|apply V293_same_exact_exit_external_good]].
Defined.

Let data lo hi entries tasks nc bs t nest hv out c value :=
 V293_exit_same_exact_data unmap group rows high bt bg br bh lo hi li t table target tp bp bo entries tasks
 current counter running saved bcur bcounter brun bn bl bs nc frame nest hv out c value.
Let answer lo hi entries tasks nc bs t c value :=
 V293_exit_same_exact_result unmap group rows high bt bg br bh lo hi li t table target tp bp bo entries tasks
 current counter running saved bcur bcounter brun bn bl bs nc frame c value.

Lemma V293_same_exact_exit_builder_unpack : forall enabled ir si ci lo hi entries tasks nc nest hv out c aop t,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 V293_exit_builder_cells saved **
 V293_same_exact_exit_external enabled ir si ci lo hi entries tasks nc nest hv out c aop t **
 V293_exit_builder_domain saved ==>
 EX old:val,EX bs:block,<||aop||> ** OS[ir,enabled,si,ci] ** data lo hi entries tasks nc bs t nest hv out c old.
Proof.
 intros enabled ir si ci lo hi entries tasks nc nest hv out c aop t T H G C K N L R s Held.
 assert(U:s |= (globals ** V293_exit_builder_domain saved) **
  (V293_exit_builder_cells saved ** (<||aop||> ** OS[ir,enabled,si,ci] **
   (V293_same_exact_exit_memory lo hi entries tasks nc nest hv out c t **
    (Amapsto(brun,0%Z)Tint8 false(V293_byteval 1) ** extra))))).
 { unfold V293_same_exact_exit_external in Held;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_names with(high:=high);assumption. }
 2:{ intros st Hst;exact Hst. }
 unfold data,V293_exit_same_exact_data,V293_exit_same_exact_core,V293_same_exact_exit_memory,
 V293_exit_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_time_cell,V293_time_binding,V293_guard_cell,V293_counter_cell,
 V293_prefix_frame,caller,V293_exit_caller_bindings,frame in *.
 clear -U;sep normal in U;destruct U as[old [bs U]];exists old;exists bs.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
 unfold Aptrmapsto in *;cbn[addrval_to_addr]in *.
 sep normal in U;sep normal.
 sep rearr in U with (2::1::9::10::11::12::13::3::4::25::14::15::16::17::5::18::19::20::21::22::7::26::8::23::6::24::nil).
 exact U.
Qed.

Lemma V293_same_exact_exit_builder_pack : forall enabled ir si ci lo hi entries tasks nc bs t c aop value (result:option val),
 [|result=None|] ** (<||aop||> ** OS[ir,enabled,si,ci] ** answer lo hi entries tasks nc bs t c value) ==>
 V293_exit_builder_cells saved **
 ([|result=None|] ** (EX selected:Modules.tid,[|V293_highest_ready tasks selected|] **
 V293_same_exact_exit_external enabled ir si ci lo hi entries tasks nc 0
 (V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))(Vptr selected)c aop t)) **
 V293_exit_builder_domain saved.
Proof.
 intros enabled ir si ci lo hi entries tasks nc bs t c aop value result s Held.
 unfold answer,V293_exit_same_exact_result in Held;sep normal in Held.
 destruct Held as[selected Held].
 assert(U:s |= (caller ** (Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running)) **
 ([|result=None|] ** ([|V293_highest_ready tasks selected|] **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (V293_time_cell true saved bs value **
 (V293_same_exact_exit_memory lo hi entries tasks nc 0
  (V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))(Vptr selected)c t **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval 1) ** (extra ** V293_exit_builder_domain saved)))))))).
 { unfold data,V293_exit_same_exact_data,V293_exit_same_exact_core,V293_same_exact_exit_memory,
   V293_guard_cell,V293_counter_cell,V293_prefix_frame,caller,V293_exit_caller_bindings,frame in *.
   unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
   unfold Aptrmapsto in *;cbn[addrval_to_addr]in *.
   sep normal in Held;sep normal.
   sep rearr in Held with (2::1::10::20::16::22::3::23::24::25::26::27::4::6::7::8::9::11::12::13::14::15::19::21::5::17::18::nil).
   exact Held. }
 eapply astar_mono in U.
 2:{ apply V293_exit_builder_forget_names. }
 2:{ intros st Hst;exact Hst. }
 unfold V293_same_exact_exit_external,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto,globals in *.
 clear -U;sep auto.
Qed.

Theorem V293_OSIntExit_same_exact_builder_contract : forall P f Spec sd I sched handoff vl lg t pre post,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 GoodFrm extra ->
 Spec sched=Some(V293_ISR_exact_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_exact_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff) ->
 Some pre=BuildPreI P f vl lg V293_same_exact_exit_fpre t ->
 Some post=BuildRetI P f vl lg V293_same_exact_exit_fpost t ->
 InfRules Spec sd li I post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff) Afalse t.
Proof.
 intros P f Spec sd I sched handoff vl lg t pre post T H G C K N L R GF Lookup Body Pre Post.
 unfold BuildPreI in Pre;rewrite Body in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved ** V293_same_exact_exit_pre lg t ** V293_exit_builder_domain saved))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Body in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_same_exact_exit_post lg t result ** V293_exit_builder_domain saved))in Post.
 inversion Post;subst post.
 unfold V293_same_exact_exit_pre,V293_same_exact_exit_post.
 destruct(V293_same_exit_index lg)as[[[[[enabled ir]si]ci]x]| ]eqn:Index.
 - eapply conseq_rule with(p:=(V293_exit_builder_cells saved **
   (EX hv:val,V293_same_exact_exit_external enabled ir si ci(V293_xlo x)(V293_xhi x)
    (V293_xentries x)(V293_xtasks x)(V293_xcurrent x)(V293_xnest x)hv(V293_xold x)(V293_xcounter x)(V293_xaop x)t) **
   V293_exit_builder_domain saved) ** [|V293_same_exit_valid si x|]).
   + intros st Hst;clear -Hst;sep auto.
   + intros st Hst;exact Hst.
   + apply pure_split_rule;intros[Bound[Valid[Nest[Lock[Ready[Bitmap[Table Same]]]]]]].
     destruct x as[lo hi nc nest locked c out token value entries tasks aop].
     cbn[V293_xlo V293_xhi V293_xcurrent V293_xnest V293_xlocked V293_xcounter V293_xold V293_xentries V293_xtasks V293_xaop]in *;destruct Valid as[Low[High[Cur[Depth Locked]]]].
     eapply conseq_rule with(p:=EX hv:val,V293_exit_builder_cells saved **
      V293_same_exact_exit_external enabled ir si ci lo hi entries tasks nc nest hv out c aop t ** V293_exit_builder_domain saved).
     * intros st Hst;clear -Hst;sep auto.
     * intros st Hst;exact Hst.
     * apply ex_intro_rule;intro hv.
       eapply conseq_rule;[apply V293_same_exact_exit_builder_unpack;assumption|intros st Hst;exact Hst| ].
       apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
       eapply r_conseq_rule with(r:=fun result=>[|result=None|] **
        (<||aop||> ** OS[ir,enabled,si,ci] ** answer lo hi entries tasks nc bs t c(Vint32 Int.zero))).
       -- intro result;apply V293_same_exact_exit_builder_pack.
       -- intros st Hst;exact Hst.
       -- unfold data,answer. apply V293_OSIntExit_same_exact_priority_body with(Hli:=Hli);try assumption.
          ++ unfold frame,V293_exit_guard_bindings,V293_exit_builder_domain;cbn[GoodFrm];tauto.
          ++ unfold frame;intros st Hst;eapply V293_star_env_l;[apply V293_exit_guard_bindings_env|exact Hst].
 - eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st Hst;apply astar_comm in Hst;apply astar_assoc_elim in Hst;
     apply astar_l_afalse_elim in Hst;exact Hst.
   + intros st Hst;exact Hst.
   + apply pfalse_rule.
Qed.

End SameExactBuilders.
