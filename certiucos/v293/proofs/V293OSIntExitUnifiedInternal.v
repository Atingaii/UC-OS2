(* Actual builders of the accepted normalized function, not the raw CPU-call
   implementation. The contract covers quiet and running same-priority paths only. *)
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

(* The logical path tag below is not a runtime branch or an extra C argument. *)
Definition V293_quiet_exit_index lg : option(nat*nat*nat*spec_code*bool*isr*is*cs) :=
 match lg with
 | logic_lv (Vint32 run::Vint32 nest::Vint32 locked::nil)::logic_code aop::
    logic_ie enabled::logic_isr ir::logic_is si::logic_cs ci::nil =>
 Some(Z.to_nat(Int.unsigned run),Z.to_nat(Int.unsigned nest),Z.to_nat(Int.unsigned locked),aop,enabled,ir,si,ci)
 | _=>None end.
Definition V293_quiet_exit_args run nest locked aop enabled ir si ci :=
 logic_lv (V293_byteval run::V293_byteval nest::V293_byteval locked::nil)::logic_code aop::
  logic_ie enabled::logic_isr ir::logic_is si::logic_cs ci::nil.
Lemma V293_quiet_exit_roundtrip : forall run nest locked aop enabled ir si ci,
 run<256 ->nest<256 ->locked<256 ->
 V293_quiet_exit_index(V293_quiet_exit_args run nest locked aop enabled ir si ci)=
 Some(run,nest,locked,aop,enabled,ir,si,ci).
Proof.
 intros;unfold V293_quiet_exit_index,V293_quiet_exit_args,V293_byteval.
 repeat rewrite V293_sched_snapshot_roundtrip by assumption;reflexivity.
Qed.
Definition V293_quiet_exit_valid run nest locked si :=
 gettopis si<=INUM /\ run<256 /\ nest<256 /\ locked<256 /\
 (run=1 ->2<=nest \/ 0<locked).

Section QuietBuilders.
Variables running nesting lock saved:var.
Variables brun bn bl:block.
Variable li:LocalInv.
Variable extra:asrt.
Variable Hli:GoodLInvAsrt li.
Variable EG:GoodFunAsrt extra.
Definition V293_quiet_globals : asrt :=
 Agvarenv running Tint8(brun,0%Z) //\\
 Agvarenv nesting Tint8(bn,0%Z) //\\ Agvarenv lock Tint8(bl,0%Z).
Definition V293_quiet_bindings :=
 (Agvarenv running Tint8(brun,0%Z) //\\ A_notin_lenv running) **
 V293_exit_guard_bindings nesting lock bn bl.
Lemma V293_quiet_builder_names :
 running<>saved ->nesting<>saved ->lock<>saved ->
 V293_quiet_globals ** V293_exit_builder_domain saved ==>
 V293_quiet_bindings ** V293_exit_builder_domain saved.
Proof.
 intros R N L s Held. unfold V293_exit_builder_domain in *.
 apply astar_comm in Held;apply astar_l_adomlenv_elim in Held as[D Held].
 assert(Absent:forall x,x<>saved ->~indom(getlenv s)x).
 { intros x Ne[v E];rewrite(V293_exit_builder_not_shadow _ _ _ Ne D)in E;discriminate. }
 unfold V293_quiet_globals in Held;destruct Held as[GR[GN GL]].
 assert(E:s |= Aemp)by(pose proof GL as H;apply agvarenv_elim in H;exact(proj2 H)).
 apply astar_comm;apply astar_l_adomlenv_intro;[ |exact D].
 unfold V293_quiet_bindings,V293_exit_guard_bindings.
 apply V293_exit_empty_star;[exact E|split;[exact GR|apply anotinlenv_intro;[exact E|apply Absent;exact R]]| ].
 apply V293_exit_empty_star;[exact E|split;[exact GN|apply anotinlenv_intro;[exact E|apply Absent;exact N]]| ].
 split;[exact GL|apply anotinlenv_intro;[exact E|apply Absent;exact L]].
Qed.
Lemma V293_quiet_forget_names : V293_quiet_bindings ==> V293_quiet_globals.
Proof.
 intros s Held;unfold V293_quiet_bindings,V293_exit_guard_bindings in Held.
 eapply astar_mono in Held.
 2:{ intros st[G _];exact G. }
 2:{ apply astar_mono;intros st[G _];exact G. }
 sep normal in Held.
 apply astar_l_agvarenv_elim in Held as[GR Held].
 apply astar_l_agvarenv_elim in Held as[GN Held].
 apply agvarenv_elim in Held as[GL E].
 unfold V293_quiet_globals;repeat split;apply agvarenv_intro;assumption.
Qed.
Definition V293_quiet_external run nest locked aop enabled ir si ci t :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 (V293_quiet_globals ** (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 (V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(CurLINV li t ** extra)))).
Lemma V293_quiet_external_good : forall run nest locked aop enabled ir si ci t,
 GoodFunAsrt(V293_quiet_external run nest locked aop enabled ir si ci t).
Proof.
 intros;unfold V293_quiet_external,V293_quiet_globals,V293_exit_cells,V293_interrupt_cells.
 cbn[V293_rdy_raw_cells GoodFunAsrt]. repeat split;try exact Logic.I;try exact EG;
 apply V293_CurLINV_function_assertion;exact Hli.
Qed.
Definition V293_quiet_exit_pre lg t :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci) =>
 [|V293_quiet_exit_valid run nest locked si|] **
 V293_quiet_external run nest locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_quiet_exit_post lg t(result:option val) :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci) =>[|result=None|] **
 V293_quiet_external run(V293_exit_quiet_depth run nest)locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_quiet_exit_fpre : fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_quiet_exit_pre lg t)_).
 unfold V293_quiet_exit_pre;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_quiet_external_good]|exact Logic.I].
Defined.
Definition V293_quiet_exit_fpost : fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_quiet_exit_post lg t result)_).
 unfold V293_quiet_exit_post;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_quiet_external_good]|exact Logic.I].
Defined.
Let frame t := V293_exit_guard_bindings nesting lock bn bl **
 (CurLINV li t ** (extra ** V293_exit_builder_domain saved)).
Let data run nest locked bs value t :=
 V293_exit_quiet_data running brun run bn bl nest locked saved bs value(frame t).
Lemma V293_quiet_builder_unpack : forall run nest locked aop enabled ir si ci t,
 running<>saved ->nesting<>saved ->lock<>saved ->
 V293_exit_builder_cells saved **
 V293_quiet_external run nest locked aop enabled ir si ci t ** V293_exit_builder_domain saved ==>
 EX old:val,EX bs:block,<||aop||> ** OS[ir,enabled,si,ci] ** data run nest locked bs old t.
Proof.
 intros run nest locked aop enabled ir si ci t R N L s Held.
 assert(U:s |= (V293_quiet_globals ** V293_exit_builder_domain saved) **
 (V293_exit_builder_cells saved ** (<||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(CurLINV li t ** extra))))).
 { unfold V293_quiet_external in Held;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_quiet_builder_names;assumption. }
 2:{ intros st Hst;exact Hst. }
 unfold data,V293_exit_quiet_data,V293_quiet_bindings,frame,V293_exit_builder_cells,
 V293_time_cell,V293_time_binding,V293_guard_cell,Alvarmapsto,Alvarenv',Aptrmapsto in *.
 clear -U;sep normal in U;destruct U as[old[bs U]];exists old;exists bs.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
 sep normal in U;sep normal;cbn[addrval_to_addr]in *.
 sep rearr in U with(1::6::7::8::9::10::2::3::11::12::13::4::14::15::5::nil). exact U.
Qed.
Lemma V293_quiet_builder_pack : forall run nest locked aop enabled ir si ci t bs value(result:option val),
 [|result=None|] ** (<||aop||> ** OS[ir,enabled,si,ci] ** data run nest locked bs value t) ==>
 V293_exit_builder_cells saved ** ([|result=None|] **
 V293_quiet_external run nest locked aop enabled ir si ci t) ** V293_exit_builder_domain saved.
Proof.
 intros run nest locked aop enabled ir si ci t bs value result s Held.
 assert(U:s |= V293_quiet_bindings ** ([|result=None|] **
 (<||aop||> ** OS[ir,enabled,si,ci] **
 (V293_time_cell true saved bs value **
 (Amapsto(brun,0%Z)Tint8 false(V293_byteval run) **
 (V293_rdy_raw_cells(V293_exit_cells bn bl nest locked)(CurLINV li t ** extra) ** V293_exit_builder_domain saved)))))).
 { unfold data,V293_exit_quiet_data,frame,V293_guard_cell,V293_quiet_bindings in *.
 unfold V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *;clear -Held;sep auto. }
 eapply astar_mono in U.
 2:{ apply V293_quiet_forget_names. }
 2:{ intros st Hst;exact Hst. }
 unfold V293_quiet_external,V293_exit_builder_cells,V293_time_cell,V293_time_binding,
 Alvarmapsto,Alvarenv',Aptrmapsto in *;clear -U;sep auto.
Qed.
Theorem V293_OSIntExit_quiet_builder_contract : forall P f Spec sd I
 table high target current counter sched handoff vl lg t pre post,
 running<>saved ->nesting<>saved ->lock<>saved ->GoodFrm extra ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff) ->
 Some pre=BuildPreI P f vl lg V293_quiet_exit_fpre t ->
 Some post=BuildRetI P f vl lg V293_quiet_exit_fpost t ->
 InfRules Spec sd li I post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff) Afalse t.
Proof.
 intros P f Spec sd I table high target current counter sched handoff vl lg t pre post R N L GF Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved ** V293_quiet_exit_pre lg t ** V293_exit_builder_domain saved))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved ** V293_quiet_exit_post lg t result ** V293_exit_builder_domain saved))in Post.
 inversion Post;subst post.
 unfold V293_quiet_exit_pre,V293_quiet_exit_post.
 destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ]eqn:Index.
 - eapply conseq_rule with(p:=(V293_exit_builder_cells saved **
   V293_quiet_external run nest locked aop enabled ir si ci t ** V293_exit_builder_domain saved) **
   [|V293_quiet_exit_valid run nest locked si|]).
   + intros st Hst;clear -Hst;sep auto.
   + intros st Hst;exact Hst.
   + apply pure_split_rule;intros[Bound[Run[Nest[Lock Off]]]].
     eapply conseq_rule;[apply V293_quiet_builder_unpack;assumption|intros st Hst;exact Hst| ].
     apply ex_intro_rule;intro old;apply ex_intro_rule;intro bs.
     eapply r_conseq_rule with(r:=fun result=>[|result=None|] **
     (<||aop||> ** OS[ir,enabled,si,ci] ** data run(V293_exit_quiet_depth run nest)locked bs(Vint32 Int.zero)t)).
     * intro result;apply V293_quiet_builder_pack.
     * intros st Hst;exact Hst.
     * unfold data;apply V293_OSIntExit_nondispatch_body;try assumption.
       -- unfold frame,V293_exit_guard_bindings,V293_exit_builder_domain;cbn[GoodFrm];
          repeat split;try exact Logic.I;try exact GF;apply V293_current_inv_frame;exact Hli.
       -- unfold frame;apply V293_star_CurLINV_r;apply V293_star_CurLINV_l;intros st Hst;exact Hst.
       -- unfold frame;intros st Hst;eapply V293_star_env_l;[apply V293_exit_guard_bindings_env|exact Hst].
 - eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st Hst;apply astar_comm in Hst;apply astar_assoc_elim in Hst;
     apply astar_l_afalse_elim in Hst;exact Hst.
   + intros st Hst;exact Hst.
   + apply pfalse_rule.
Qed.
End QuietBuilders.

Definition V293_exit_path lg : option(bool*list logicvar) :=
 match lg with logic_ie quiet::rest=>Some(quiet,rest)|_=>None end.
Definition V293_exit_quiet_args lg := logic_ie true::lg.
Definition V293_exit_same_args lg := logic_ie false::lg.
Section UnifiedBuilders.
Variables unmap group rows high table target current counter nesting lock running saved : var.
Variables bt bg br bh bp bo bcur bcounter bn bl brun : block.
Variable tp : type.
Variable li : LocalInv.
Variable extra : asrt.
Variable Hli : GoodLInvAsrt li.
Variable EG : GoodFunAsrt extra.
Let quietfp := V293_quiet_exit_fpre running nesting lock brun bn bl li extra Hli EG.
Let quietfq := V293_quiet_exit_fpost running nesting lock brun bn bl li extra Hli EG.
Let samefp := V293_same_exit_fpre unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bcur bcounter bn bl brun tp li extra Hli EG.
Let samefq := V293_same_exit_fpost unmap group rows high table target current counter nesting lock running
 bt bg br bh bp bo bcur bcounter bn bl brun tp li extra Hli EG.
Definition V293_unified_exit_fpre : fpre := fun vl lg t =>
 match V293_exit_path lg with
 | Some(true,rest)=>quietfp vl rest t
 | Some(false,rest)=>samefp vl rest t
 | None=>@mkfunasrt Afalse Logic.I end.
Definition V293_unified_exit_fpost : fpost := fun vl result lg t =>
 match V293_exit_path lg with
 | Some(true,rest)=>quietfq vl result rest t
 | Some(false,rest)=>samefq vl result rest t
 | None=>@mkfunasrt Afalse Logic.I end.
Theorem V293_OSIntExit_unified_builder_contract : forall P f Spec sd I sched handoff vl lg t pre post,
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 GoodFrm extra ->
 Spec sched=Some(V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil)) ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff) ->
 Some pre=BuildPreI P f vl lg V293_unified_exit_fpre t ->
 Some post=BuildRetI P f vl lg V293_unified_exit_fpost t ->
 InfRules Spec sd li I post Afalse pre
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff) Afalse t.
Proof.
 intros P f Spec sd I sched handoff vl lg t pre post T H G C K N L R GF S Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
       apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
     unfold V293_exit_boundary_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(V293_exit_builder_cells saved **
 getasrt(V293_unified_exit_fpre nil lg t) ** V293_exit_builder_domain saved))in Pre.
 unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>V293_exit_builder_cells saved **
 getasrt(V293_unified_exit_fpost nil result lg t) ** V293_exit_builder_domain saved))in Post.
 unfold V293_unified_exit_fpre in Pre;unfold V293_unified_exit_fpost in Post.
 destruct(V293_exit_path lg)as[[quiet rest]| ]eqn:Path.
 - destruct quiet.
   + eapply (V293_OSIntExit_quiet_builder_contract running nesting lock saved brun bn bl li extra Hli EG
       P f Spec sd I table high target current counter sched handoff nil rest t pre post);try eassumption.
     * unfold BuildPreI;rewrite Code;exact Pre.
     * unfold BuildRetI;rewrite Code;exact Post.
   + eapply (V293_OSIntExit_same_builder_contract
       unmap group rows high table target current counter nesting lock running saved
       bt bg br bh bp bo bcur bcounter bn bl brun tp li extra Hli EG
       P f Spec sd I sched handoff nil rest t pre post);try eassumption.
     * unfold BuildPreI;rewrite Code;exact Pre.
     * unfold BuildRetI;rewrite Code;exact Post.
 - inversion Pre;subst pre;eapply conseq_rule with(p:=Afalse)(q:=Afalse).
   + intros st Hst;apply astar_comm in Hst;apply astar_assoc_elim in Hst;
     apply astar_l_afalse_elim in Hst;exact Hst.
   + intros st Hst;exact Hst.
   + apply pfalse_rule.
Qed.
Variable I : Inv.
Definition V293_unified_exit_env_spec exit enter sched : funspec :=
 fun f=>if Z.eq_dec f exit then Some(V293_unified_exit_fpre,V293_unified_exit_fpost,(Tvoid,nil))
 else if Z.eq_dec f enter then Some
 (V293_interrupt_fpre running nesting brun bn li Hli,
  V293_interrupt_fpost running nesting brun bn li Hli,(Tvoid,nil))
 else V293_ISR_sched_spec sched unmap group rows high bt bg br bh li I Hli f.
Let unit exit enter sched y :=
 V293_exit_env_unit exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
  (V293_interrupt_handoff high current target)).
Lemma V293_unified_exit_env_domains : forall exit enter sched y,
 EqDom(unit exit enter sched y)(V293_unified_exit_env_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,V293_OSIntEnter_unit,
 V293_OSSchedNew_internal_unit,V293_unified_exit_env_spec,V293_ISR_sched_spec.
 destruct(Z.eq_dec f exit), (Z.eq_dec f enter), (Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.

(* The exit body obligation is discharged, unlike the earlier equivalence.
   The exit specification combines quiet and same-task scheduling paths. *)
Theorem V293_unified_exit_env_WFFunEnv : forall exit enter sched y sd,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(unit exit enter sched y)(V293_unified_exit_env_spec exit enter sched)sd li I.
Proof.
 intros exit enter sched y sd XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_unified_exit_env_spec exit enter sched sched=Some
 (V293_ISR_sched_fpre unmap group rows high bt bg br bh li I Hli,
  V293_ISR_sched_fpost unmap group rows high bt bg br bh li I Hli,(Tvoid,nil))).
 { unfold V293_unified_exit_env_spec,V293_ISR_sched_spec;repeat destruct Z.eq_dec;congruence. }
 split;[apply V293_unified_exit_env_domains| ].
 intros f pre post t tl Lookup. unfold V293_unified_exit_env_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
    (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ]. split;[constructor| ]. split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_unified_builder_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ]. split;[constructor| ]. split;[reflexivity| ].
     intros vl p q lg t Pre Post. eapply V293_OSIntEnter_internal_contract;try eassumption.
   + unfold V293_ISR_sched_spec in Lookup.
     destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ]. split;[constructor| ]. split;[reflexivity| ].
     intros vl p q lg t Pre Post. eapply V293_OSSchedNew_ISR_contract;try eassumption.
Qed.
Lemma V293_unified_exit_env_WFIFun : forall exit enter sched y sd,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(unit exit enter sched y)(V293_unified_exit_env_spec exit enter sched)sd I li.
Proof.
 intros. destruct(V293_unified_exit_env_WFFunEnv exit enter sched y sd
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ]. intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
End UnifiedBuilders.
