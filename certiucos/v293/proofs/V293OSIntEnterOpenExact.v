(* Exact control snapshots remain open across the function boundary. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Section OpenEnter.
Variables running nesting lock:var.
Variables brun bn bl:block.
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Definition V293_enter_open_external run nest locked aop enabled ir si ci t :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 (globals ** (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local V293_shared_li t nil ** extra))))).
Lemma V293_enter_open_good : forall run nest locked aop enabled ir si ci t,
 GoodFunAsrt(V293_enter_open_external run nest locked aop enabled ir si ci t).
Proof.
 intros;unfold V293_enter_open_external,globals,V293_quiet_globals;
 cbn[GoodFunAsrt];repeat split;try exact Logic.I;try exact EG;
 apply V293_exact_local_good;apply V293_switch_li_good.
Qed.
Definition V293_enter_open_pre lg t :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci)=>
 [|run<256 /\ nest<256 /\ locked<256|] **
 V293_enter_open_external run nest locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_enter_open_post lg t(result:option val) :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci)=>[|result=None|] **
 V293_enter_open_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_enter_open_fpre:fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_enter_open_pre lg t)_).
 unfold V293_enter_open_pre;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_enter_open_good]|exact Logic.I].
Defined.
Definition V293_enter_open_fpost:fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_enter_open_post lg t result)_).
 unfold V293_enter_open_post;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_enter_open_good]|exact Logic.I].
Defined.
Let kept locked enabled ir si ci t:=globals **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local V293_shared_li t nil ** extra ** (OS[ir,enabled,si,ci] ** A_dom_lenv nil))).
Lemma V293_enter_open_env : forall locked enabled ir si ci t st,
 st |=kept locked enabled ir si ci t ->
 V293_interrupt_env running nesting brun bn(getgenv st)(getlenv st).
Proof.
 intros locked enabled ir si ci t st H.
 assert(D:st |=A_dom_lenv nil ** Atrue)by(unfold kept in H;sep auto).
 apply astar_l_adomlenv_elim in D;destruct D as[D _].
 assert(G:get(getgenv st)running=Some(brun,Tint8) /\ get(getgenv st)nesting=Some(bn,Tint8)).
 { eapply V293_star_env_l with(E:=fun ge le=>get ge running=Some(brun,Tint8) /\ get ge nesting=Some(bn,Tint8));[ |exact H].
 intros s [GR[GN GL]];apply agvarenv_elim in GR,GN.
 change(EnvMod.get(getgenv s)running=Some(brun,Tint8) /\ EnvMod.get(getgenv s)nesting=Some(bn,Tint8));tauto. }
 unfold V293_interrupt_env;repeat split;try(apply V293_interrupt_empty_local;exact D);tauto.
Qed.
Theorem V293_OSIntEnter_open_updates : forall Spec sd I r ri t run nest locked aop enabled ir si ci,
 run<256 ->nest<256 ->
 InfRules Spec sd V293_shared_li I r ri
 (V293_enter_open_external run nest locked aop enabled ir si ci t ** A_dom_lenv nil)
 (V293_OSIntEnter_updates running nesting)
 (V293_enter_open_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** A_dom_lenv nil)t.
Proof.
 intros;eapply conseq_rule with
 (p:=<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run nest)(kept locked enabled ir si ci t))
 (q:=<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run(V293_interrupt_nest_after run nest))(kept locked enabled ir si ci t)).
 - unfold V293_enter_open_external,kept,V293_interrupt_cells;cbn[V293_rdy_raw_cells];intros s K;sep auto.
 - unfold V293_enter_open_external,kept,V293_interrupt_cells;cbn[V293_rdy_raw_cells];intros s K;sep auto.
 - apply V293_OSIntEnter_updates_hoare;try assumption;[apply V293_enter_open_env| ].
   unfold kept;intros s K;apply V293_local_current_extend with(extra:=Atrue);sep auto.
Qed.
Theorem V293_OSIntEnter_open_body : forall Spec sd I t lg,
 InfRules Spec sd V293_shared_li I
 (fun result=>Aemp ** (V293_enter_open_post lg t result ** A_dom_lenv nil))Afalse
 (Aemp ** (V293_enter_open_pre lg t ** A_dom_lenv nil))
 (V293_OSIntEnter_body running nesting)Afalse t.
Proof.
 intros;unfold V293_enter_open_pre,V293_enter_open_post.
 destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ].
 - eapply conseq_rule with(p:=(V293_enter_open_external run nest locked aop enabled ir si ci t ** A_dom_lenv nil) ** [|run<256 /\ nest<256 /\ locked<256|]).
   + intros s K;sep auto.
   + intros s K;exact K.
   + apply pure_split_rule;intros[Run[Nest Lock]].
     unfold V293_OSIntEnter_body;eapply seq_rule.
     * apply V293_OSIntEnter_open_updates;assumption.
     * apply ret_rule;intros s K;sep auto.
 - apply V293_interrupt_false_entry.
Qed.
Theorem V293_OSIntEnter_open_contract : forall P f Spec sd I vl lg t pre post,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 Some pre=BuildPreI P f vl lg V293_enter_open_fpre t ->
 Some post=BuildRetI P f vl lg V293_enter_open_fpost t ->
 InfRules Spec sd V293_shared_li I post Afalse pre(V293_OSIntEnter_body running nesting)Afalse t.
Proof.
 intros P f Spec sd I vl lg t pre post Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
 apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 unfold V293_OSIntEnter_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(Aemp ** (V293_enter_open_pre lg t ** A_dom_lenv nil)))in Pre.
 inversion Pre;subst pre;unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>Aemp ** (V293_enter_open_post lg t result ** A_dom_lenv nil)))in Post.
 inversion Post;subst post;apply V293_OSIntEnter_open_body.
Qed.
Theorem V293_OSIntEnter_open_call : forall Spec sd I r ri enter t run nest locked aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->GoodFrm callerframe ->
 Spec enter=Some(V293_enter_open_fpre,V293_enter_open_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li I r ri
 (V293_enter_open_external run nest locked aop enabled ir si ci t ** callerframe)
 (scall enter nil)
 (V293_enter_open_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros Spec sd I r ri enter t run nest locked aop enabled ir si ci callerframe Run Nest Lock GF Entry.
 set(lg:=V293_quiet_exit_args run nest locked aop enabled ir si ci).
 assert(Ep:getasrt(V293_enter_open_fpre nil lg t)=[|run<256 /\ nest<256 /\ locked<256|] ** V293_enter_open_external run nest locked aop enabled ir si ci t).
 { unfold V293_enter_open_fpre,V293_enter_open_pre,lg;rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 assert(Eq:forall result,getasrt(V293_enter_open_fpost nil result lg t)=[|result=None|] ** V293_enter_open_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t).
 { intro result;unfold V293_enter_open_fpost,V293_enter_open_post,lg;rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 eapply conseq_rule with(p:=getasrt(V293_enter_open_fpre nil lg t) ** callerframe)
 (q:=EX result:option val,getasrt(V293_enter_open_fpost nil result lg t) ** callerframe).
 - rewrite Ep;intros s K;sep auto.
 - intros s[result K];rewrite Eq in K;sep auto.
 - eapply call_rule with(pre:=V293_enter_open_fpre)(post:=V293_enter_open_fpost)
 (vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
   + exact GF.
   + exact Entry.
   + intros s K;exact K.
   + intros s K;reflexivity.
   + reflexivity.
   + rewrite Ep;intros s K;apply V293_local_current_extend with(extra:=Atrue);unfold V293_enter_open_external in K;sep auto.
   + intros s[result K];rewrite Eq in K;apply V293_local_current_extend with(extra:=Atrue);unfold V293_enter_open_external in K;sep auto.
Qed.
End OpenEnter.
