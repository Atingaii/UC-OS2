(* Global control bindings live in the framework's existing LocalInv. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryGeneral.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryControl.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Section Bindings.
Variables running nesting lock:var.
Variables brun bn bl:block.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Definition V293_irq_bound_li:LocalInv:=fun _ _=>globals.
Lemma V293_irq_bound_empty : forall t lg,V293_irq_bound_li t lg ==>Aemp.
Proof.
 intros t lg st [G _];apply agvarenv_elim in G;exact(proj2 G).
Qed.
Lemma V293_irq_bound_good : GoodLInvAsrt V293_irq_bound_li.
Proof.
 intros t lg;split.
 - unfold V293_irq_bound_li,globals,V293_quiet_globals;cbn[GoodLocalInvAsrt];auto.
 - intros ge le M ir aux O le' M' aux' ir' O' H H'.
   specialize(H(spec_done None));specialize(H'(spec_done None)).
   apply V293_irq_bound_empty in H,H'.
   destruct H as[HM HO];destruct H' as[HM' HO'].
   cbn[emptaskst emposabst]in *;split;congruence.
Qed.
Lemma V293_irq_bound_local_open : forall t lg,
 p_local V293_irq_bound_li t lg ==>p_local V293_shared_li t nil ** globals.
Proof.
 intros t lg;unfold p_local,LINV,V293_irq_bound_li,V293_shared_li.
 intros st H;sep auto;apply V293_switch_li_good.
Qed.
Lemma V293_irq_bound_local_close : forall t lg,
 p_local V293_shared_li t nil ** globals ==>p_local V293_irq_bound_li t lg.
Proof.
 intros t lg;unfold p_local,LINV,V293_irq_bound_li,V293_shared_li.
 intros st H;sep auto;apply V293_irq_bound_good.
Qed.
Lemma V293_irq_bound_current : forall t extra,
 p_local V293_irq_bound_li t nil ** extra ==>CurLINV V293_irq_bound_li t.
Proof.
 intros t extra st H;exists(@nil logicvar);unfold p_local in H;sep auto.
Qed.
Theorem V293_irq_bound_GoodI : forall Inv0 sd,
 GoodI Inv0 sd V293_shared_li ->GoodI Inv0 sd V293_irq_bound_li.
Proof.
 intros Inv0 sd [All [Current [Switch Sched]]].
 split;[exact All| ];split;[exact Current| ];split;[ |exact Sched].
 intros o O ab t b tp M' ct Inv Highest Global Store.
 destruct(Switch o O ab t b tp M' ct Inv Highest Global Store)as[tls[Tasks Branch]].
 exists tls;split;[exact Tasks| ];destruct Branch as[Alive|[Dead Release]];[left;exact Alive| ].
 right;split;[exact Dead| ];intros Mx Ox MM OO Local JM JO.
 apply Release with(Mx:=Mx)(Ox:=Ox);try assumption.
 intros aop;specialize(Local aop);destruct Local as[lg Local].
 exists lg;apply V293_irq_bound_empty in Local;exact Local.
Qed.
End Bindings.

Section BoundEnter.
Variables running nesting lock:var.
Variables brun bn bl:block.
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Definition V293_enter_bound_external run nest locked aop enabled ir si ci t :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** extra)))).
Lemma V293_enter_bound_good : forall run nest locked aop enabled ir si ci t,
 GoodFunAsrt(V293_enter_bound_external run nest locked aop enabled ir si ci t).
Proof.
 intros;unfold V293_enter_bound_external,globals,V293_quiet_globals;
 cbn[GoodFunAsrt];repeat split;try exact Logic.I;try exact EG;
 apply V293_exact_local_good;apply V293_irq_bound_good.
Qed.
Definition V293_enter_bound_pre lg t :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci)=>
 [|run<256 /\ nest<256 /\ locked<256|] **
 V293_enter_bound_external run nest locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_enter_bound_post lg t(result:option val) :=
 match V293_quiet_exit_index lg with
 | Some(run,nest,locked,aop,enabled,ir,si,ci)=>[|result=None|] **
 V293_enter_bound_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t
 | None=>Afalse end.
Definition V293_enter_bound_fpre:fpre.
Proof.
 intros vl lg t;refine(@mkfunasrt(V293_enter_bound_pre lg t)_).
 unfold V293_enter_bound_pre;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_enter_bound_good]|exact Logic.I].
Defined.
Definition V293_enter_bound_fpost:fpost.
Proof.
 intros vl result lg t;refine(@mkfunasrt(V293_enter_bound_post lg t result)_).
 unfold V293_enter_bound_post;destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ];
 [split;[exact Logic.I|apply V293_enter_bound_good]|exact Logic.I].
Defined.
Let kept locked enabled ir si ci t:=
 Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** extra ** (OS[ir,enabled,si,ci] ** A_dom_lenv nil)).
Lemma V293_enter_bound_env : forall locked enabled ir si ci t st,
 st |=kept locked enabled ir si ci t ->
 V293_interrupt_env running nesting brun bn(getgenv st)(getlenv st).
Proof.
 intros locked enabled ir si ci t st H.
 assert(D:st |=A_dom_lenv nil ** Atrue)by(unfold kept in H;sep auto).
 apply astar_l_adomlenv_elim in D;destruct D as[D _].
 assert(B:st |=globals ** Atrue).
 { unfold kept,p_local,LINV,li,V293_irq_bound_li in H;sep auto. }
 assert(G:get(getgenv st)running=Some(brun,Tint8) /\ get(getgenv st)nesting=Some(bn,Tint8)).
 { eapply V293_star_env_l with(E:=fun ge le=>get ge running=Some(brun,Tint8) /\ get ge nesting=Some(bn,Tint8));[ |exact B].
 intros s [GR[GN GL]];apply agvarenv_elim in GR,GN.
 change(EnvMod.get(getgenv s)running=Some(brun,Tint8) /\ EnvMod.get(getgenv s)nesting=Some(bn,Tint8));tauto. }
 unfold V293_interrupt_env;repeat split;try(apply V293_interrupt_empty_local;exact D);tauto.
Qed.
Theorem V293_OSIntEnter_bound_updates : forall Spec sd I r ri t run nest locked aop enabled ir si ci,
 run<256 ->nest<256 ->
 InfRules Spec sd li I r ri
 (V293_enter_bound_external run nest locked aop enabled ir si ci t ** A_dom_lenv nil)
 (V293_OSIntEnter_updates running nesting)
 (V293_enter_bound_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** A_dom_lenv nil)t.
Proof.
 intros;eapply conseq_rule with
 (p:=<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run nest)(kept locked enabled ir si ci t))
 (q:=<||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run(V293_interrupt_nest_after run nest))(kept locked enabled ir si ci t)).
 - unfold V293_enter_bound_external,kept,V293_interrupt_cells;cbn[V293_rdy_raw_cells];intros s K;sep auto.
 - unfold V293_enter_bound_external,kept,V293_interrupt_cells;cbn[V293_rdy_raw_cells];intros s K;sep auto.
 - apply V293_OSIntEnter_updates_hoare;try assumption;[apply V293_enter_bound_env| ].
   unfold kept;intros s K;apply V293_irq_bound_current with(extra:=Atrue);sep auto.
Qed.
Theorem V293_OSIntEnter_bound_body : forall Spec sd I t lg,
 InfRules Spec sd li I
 (fun result=>Aemp ** (V293_enter_bound_post lg t result ** A_dom_lenv nil))Afalse
 (Aemp ** (V293_enter_bound_pre lg t ** A_dom_lenv nil))
 (V293_OSIntEnter_body running nesting)Afalse t.
Proof.
 intros;unfold V293_enter_bound_pre,V293_enter_bound_post.
 destruct(V293_quiet_exit_index lg)as[[[[[[[[run nest]locked]aop]enabled]ir]si]ci]| ].
 - eapply conseq_rule with(p:=(V293_enter_bound_external run nest locked aop enabled ir si ci t ** A_dom_lenv nil) ** [|run<256 /\ nest<256 /\ locked<256|]).
   + intros s K;sep auto.
   + intros s K;exact K.
   + apply pure_split_rule;intros[Run[Nest Lock]].
     unfold V293_OSIntEnter_body;eapply seq_rule.
     * apply V293_OSIntEnter_bound_updates;assumption.
     * apply ret_rule;intros s K;sep auto.
 - apply V293_interrupt_false_entry.
Qed.
Theorem V293_OSIntEnter_bound_contract : forall P f Spec sd I vl lg t pre post,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 Some pre=BuildPreI P f vl lg V293_enter_bound_fpre t ->
 Some post=BuildRetI P f vl lg V293_enter_bound_fpost t ->
 InfRules Spec sd li I post Afalse pre(V293_OSIntEnter_body running nesting)Afalse t.
Proof.
 intros P f Spec sd I vl lg t pre post Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre;destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
 apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 unfold V293_OSIntEnter_function in Pre;rewrite E in Pre;discriminate. }
 change(Some pre=Some(Aemp ** (V293_enter_bound_pre lg t ** A_dom_lenv nil)))in Pre.
 inversion Pre;subst pre;unfold BuildRetI in Post;rewrite Code in Post.
 change(Some post=Some(fun result=>Aemp ** (V293_enter_bound_post lg t result ** A_dom_lenv nil)))in Post.
 inversion Post;subst post;apply V293_OSIntEnter_bound_body.
Qed.
Theorem V293_OSIntEnter_bound_call : forall Spec sd I r ri enter t run nest locked aop enabled ir si ci callerframe,
 run<256 ->nest<256 ->locked<256 ->GoodFrm callerframe ->
 Spec enter=Some(V293_enter_bound_fpre,V293_enter_bound_fpost,(Tvoid,nil)) ->
 InfRules Spec sd li I r ri
 (V293_enter_bound_external run nest locked aop enabled ir si ci t ** callerframe)
 (scall enter nil)
 (V293_enter_bound_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t ** callerframe)t.
Proof.
 intros Spec sd I r ri enter t run nest locked aop enabled ir si ci callerframe Run Nest Lock GF Entry.
 set(lg:=V293_quiet_exit_args run nest locked aop enabled ir si ci).
 assert(Ep:getasrt(V293_enter_bound_fpre nil lg t)=[|run<256 /\ nest<256 /\ locked<256|] ** V293_enter_bound_external run nest locked aop enabled ir si ci t).
 { unfold V293_enter_bound_fpre,V293_enter_bound_pre,lg;rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 assert(Eq:forall result,getasrt(V293_enter_bound_fpost nil result lg t)=[|result=None|] ** V293_enter_bound_external run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t).
 { intro result;unfold V293_enter_bound_fpost,V293_enter_bound_post,lg;rewrite V293_quiet_exit_roundtrip by assumption;reflexivity. }
 eapply conseq_rule with(p:=getasrt(V293_enter_bound_fpre nil lg t) ** callerframe)
 (q:=EX result:option val,getasrt(V293_enter_bound_fpost nil result lg t) ** callerframe).
 - rewrite Ep;intros s K;sep auto.
 - intros s[result K];rewrite Eq in K;sep auto.
 - eapply call_rule with(pre:=V293_enter_bound_fpre)(post:=V293_enter_bound_fpost)
 (vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil).
   + exact GF.
   + exact Entry.
   + intros s K;exact K.
   + intros s K;reflexivity.
   + reflexivity.
   + rewrite Ep;intros s K;apply V293_irq_bound_current with(extra:=Atrue);unfold V293_enter_bound_external in K;sep auto.
   + intros s[result K];rewrite Eq in K;apply V293_irq_bound_current with(extra:=Atrue);unfold V293_enter_bound_external in K;sep auto.
Qed.
Definition V293_enter_bound_spec enter:funspec:=fun f=>
 if Z.eq_dec f enter then Some(V293_enter_bound_fpre,V293_enter_bound_fpost,(Tvoid,nil))else None.
Theorem V293_OSIntEnter_bound_WFFunEnv : forall enter sd Inv0,
 WFFunEnv(V293_OSIntEnter_unit enter running nesting)(V293_enter_bound_spec enter)sd li Inv0.
Proof.
 intros enter sd Inv0;split.
 - intros f;unfold V293_OSIntEnter_unit,V293_enter_bound_spec.
   destruct(Z.eq_dec f enter);split;intros[x H];try discriminate;eexists;reflexivity.
 - intros f pre post t tl Lookup;unfold V293_enter_bound_spec in Lookup.
   destruct(Z.eq_dec f enter);[ |discriminate];inversion Lookup;subst pre post t tl.
   exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
   split.
   + unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
   + split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg tid Pre Post;eapply V293_OSIntEnter_bound_contract;try eassumption.
     unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
Qed.
Theorem V293_OSIntEnter_bound_WFIFun : forall enter sd Inv0,
 WFIFun(V293_OSIntEnter_unit enter running nesting)(V293_enter_bound_spec enter)sd Inv0 li.
Proof.
 intros;destruct(V293_OSIntEnter_bound_WFFunEnv enter sd Inv0)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&stmt&Code&Types&Decls&Checked).
 exists d1;exists d2;exists stmt;auto.
Qed.
End BoundEnter.

Section BoundEntry.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let globals:=V293_quiet_globals running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let kept:=V293_quiet_irq_kept target bt bg br bh bp bc bk rest.
Let external:=V293_enter_bound_external running nesting lock brun bn bl Aemp.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Definition V293_irq_bound_snapshot run nest locked aop enabled ir si ci t:=
 external run nest locked aop enabled ir si ci t ** (kept ** A_dom_lenv nil).
Lemma V293_irq_bound_snapshot_pack : forall run nest locked aop enabled ir si ci t,
 V293_quiet_irq_snapshot target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 run nest locked aop enabled ir si ci t ==>
 V293_irq_bound_snapshot run nest locked aop enabled ir si ci t.
Proof.
 intros run nest locked aop enabled ir si ci t st H.
 unfold V293_quiet_irq_snapshot,V293_enter_open_external in H.
 unfold V293_irq_bound_snapshot,external,V293_enter_bound_external,li,
 p_local,LINV,V293_irq_bound_li,V293_shared_li in *;sep auto;apply V293_irq_bound_good.
Qed.
Theorem V293_irq_bound_builder_open : forall i ir si aop t lg,
 ipreasrt' i ir si aop Inv0 ** p_local li t lg ==>
 EX run,EX nest,EX locked,[|run<256 /\ nest<256 /\ locked<256|] **
 V293_irq_bound_snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t.
Proof.
 intros i ir si aop t lg st H.
 eapply astar_mono in H;[ |intros s K;exact K|apply V293_irq_bound_local_open].
 assert(B:st |=(ipreasrt' i ir si aop Inv0 ** p_local V293_shared_li t nil) ** globals)by(sep auto).
 apply V293_irq_entry_builder_open in B.
 destruct B as[run[nest[locked B]]];exists run;exists nest;exists locked.
 eapply astar_mono in B;[ |intros s K;exact K|apply V293_irq_bound_snapshot_pack];exact B.
Qed.
Definition V293_irq_bound_physical run nest locked t:=
 Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** (kept ** A_dom_lenv nil)))).
Lemma V293_irq_bound_physical_good : forall run nest locked t,
 GoodFrm(V293_irq_bound_physical run nest locked t).
Proof.
 intros;unfold V293_irq_bound_physical;split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
 - apply V293_exact_local_frame;apply V293_irq_bound_good.
 - split;[apply V293_quiet_irq_kept_good|exact Logic.I].
Qed.
Lemma V293_irq_bound_prefix : forall Spec sd r ri enter i ir si aop t id run nest locked,
 run<256 ->nest<256 ->locked<256 ->Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd li Inv0 r ri
 (V293_irq_bound_snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t)
 (sseq(sprim(eoi id))(scall enter nil))
 (V293_irq_bound_snapshot run(V293_interrupt_nest_after run nest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t)t.
Proof.
 intros Spec sd r ri enter i ir si aop t id run nest locked Run Nest Lock Enter Bound Index.
 eapply seq_rule with(p':=V293_irq_bound_snapshot run nest locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||aop||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_irq_bound_physical run nest locked t)
   (q:=<||aop||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_irq_bound_physical run nest locked t).
   + unfold V293_irq_bound_snapshot,external,V293_enter_bound_external,V293_irq_bound_physical;intros s H;sep auto.
   + unfold V293_irq_bound_snapshot,external,V293_enter_bound_external,V293_irq_bound_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_irq_bound_physical_good].
 - unfold V293_irq_bound_snapshot,external;apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
   split;[apply V293_quiet_irq_kept_good|exact Logic.I].
Qed.
Definition V293_irq_bound_after i ir si aop t:=
 EX run,EX oldnest,EX locked,[|run<256 /\ oldnest<256 /\ locked<256|] **
 V293_irq_bound_snapshot run(V293_interrupt_nest_after run oldnest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t.
Theorem V293_interrupt_bound_entry : forall Spec sd r ri enter intspec i ir si aop t lg pre id,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si Inv0 li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd li Inv0 r ri pre
 (sseq(sprim(eoi id))(scall enter nil))(V293_irq_bound_after i ir si aop t)t.
Proof.
 intros Spec sd r ri enter intspec i ir si aop t lg pre id Lookup Pre Enter Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule;[apply V293_irq_bound_builder_open|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Run[Nest Lock]].
 eapply conseq_rule;[intros s H;exact H| |eapply V293_irq_bound_prefix;try eassumption].
 intros s H;unfold V293_irq_bound_after;exists run;exists nest;exists locked;sep auto.
Qed.
End BoundEntry.
