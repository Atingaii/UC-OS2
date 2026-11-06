(* The selected LocalInv is constant Aemp: every logic witness has the same
   exact footprint. Keep that footprint rather than hiding a frame in Atrue. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFunctionEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.toptheorem.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_local_witness_identity : forall tid lg,
 p_local V293_shared_li tid lg=p_local V293_shared_li tid nil.
Proof. reflexivity. Qed.
Lemma V293_local_current_extend : forall tid extra,
 p_local V293_shared_li tid nil ** extra ==> CurLINV V293_shared_li tid.
Proof.
 intros tid extra st H;exists(@nil logicvar);unfold p_local in H;sep auto.
Qed.
Section ExactEnter.
Variables br bg bp brun bn:block.
Variables running nesting target:var.
Variable tp:type.
Variables prefix suffix:list(addr*type).
Let cells:=prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8)]++suffix.
Let Inv0:=V293_ready_storage_inv br bg bp target tp cells.
Definition V293_enter_local_boundary aop si ci tid :=
 <||aop||> ** ((SWINV Inv0 ** (Ais si ** Acs ci)) **
 (V293_interrupt_globals running nesting brun bn ** p_local V293_shared_li tid nil)).
Definition V293_enter_local_kept si ci tid :=
 V293_interrupt_globals running nesting brun bn **
 (V293_shared_flags ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target tp ** (V293_storage prefix ** V293_storage suffix))) **
 (Ais si ** Acs ci ** (p_local V293_shared_li tid nil ** A_dom_lenv nil))).
Definition V293_enter_local_open aop si ci tid run nest :=
 <||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run nest)
 (V293_enter_local_kept si ci tid).

Lemma V293_enter_local_extract : forall aop si ci tid,
 V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil ==>
 EX run,EX nest,[|run<256 /\ nest<256|] ** V293_enter_local_open aop si ci tid run nest.
Proof.
 intros aop si ci tid st H;unfold V293_enter_local_boundary in H.
 assert(S:st |= SWINV Inv0 ** (<||aop||> ** Ais si ** Acs ci **
 V293_interrupt_globals running nesting brun bn ** p_local V293_shared_li tid nil ** A_dom_lenv nil))by(sep auto).
 eapply astar_mono in S;[ |apply V293_ready_storage_switch_open|intros s K;exact K].
 unfold V293_ready_storage_core,V293_ready_storage_extra in S.
 assert(K:st |= V293_storage cells **
 (V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp **
 (<||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil)))by(sep auto).
 eapply astar_mono in K;[ |apply V293_storage_split|intros s T;exact T].
 unfold cells in K;cbn[V293_storage]in K.
 assert(K2:st |= V293_storage_cell(brun,0%Z)Tint8 **
 (V293_storage_cell(bn,0%Z)Tint8 **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil)))by(clear H S;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K2;sep destruct K2.
 assert(K3:st |= V293_storage_cell(bn,0%Z)Tint8 **
 ([|x<256|] ** Amapsto(brun,0%Z)Tint8 true(V293_byteval x) **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil)))by(clear H S K;sep auto).
 eapply astar_mono in K3;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K3;sep destruct K3.
 exists x;exists x0;unfold V293_enter_local_open,V293_enter_local_kept,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];clear H S K K2;sep auto.
Qed.

Lemma V293_enter_local_close : forall aop si ci tid run nest,
 run<256 ->nest<256 ->V293_enter_local_open aop si ci tid run nest ==>
 V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil.
Proof.
 intros aop si ci tid run nest Br Bn st H.
 unfold V293_enter_local_open,V293_enter_local_kept,V293_interrupt_cells in H;
 cbn[V293_rdy_raw_cells]in H.
 assert(K:st |= Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil)))by(sep auto).
 eapply astar_mono in K;[ |apply V293_storage_byte_close;exact Br|intros s T;exact T].
 assert(K2:st |= Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (V293_storage_cell(brun,0%Z)Tint8 **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil)))by(clear H;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_byte_close;exact Bn|intros s T;exact T].
 assert(K3:st |= (V293_storage prefix ** V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8)]++suffix)) **
 (V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp **
 <||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil))by(cbn[app V293_storage];clear H K;sep auto).
 eapply astar_mono in K3;[ |apply V293_storage_append|intros s T;exact T].
 assert(K4:st |= (V293_shared_flags ** V293_ready_storage_core br bg bp target tp cells) **
 (<||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 p_local V293_shared_li tid nil ** A_dom_lenv nil))by(unfold V293_ready_storage_core,V293_ready_storage_extra,cells;clear H K K2;sep auto).
 eapply astar_mono in K4;[ |apply V293_ready_storage_switch_close|intros s T;exact T].
 unfold V293_enter_local_boundary;clear H K K2 K3;sep auto.
Qed.
Lemma V293_enter_local_env : forall si ci tid st,
 st |= V293_enter_local_kept si ci tid ->
 V293_interrupt_env running nesting brun bn(getgenv st)(getlenv st).
Proof.
 intros si ci tid st H;unfold V293_enter_local_kept in H.
 assert(D:st |= A_dom_lenv nil ** Atrue)by(sep auto).
 apply astar_l_adomlenv_elim in D;destruct D as[D _].
 assert(G: get(getgenv st)running=Some(brun,Tint8) /\
 get(getgenv st)nesting=Some(bn,Tint8)).
 { eapply V293_star_env_l with(E:=fun ge le=>get ge running=Some(brun,Tint8) /\ get ge nesting=Some(bn,Tint8));[ |exact H]. intros s [G1 G2].
   apply agvarenv_elim in G1;apply agvarenv_elim in G2.
   change(EnvMod.get(getgenv s)running=Some(brun,Tint8) /\
    EnvMod.get(getgenv s)nesting=Some(bn,Tint8));tauto. }
 unfold V293_interrupt_env;repeat split;try apply V293_interrupt_empty_local;try exact D;tauto.
Qed.
Theorem V293_OSIntEnter_local_updates : forall Spec sd r ri aop si ci tid,
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil)
 (V293_OSIntEnter_updates running nesting)
 (V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros;eapply conseq_rule;[apply V293_enter_local_extract|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Br Bn].
 eapply conseq_rule;[intros s H;exact H|apply V293_enter_local_close;[exact Br|apply V293_interrupt_nest_bound;exact Bn]| ].
 apply V293_OSIntEnter_updates_hoare;[exact Br|exact Bn|apply V293_enter_local_env| ].
 unfold V293_enter_local_kept.
 intros st Held;apply V293_local_current_extend with(extra:=Atrue);sep auto.
Qed.

Theorem V293_OSIntEnter_local_body : forall Spec sd aop si ci tid,
 InfRules Spec sd V293_shared_li Inv0
 (fun result=>Aemp ** (([|result=None|] ** V293_enter_local_boundary aop si ci tid) ** A_dom_lenv nil))
 Afalse (Aemp ** (V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil))
 (V293_OSIntEnter_body running nesting) Afalse tid.
Proof.
 intros;unfold V293_OSIntEnter_body;eapply seq_rule.
 - eapply conseq_rule;[ |intros s H;exact H|apply V293_OSIntEnter_local_updates].
   intros s H;sep auto.
 - apply ret_rule;intros s H;sep auto.
Qed.
Lemma V293_enter_local_boundary_good : forall aop si ci tid,
 GoodFunAsrt(V293_enter_local_boundary aop si ci tid).
Proof.
 intros;unfold V293_enter_local_boundary;split;[exact I|split].
 - apply V293_sched_critical_good.
 - split;[unfold V293_interrupt_globals;cbn[GoodFunAsrt];auto| ].
   unfold p_local,LINV,V293_shared_li,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFunAsrt];intros;repeat split;exact I.
Qed.
Definition V293_enter_local_pre tid lg :=
 match V293_enter_ready_args lg with
 | Some(aop,si,ci)=>V293_enter_local_boundary aop si ci tid
 | None=>Afalse end.
Definition V293_enter_local_post tid lg (result:option val) :=
 match V293_enter_ready_args lg with
 | Some(aop,si,ci)=>[|result=None|] ** V293_enter_local_boundary aop si ci tid
 | None=>Afalse end.
Definition V293_enter_local_fpre:fpre.
Proof.
 intros vl lg tid;refine(@mkfunasrt(V293_enter_local_pre tid lg)_).
 unfold V293_enter_local_pre;destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [apply V293_enter_local_boundary_good|exact I].
Defined.
Definition V293_enter_local_fpost:fpost.
Proof.
 intros vl result lg tid;refine(@mkfunasrt(V293_enter_local_post tid lg result)_).
 unfold V293_enter_local_post;destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [split;[exact I|apply V293_enter_local_boundary_good]|exact I].
Defined.
Theorem V293_OSIntEnter_local_contract : forall P f Spec sd lg tid vl pre post,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 Some pre=BuildPreI P f vl lg V293_enter_local_fpre tid ->
 Some post=BuildRetI P f vl lg V293_enter_local_fpost tid ->
 InfRules Spec sd V293_shared_li Inv0 post Afalse pre
 (V293_OSIntEnter_body running nesting) Afalse tid.
Proof.
 intros P f Spec sd lg tid vl pre post Code Pre Post.
 unfold BuildPreI in Pre;rewrite Code in Pre.
 destruct vl as[ |v vl].
 2:{ assert(E:dl_vl_match dnil(rev(v::vl))=false).
     { destruct(rev(v::vl))eqn:E;[ |reflexivity].
       apply(f_equal(@rev val))in E;rewrite rev_involutive in E;discriminate. }
     unfold V293_OSIntEnter_function in Pre;rewrite E in Pre;discriminate. }
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons dl_vl_match buildp good_decllist getlenvdom V293_enter_local_fpre getasrt]in Pre.
 change(Some pre=Some(Aemp ** (V293_enter_local_pre tid lg ** A_dom_lenv nil)))in Pre.
 inversion Pre;subst pre;unfold BuildRetI in Post;rewrite Code in Post.
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons buildq good_decllist getlenvdom V293_enter_local_fpost getasrt]in Post.
 change(Some post=Some(fun result=>Aemp ** (V293_enter_local_post tid lg result ** A_dom_lenv nil)))in Post.
 inversion Post;subst post;unfold V293_enter_local_pre,V293_enter_local_post.
 destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [apply V293_OSIntEnter_local_body|apply V293_interrupt_false_entry].
Qed.
Lemma V293_enter_local_boundary_local : forall aop si ci tid,
 V293_enter_local_boundary aop si ci tid ==>CurLINV V293_shared_li tid.
Proof.
 intros aop si ci tid st H;unfold V293_enter_local_boundary in H.
 apply V293_local_current_extend with(extra:=Atrue);sep auto.
Qed.
Theorem V293_OSIntEnter_local_call : forall Spec sd r ri enter aop si ci tid,
 Spec enter=Some(V293_enter_local_fpre,V293_enter_local_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil)
 (scall enter nil)
 (V293_enter_local_boundary aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros Spec sd r ri enter aop si ci tid HS.
 assert(Ep:getasrt(V293_enter_local_fpre nil(V293_enter_ready_call_lg aop si ci)tid)=
 V293_enter_local_boundary aop si ci tid)by reflexivity.
 assert(Eq:forall result,getasrt(V293_enter_local_fpost nil result(V293_enter_ready_call_lg aop si ci)tid)=
 [|result=None|] ** V293_enter_local_boundary aop si ci tid)by reflexivity.
 eapply conseq_rule with(q:=EX result:option val,
 getasrt(V293_enter_local_fpost nil result(V293_enter_ready_call_lg aop si ci)tid) ** A_dom_lenv nil).
 - intros s H;exact H.
 - intros s[result H];rewrite Eq in H;sep auto.
 - eapply call_rule with(pre:=V293_enter_local_fpre)(post:=V293_enter_local_fpost)
   (vl:=nil)(logicl:=V293_enter_ready_call_lg aop si ci)(tp:=Tvoid)(tl:=nil).
   + exact I.
   + exact HS.
   + rewrite Ep;intros s H;exact H.
   + intros s H;reflexivity.
   + reflexivity.
   + rewrite Ep;apply V293_enter_local_boundary_local.
   + intros s[result H];rewrite Eq in H;apply astar_l_apure_elim in H.
     destruct H as[_ H];eapply V293_enter_local_boundary_local;exact H.
Qed.

Lemma V293_irq_local_enter_pre : forall i si aop tid lg,
 V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn ==>
 V293_enter_local_boundary aop(i::si)nil tid ** A_dom_lenv nil.
Proof.
 intros i si aop tid lg st H;unfold V293_irq_ready_closed,V293_enter_local_boundary in *.
 rewrite V293_local_witness_identity in H;sep auto.
Qed.
Lemma V293_irq_local_enter_post : forall i si aop tid lg,
 V293_enter_local_boundary aop(i::si)nil tid ** A_dom_lenv nil ==>
 V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn.
Proof.
 intros i si aop tid lg st H;unfold V293_irq_ready_closed,V293_enter_local_boundary in *.
 rewrite V293_local_witness_identity;sep auto.
Qed.
Theorem V293_irq_local_enter_call : forall Spec sd r ri enter i si aop tid lg,
 Spec enter=Some(V293_enter_local_fpre,V293_enter_local_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn)
 (scall enter nil)
 (V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn)tid.
Proof.
 intros;eapply conseq_rule;[apply V293_irq_local_enter_pre|apply V293_irq_local_enter_post| ].
 apply V293_OSIntEnter_local_call;assumption.
Qed.
Theorem V293_irq_local_return_resources : forall i ir si tid lg,
 (forall j,ir j=false) ->
 V293_enter_local_boundary(spec_done None)(i::si)nil tid ** A_dom_lenv nil ==>
 (iretasrt' i ir si Inv0 ** p_local V293_shared_li tid lg) **
 V293_interrupt_globals running nesting brun bn.
Proof.
 intros i ir si tid lg Clear st Held.
 apply(V293_irq_local_enter_post i si(spec_done None)tid lg)in Held.
 eapply astar_mono in Held;[exact Held|apply V293_irq_ready_return_resources;exact Clear|intros s H;exact H].
Qed.
(* The actual two-statement prefix only; Exit and the ISR abstract action
   are not omitted from any claimed whole-handler theorem. *)
Theorem V293_irq_local_eoi_enter : forall Spec sd r ri enter intspec i ir si tid lg pre id,
 Spec enter=Some(V293_enter_local_fpre,V293_enter_local_fpost,(Tvoid,nil)) ->
 intspec i<>None ->Some pre=BuildintPre i intspec ir si Inv0 V293_shared_li tid lg ->
 (forall j,ir j=false) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (pre ** V293_interrupt_globals running nesting brun bn)
 (sseq(sprim(eoi id))(scall enter nil))
 (V293_irq_ready_closed br bg bp target tp cells i si
 (match intspec i with Some a=>a|None=>spec_done None end)tid lg **
 V293_interrupt_globals running nesting brun bn)tid.
Proof.
 intros Spec sd r ri enter intspec i ir si tid lg pre id Entry Defined Pre Clear Bound Index.
 destruct(intspec i)as[ispec| ]eqn:Lookup;[ |contradiction].
 eapply seq_rule;[ |apply V293_irq_local_enter_call;exact Entry].
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule with
 (p:=<||ispec||> ** OS[isrupd ir i true,false,i::si,nil] **
 (V293_irq_ready_frame br bg bp target tp cells tid lg **
 V293_interrupt_globals running nesting brun bn))
 (q:=<||ispec||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] **
 (V293_irq_ready_frame br bg bp target tp cells tid lg **
 V293_interrupt_globals running nesting brun bn)).
 - intros st Held;eapply astar_mono in Held;
   [ |apply V293_irq_ready_builder_resources|intros s H;exact H];sep auto.
 - intros st Held;rewrite(V293_irq_clear_update ir i Clear)in Held.
   assert(Open:st |= V293_irq_ready_open br bg bp target tp cells i si ispec tid lg **
    V293_interrupt_globals running nesting brun bn)by(unfold V293_irq_ready_open;sep auto).
   eapply astar_mono in Open;[exact Open|apply V293_irq_ready_open_close|intros s H;exact H].
 - apply eoi_ieoff_rule;[exact Bound|exact Index| ].
   split;[apply V293_irq_ready_frame_good| ].
   unfold V293_interrupt_globals;cbn[GoodFrm];auto.
Qed.
End ExactEnter.

Section ExactInterruptEnvironment.
Variables unmap group rows high table target current counter running nesting lock saved:var.
Variables bt bg br bh bp bo bc bk brun bn bl:block.
Variable rest:list(addr*type).
Variable extra:asrt.
Variable EG:GoodFunAsrt extra.
Let tp:=V293_tcb_type.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let Hli:=V293_switch_li_good.
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let suffix:=V293_ready_irq_suffix bl rest.
Let efp:=V293_enter_local_fpre br bg bp brun bn running nesting target tp
 prefix suffix.
Let efq:=V293_enter_local_fpost br bg bp brun bn running nesting target tp
 prefix suffix.
Let xfp:=V293_ready_dynamic_exit_fpre unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let xfq:=V293_ready_dynamic_exit_fpost unmap group rows high table target current counter running nesting lock
 bt bg br bh bp bo bc bk brun bn bl rest extra EG.
Let sfp:=V293_joint_sched_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Let sfq:=V293_joint_sched_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv Inv0 Hli.
Definition V293_ready_local_spec exit enter sched:funspec:=
 fun f=>if Z.eq_dec f exit then Some(xfp,xfq,(Tvoid,nil))
 else if Z.eq_dec f enter then Some(efp,efq,(Tvoid,nil))
 else if Z.eq_dec f sched then Some(sfp,sfq,(Tvoid,nil))else None.
Lemma V293_ready_local_domains : forall exit enter sched y,
 EqDom(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_ready_local_spec exit enter sched).
Proof.
 intros exit enter sched y f.
 unfold V293_ready_irq_unit,V293_exit_env_unit,V293_irq_internal_unit,pumerge,
 V293_OSIntEnter_unit,V293_OSSchedNew_internal_unit,V293_ready_local_spec.
 destruct(Z.eq_dec f exit),(Z.eq_dec f enter),(Z.eq_dec f sched);
 split;intros[x H];try discriminate;eexists;reflexivity.
Qed.
Theorem V293_ready_local_WFFunEnv : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFFunEnv(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_ready_local_spec exit enter sched)
 V293_scheduler V293_shared_li Inv0.
Proof.
 intros exit enter sched y XE XS ES UY GY RY HY T H G C K N L R GF.
 pose proof(V293_exit_env_entries exit enter sched running nesting unmap group rows high y saved
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched
 (V293_interrupt_handoff high current target)) XE XS ES)as(CodeX&CodeE&CodeS).
 assert(Sched:V293_ready_local_spec exit enter sched sched=Some(sfp,sfq,(Tvoid,nil))).
 { unfold V293_ready_local_spec;repeat destruct Z.eq_dec;try congruence;reflexivity. }
 split;[apply V293_ready_local_domains| ].
 intros f pre post t tl Lookup;unfold V293_ready_local_spec in Lookup.
 destruct(Z.eq_dec f exit)as[E|NE].
 - subst f;inversion Lookup;subst pre post t tl.
   exists dnil;exists(dcons saved Tint32 dnil).
   exists(V293_exit_boundary_body running nesting lock saved table high target current counter sched
   (V293_interrupt_handoff high current target)).
   split;[exact CodeX| ];split;[constructor| ];split;[reflexivity| ].
   intros vl p q lg t Pre Post.
   eapply V293_OSIntExit_ready_dynamic_builder_contract;try eassumption.
 - destruct(Z.eq_dec f enter)as[E|NEE].
   + subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting).
     split;[exact CodeE| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     unfold Inv0;rewrite <-V293_ready_irq_inv_layout.
     eapply V293_OSIntEnter_local_contract;try eassumption.
   + destruct(Z.eq_dec f sched)as[E|NES];[ |discriminate].
     subst f;inversion Lookup;subst pre post t tl.
     exists dnil;exists(dcons y Tint8 dnil);exists(V293_OSSchedNew_body unmap group rows high y).
     split;[exact CodeS| ];split;[constructor| ];split;[reflexivity| ].
     intros vl p q lg t Pre Post.
     eapply(V293_OSSchedNew_joint_contract unmap group rows high bt bg br bh
     V293_shared_li V293_opened_inv Inv0 Hli);try eassumption.
Qed.
Theorem V293_ready_local_WFIFun : forall exit enter sched y,
 exit<>enter ->exit<>sched ->enter<>sched ->
 unmap<>y ->group<>y ->rows<>y ->high<>y ->
 table<>saved ->high<>saved ->target<>saved ->current<>saved ->
 counter<>saved ->nesting<>saved ->lock<>saved ->running<>saved ->
 GoodFrm extra ->
 WFIFun(V293_ready_irq_unit unmap group rows high table target current counter running nesting lock saved exit enter sched y)(V293_ready_local_spec exit enter sched)
 V293_scheduler Inv0 V293_shared_li.
Proof.
 intros;destruct(V293_ready_local_WFFunEnv exit enter sched y
 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)as[Dom Body].
 split;[exact Dom| ];intros f p q t tl Lookup.
 destruct(Body f p q t tl Lookup)as(d1&d2&s&Code&Types&Decls&Checked).
 exists d1;exists d2;exists s;auto.
Qed.
Theorem V293_ready_local_Enter_call : forall exit enter sched r ri aop si ci tid,
 exit<>enter ->
 InfRules(V293_ready_local_spec exit enter sched)V293_scheduler V293_shared_li Inv0 r ri
 (V293_enter_local_boundary br bg bp brun bn running nesting target tp
 prefix suffix aop si ci tid ** A_dom_lenv nil)
 (scall enter nil)
 (V293_enter_local_boundary br bg bp brun bn running nesting target tp
 prefix suffix aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros;unfold Inv0;rewrite <-V293_ready_irq_inv_layout;apply V293_OSIntEnter_local_call.
 unfold V293_ready_local_spec;repeat destruct Z.eq_dec;try congruence;reflexivity.
Qed.
End ExactInterruptEnvironment.
