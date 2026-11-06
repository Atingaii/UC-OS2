Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_storage_byte_value : forall v,
 rule_type_val_match Tint8 v=true ->exists n,n<256 /\ v=V293_byteval n.
Proof.
 intros v T;destruct v;try discriminate.
 exists(Z.to_nat(Int.unsigned i));split.
 - cbn[rule_type_val_match]in T.
   destruct((Int.unsigned i<=?Byte.max_unsigned)%Z)eqn:B;[ |discriminate].
   apply Z.leb_le in B.
   pose proof(Int.unsigned_range i);change (Int.unsigned i<=255)%Z in B;lia.
 - unfold V293_byteval;rewrite Z2Nat.id by apply Int.unsigned_range_2.
   rewrite Int.repr_unsigned;reflexivity.
Qed.
Lemma V293_storage_split : forall left right,
 V293_storage(left++right) ==> V293_storage left ** V293_storage right.
Proof.
 induction left as[ |[a tau]tail IH];intros right st H;cbn[V293_storage app]in *.
 - apply astar_l_aemp_intro;exact H.
 - apply astar_assoc_intro;eapply astar_mono;[intros s K;exact K|apply IH|exact H].
Qed.
Lemma V293_storage_byte_open : forall a,
 V293_storage_cell a Tint8 ==>
 EX n,[|n<256|] ** Amapsto a Tint8 true(V293_byteval n).
Proof.
 intros a st[v H];apply astar_l_apure_elim in H;destruct H as[T H].
 destruct(V293_storage_byte_value v T)as(n&B&E);subst v.
 exists n;apply astar_l_apure_intro;assumption.
Qed.
Lemma V293_storage_byte_close : forall a n,
 n<256 ->Amapsto a Tint8 true(V293_byteval n) ==> V293_storage_cell a Tint8.
Proof.
 intros a n B st H;exists(V293_byteval n);apply astar_l_apure_intro;[exact H|apply V293_byte_type;exact B].
Qed.
Lemma V293_interrupt_nest_bound : forall run nest,
 nest<256 ->V293_interrupt_nest_after run nest<256.
Proof.
 intros run nest B;unfold V293_interrupt_nest_after.
 destruct(Nat.eqb run 1);simpl;[ |exact B].
 destruct(Nat.ltb nest 255)eqn:E;[apply Nat.ltb_lt in E;lia|exact B].
Qed.

Section SharedEnter.
Variables br bg bp brun bn:block.
Variables running nesting target:var.
Variable tp:type.
Variables prefix suffix:list(addr*type).
Let cells:=prefix++[((brun,0%Z),Tint8);((bn,0%Z),Tint8)]++suffix.
Let Inv0:=V293_ready_storage_inv br bg bp target tp cells.
Definition V293_enter_ready_boundary aop si ci tid :=
 <||aop||> ** ((SWINV Inv0 ** (Ais si ** Acs ci)) **
 (V293_interrupt_globals running nesting brun bn ** CurLINV V293_shared_li tid)).
Definition V293_enter_ready_kept si ci tid :=
 V293_interrupt_globals running nesting brun bn **
 (V293_shared_flags ** (V293ReadyTaskInvariant.V293_ready_core br bg bp **
 (V293_dispatch_cell target tp ** (V293_storage prefix ** V293_storage suffix))) **
 (Ais si ** Acs ci ** (CurLINV V293_shared_li tid ** A_dom_lenv nil))).
Definition V293_enter_ready_open aop si ci tid run nest :=
 <||aop||> ** V293_rdy_raw_cells(V293_interrupt_cells brun bn run nest)
 (V293_enter_ready_kept si ci tid).

Lemma V293_enter_ready_extract : forall aop si ci tid,
 V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil ==>
 EX run,EX nest,[|run<256 /\ nest<256|] ** V293_enter_ready_open aop si ci tid run nest.
Proof.
 intros aop si ci tid st H;unfold V293_enter_ready_boundary in H.
 assert(S:st |= SWINV Inv0 ** (<||aop||> ** Ais si ** Acs ci **
 V293_interrupt_globals running nesting brun bn ** CurLINV V293_shared_li tid ** A_dom_lenv nil))by(sep auto).
 eapply astar_mono in S;[ |apply V293_ready_storage_switch_open|intros s K;exact K].
 unfold V293_ready_storage_core,V293_ready_storage_extra in S.
 assert(K:st |= V293_storage cells **
 (V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp **
 (<||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil)))by(sep auto).
 eapply astar_mono in K;[ |apply V293_storage_split|intros s T;exact T].
 unfold cells in K;cbn[V293_storage]in K.
 assert(K2:st |= V293_storage_cell(brun,0%Z)Tint8 **
 (V293_storage_cell(bn,0%Z)Tint8 **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil)))by(clear H S;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K2;sep destruct K2.
 assert(K3:st |= V293_storage_cell(bn,0%Z)Tint8 **
 ([|x<256|] ** Amapsto(brun,0%Z)Tint8 true(V293_byteval x) **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil)))by(clear H S K;sep auto).
 eapply astar_mono in K3;[ |apply V293_storage_byte_open|intros s T;exact T].
 sep normal in K3;sep destruct K3.
 exists x;exists x0;unfold V293_enter_ready_open,V293_enter_ready_kept,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];clear H S K K2;sep auto.
Qed.

Lemma V293_enter_ready_close : forall aop si ci tid run nest,
 run<256 ->nest<256 ->V293_enter_ready_open aop si ci tid run nest ==>
 V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil.
Proof.
 intros aop si ci tid run nest Br Bn st H.
 unfold V293_enter_ready_open,V293_enter_ready_kept,V293_interrupt_cells in H;
 cbn[V293_rdy_raw_cells]in H.
 assert(K:st |= Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil)))by(sep auto).
 eapply astar_mono in K;[ |apply V293_storage_byte_close;exact Br|intros s T;exact T].
 assert(K2:st |= Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (V293_storage_cell(brun,0%Z)Tint8 **
 (V293_storage prefix ** V293_storage suffix ** V293_shared_flags **
 V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp ** <||aop||> **
 Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil)))by(clear H;sep auto).
 eapply astar_mono in K2;[ |apply V293_storage_byte_close;exact Bn|intros s T;exact T].
 assert(K3:st |= (V293_storage prefix ** V293_storage([((brun,0%Z),Tint8);((bn,0%Z),Tint8)]++suffix)) **
 (V293_shared_flags ** V293ReadyTaskInvariant.V293_ready_core br bg bp ** V293_dispatch_cell target tp **
 <||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil))by(cbn[app V293_storage];clear H K;sep auto).
 eapply astar_mono in K3;[ |apply V293_storage_append|intros s T;exact T].
 assert(K4:st |= (V293_shared_flags ** V293_ready_storage_core br bg bp target tp cells) **
 (<||aop||> ** Ais si ** Acs ci ** V293_interrupt_globals running nesting brun bn **
 CurLINV V293_shared_li tid ** A_dom_lenv nil))by(unfold V293_ready_storage_core,V293_ready_storage_extra,cells;clear H K K2;sep auto).
 eapply astar_mono in K4;[ |apply V293_ready_storage_switch_close|intros s T;exact T].
 unfold V293_enter_ready_boundary;clear H K K2 K3;sep auto.
Qed.
Lemma V293_enter_ready_env : forall si ci tid st,
 st |= V293_enter_ready_kept si ci tid ->
 V293_interrupt_env running nesting brun bn(getgenv st)(getlenv st).
Proof.
 intros si ci tid st H;unfold V293_enter_ready_kept in H.
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
Theorem V293_OSIntEnter_ready_updates : forall Spec sd r ri aop si ci tid,
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil)
 (V293_OSIntEnter_updates running nesting)
 (V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros;eapply conseq_rule;[apply V293_enter_ready_extract|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Br Bn].
 eapply conseq_rule;[intros s H;exact H|apply V293_enter_ready_close;[exact Br|apply V293_interrupt_nest_bound;exact Bn]| ].
 apply V293_OSIntEnter_updates_hoare;[exact Br|exact Bn|apply V293_enter_ready_env| ].
 unfold V293_enter_ready_kept.
 intros st Held;apply V293_CurLINV_extend with(extra:=Atrue);sep auto.
Qed.

Theorem V293_OSIntEnter_ready_body : forall Spec sd aop si ci tid,
 InfRules Spec sd V293_shared_li Inv0
 (fun result=>Aemp ** (([|result=None|] ** V293_enter_ready_boundary aop si ci tid) ** A_dom_lenv nil))
 Afalse (Aemp ** (V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil))
 (V293_OSIntEnter_body running nesting) Afalse tid.
Proof.
 intros;unfold V293_OSIntEnter_body;eapply seq_rule.
 - eapply conseq_rule;[ |intros s H;exact H|apply V293_OSIntEnter_ready_updates].
   intros s H;sep auto.
 - apply ret_rule;intros s H;sep auto.
Qed.
Lemma V293_enter_ready_boundary_good : forall aop si ci tid,
 GoodFunAsrt(V293_enter_ready_boundary aop si ci tid).
Proof.
 intros;unfold V293_enter_ready_boundary;split;[exact I|split].
 - apply V293_sched_critical_good.
 - split;[unfold V293_interrupt_globals;cbn[GoodFunAsrt];auto| ].
   apply V293_CurLINV_function_assertion;apply V293_switch_li_good.
Qed.
Definition V293_enter_ready_args(lg:list logicvar):option(spec_code*is*cs):=
 match lg with
 | [logic_code aop;logic_is si;logic_cs ci]=>Some(aop,si,ci)
 | _=>None end.
Definition V293_enter_ready_pre tid lg :=
 match V293_enter_ready_args lg with
 | Some(aop,si,ci)=>V293_enter_ready_boundary aop si ci tid
 | None=>Afalse end.
Definition V293_enter_ready_post tid lg (result:option val) :=
 match V293_enter_ready_args lg with
 | Some(aop,si,ci)=>[|result=None|] ** V293_enter_ready_boundary aop si ci tid
 | None=>Afalse end.
Definition V293_enter_ready_fpre:fpre.
Proof.
 intros vl lg tid;refine(@mkfunasrt(V293_enter_ready_pre tid lg)_).
 unfold V293_enter_ready_pre;destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [apply V293_enter_ready_boundary_good|exact I].
Defined.
Definition V293_enter_ready_fpost:fpost.
Proof.
 intros vl result lg tid;refine(@mkfunasrt(V293_enter_ready_post tid lg result)_).
 unfold V293_enter_ready_post;destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [split;[exact I|apply V293_enter_ready_boundary_good]|exact I].
Defined.
Theorem V293_OSIntEnter_ready_contract : forall P f Spec sd lg tid vl pre post,
 P f=Some(V293_OSIntEnter_function running nesting) ->
 Some pre=BuildPreI P f vl lg V293_enter_ready_fpre tid ->
 Some post=BuildRetI P f vl lg V293_enter_ready_fpost tid ->
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
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons dl_vl_match buildp good_decllist getlenvdom V293_enter_ready_fpre getasrt]in Pre.
 change(Some pre=Some(Aemp ** (V293_enter_ready_pre tid lg ** A_dom_lenv nil)))in Pre.
 inversion Pre;subst pre;unfold BuildRetI in Post;rewrite Code in Post.
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons buildq good_decllist getlenvdom V293_enter_ready_fpost getasrt]in Post.
 change(Some post=Some(fun result=>Aemp ** (V293_enter_ready_post tid lg result ** A_dom_lenv nil)))in Post.
 inversion Post;subst post;unfold V293_enter_ready_pre,V293_enter_ready_post.
 destruct(V293_enter_ready_args lg)as[[[aop si]ci]| ];
 [apply V293_OSIntEnter_ready_body|apply V293_interrupt_false_entry].
Qed.
Definition V293_enter_ready_spec(enter:fid):funspec:=
 fun f=>if Z.eq_dec f enter then Some(V293_enter_ready_fpre,V293_enter_ready_fpost,(Tvoid,nil))else None.
Theorem V293_OSIntEnter_ready_WFFunEnv : forall enter sd,
 WFFunEnv(V293_OSIntEnter_unit enter running nesting)(V293_enter_ready_spec enter)
 sd V293_shared_li Inv0.
Proof.
 intros;split.
 - intros f;unfold V293_OSIntEnter_unit,V293_enter_ready_spec.
   destruct(Z.eq_dec f enter);split;intros[a H];try discriminate;eexists;reflexivity.
 - intros f pre post t tl HS;unfold V293_enter_ready_spec in HS.
   destruct(Z.eq_dec f enter);try discriminate;inversion HS;subst pre post t tl.
   exists dnil;exists dnil;exists(V293_OSIntEnter_body running nesting);split.
   + unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
   + split;[constructor| ];split;[reflexivity| ].
     intros vl pre post lg tid Pre Post;eapply V293_OSIntEnter_ready_contract;try eassumption.
     unfold V293_OSIntEnter_unit;destruct(Z.eq_dec f enter);[reflexivity|contradiction].
Qed.
Theorem V293_OSIntEnter_ready_builders : forall enter lg tid,
 exists pre post,
 Some pre=BuildPreI(V293_OSIntEnter_unit enter running nesting)enter nil lg V293_enter_ready_fpre tid /\
 Some post=BuildRetI(V293_OSIntEnter_unit enter running nesting)enter nil lg V293_enter_ready_fpost tid.
Proof.
 intros;unfold BuildPreI,BuildRetI,V293_OSIntEnter_unit.
 destruct(Z.eq_dec enter enter);[ |contradiction];eexists;eexists;split;reflexivity.
Qed.
Definition V293_enter_ready_call_lg aop si ci:list logicvar :=
 [logic_code aop;logic_is si;logic_cs ci].
Lemma V293_enter_ready_boundary_local : forall aop si ci tid,
 V293_enter_ready_boundary aop si ci tid ==>CurLINV V293_shared_li tid.
Proof.
 intros aop si ci tid st H;unfold V293_enter_ready_boundary in H.
 apply V293_CurLINV_extend with(extra:=Atrue);sep auto.
Qed.
Theorem V293_OSIntEnter_ready_call : forall Spec sd r ri enter aop si ci tid,
 Spec enter=Some(V293_enter_ready_fpre,V293_enter_ready_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil)
 (scall enter nil)
 (V293_enter_ready_boundary aop si ci tid ** A_dom_lenv nil)tid.
Proof.
 intros Spec sd r ri enter aop si ci tid HS.
 assert(Ep:getasrt(V293_enter_ready_fpre nil(V293_enter_ready_call_lg aop si ci)tid)=
 V293_enter_ready_boundary aop si ci tid)by reflexivity.
 assert(Eq:forall result,getasrt(V293_enter_ready_fpost nil result(V293_enter_ready_call_lg aop si ci)tid)=
 [|result=None|] ** V293_enter_ready_boundary aop si ci tid)by reflexivity.
 eapply conseq_rule with(q:=EX result:option val,
 getasrt(V293_enter_ready_fpost nil result(V293_enter_ready_call_lg aop si ci)tid) ** A_dom_lenv nil).
 - intros s H;exact H.
 - intros s[result H];rewrite Eq in H;sep auto.
 - eapply call_rule with(pre:=V293_enter_ready_fpre)(post:=V293_enter_ready_fpost)
   (vl:=nil)(logicl:=V293_enter_ready_call_lg aop si ci)(tp:=Tvoid)(tl:=nil).
   + exact I.
   + exact HS.
   + rewrite Ep;intros s H;exact H.
   + intros s H;reflexivity.
   + reflexivity.
   + rewrite Ep;apply V293_enter_ready_boundary_local.
   + intros s[result H];rewrite Eq in H;apply astar_l_apure_elim in H.
     destruct H as[_ H];eapply V293_enter_ready_boundary_local;exact H.
Qed.

Lemma V293_irq_ready_enter_boundary : forall i si aop tid lg,
 V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn ==>
 V293_enter_ready_boundary aop(i::si)nil tid ** A_dom_lenv nil.
Proof.
 intros i si aop tid lg st H;unfold V293_irq_ready_closed in H.
 assert(Convert:p_local V293_shared_li tid lg ==>CurLINV V293_shared_li tid).
 { intros s K;exists lg;unfold p_local in K;sep auto. }
 unfold V293_enter_ready_boundary.
 assert(Pack:st |= p_local V293_shared_li tid lg **
 (<||aop||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil ** A_dom_lenv nil **
 V293_interrupt_globals running nesting brun bn))by(sep auto).
 eapply astar_mono in Pack;[ |exact Convert|intros s K;exact K];clear H;sep auto.
Qed.
Theorem V293_irq_ready_enter_call : forall Spec sd r ri enter i si aop tid lg,
 Spec enter=Some(V293_enter_ready_fpre,V293_enter_ready_fpost,(Tvoid,nil)) ->
 InfRules Spec sd V293_shared_li Inv0 r ri
 (V293_irq_ready_closed br bg bp target tp cells i si aop tid lg **
 V293_interrupt_globals running nesting brun bn)
 (scall enter nil)
 (V293_enter_ready_boundary aop(i::si)nil tid ** A_dom_lenv nil)tid.
Proof.
 intros;eapply conseq_rule;[apply V293_irq_ready_enter_boundary|intros s K;exact K| ].
 apply V293_OSIntEnter_ready_call;assumption.
Qed.
End SharedEnter.
