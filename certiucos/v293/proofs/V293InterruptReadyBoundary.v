Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Local Open Scope nat_scope.

(* Only the endpoints of the original ISR wrapper are established here. *)
Lemma V293_irq_clear_update : forall ir i,
 (forall j,ir j=false) ->
 isrupd(isrupd ir i true)i false=(fun _:hid=>false).
Proof.
 intros ir i Clear;apply functional_extensionality;intro j.
 unfold isrupd;destruct(Nat.eqb i j);auto.
Qed.
Lemma V293_irq_other_bit_survives : forall ir i j,
 i<>j ->ir j=true ->isrupd(isrupd ir i true)i false j=true.
Proof.
 intros ir i j Apart Active;unfold isrupd.
 assert(Nat.eqb i j=false)by(apply Nat.eqb_neq;exact Apart).
 rewrite H;exact Active.
Qed.

Section ReadyIRQBoundary.
Variables br bg bp:block.
Variable target:var.
Variable tp:type.
Variable cells:list(addr*type).
Let Inv0:=V293_ready_storage_inv br bg bp target tp cells.
Let core:=V293_ready_storage_core br bg bp target tp cells.
Definition V293_irq_ready_frame t lg:=
 core ** (A_dom_lenv nil ** p_local V293_shared_li t lg).
Definition V293_irq_ready_open i si aop t lg:=
 <||aop||> ** OS[(fun _:hid=>false),false,i::si,nil] ** V293_irq_ready_frame t lg.
Definition V293_irq_ready_closed i si aop t lg:=
 <||aop||> ** SWINV Inv0 ** Ais(i::si) ** Acs nil **
 (A_dom_lenv nil ** p_local V293_shared_li t lg).
Lemma V293_irq_ready_frame_good : forall t lg,GoodFrm(V293_irq_ready_frame t lg).
Proof.
 intros t lg;unfold V293_irq_ready_frame;split.
 - unfold core,V293_ready_storage_core;split.
   + unfold V293_ready_core;cbn[GoodFrm];intros ct ts es now.
     unfold V293_shared_ready_records;split.
     * split.
       -- unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
       -- unfold V293_shared_fields;cbn[GoodFrm];auto.
     * apply V293_ready_payload_frame.
   + unfold V293_ready_storage_extra;split.
     * unfold V293_dispatch_cell;intro v;cbn[GoodFrm];split;[exact I| ].
       unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
     * apply V293_storage_frame_good.
 - split;[exact I| ]. unfold p_local,LINV,V293_shared_li;split.
   + unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
   + cbn[GoodFrm];auto.
Qed.

(* starinv_noisr includes its low index even when the length argument is zero. *)
Theorem V293_irq_ready_builder_resources : forall i ir si ispec t lg,
 ipreasrt' i ir si ispec Inv0 ** p_local V293_shared_li t lg ==>
 <||ispec||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_irq_ready_frame t lg.
Proof.
 intros i ir si ispec t lg st Held.
 unfold ipreasrt',invlth_noisr in Held;rewrite Nat.sub_0_r in Held.
 assert(Raw:st |= starinv_noisr Inv0 0 i **
 (<||ispec||> ** OS[isrupd ir i true,false,i::si,nil] **
 (isr_inv ** (A_dom_lenv nil ** p_local V293_shared_li t lg))))by(sep auto).
 eapply astar_mono in Raw;[ |intros s H;apply V293_ready_storage_noisr_core in H;exact H|intros s H;exact H].
 unfold isr_inv in Raw;sep normal in Raw;sep destruct Raw.
 unfold V293_irq_ready_frame,core;clear Held;sep auto.
 destruct Raw as[Raw _].
 apply aisr_elim in Raw;exact(proj2 Raw).
Qed.

Theorem V293_irq_ready_eoi : forall Spec sd r ri intspec i ir si t lg pre id,
 intspec i<>None ->
 Some pre=BuildintPre i intspec ir si Inv0 V293_shared_li t lg ->
 (forall j,ir j=false) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri pre (sprim(eoi id))
 (V293_irq_ready_open i si (match intspec i with Some a=>a|None=>spec_done None end)t lg)t.
Proof.
 intros Spec sd r ri intspec i ir si t lg pre id Defined Pre Clear Bound Index.
 destruct(intspec i)as[ispec| ]eqn:Lookup;[ |contradiction].
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule with(q:=<||ispec||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_irq_ready_frame t lg).
 - apply V293_irq_ready_builder_resources.
 - intros st Held;unfold V293_irq_ready_open.
   rewrite(V293_irq_clear_update ir i Clear)in Held;exact Held.
 - apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_irq_ready_frame_good].
Qed.

Lemma V293_irq_ready_open_close : forall i si aop t lg,
 V293_irq_ready_open i si aop t lg ==> V293_irq_ready_closed i si aop t lg.
Proof.
 intros i si aop t lg st Held.
 unfold V293_irq_ready_open,V293_irq_ready_frame in Held.
 destruct st as [[[[[[ge le] M] ir] [[ie stack] cs]] O] op].
 assert(Raw:(ge,le,M,ir,(ie,stack,cs),O,op) |=
    Aisr(fun _:hid=>false) ** (Aie false ** (Ais(i::si) ** Atrue)))by(sep auto).
 apply astar_l_aisr_elim in Raw;destruct Raw as[IR Raw].
 apply astar_l_aie_elim in Raw;destruct Raw as[IE Raw].
 apply astar_l_ais_elim in Raw;destruct Raw as[IS Raw].
 assert(Convert:Aisr(fun _:hid=>false) ==> isrclr).
 { intros s H;exists(fun _:hid=>false);split;[exact H| ].
   apply apure_intro;[exact(proj2(@aisr_elim s (fun _:hid=>false) H))|reflexivity]. }
 assert(Raw2:(ge,le,M,ir,(ie,stack,cs),O,op) |=
  Aisr(fun _:hid=>false) **
  (<||aop||> ** Aie false ** Ais(i::si) ** Acs nil ** core **
  (A_dom_lenv nil ** p_local V293_shared_li t lg)))by(clear Raw;sep auto).
 eapply astar_mono in Raw2;[ |exact Convert|intros s H;exact H].
 apply astar_l_atopis_intro with(i:=i)in Raw2;[ |rewrite IS;reflexivity].
 assert(Pack:(ge,le,M,ir,(ie,stack,cs),O,op) |=
  (V293_shared_flags ** core) **
  (<||aop||> ** Ais(i::si) ** Acs nil ** (A_dom_lenv nil ** p_local V293_shared_li t lg))).
 { clear Held Raw;unfold V293_shared_flags;sep auto. }
 eapply astar_mono in Pack;[ |apply V293_ready_storage_switch_close|intros s H;exact H].
 unfold V293_irq_ready_closed;clear Held;sep auto.
Qed.

Theorem V293_irq_ready_eoi_closed : forall Spec sd r ri intspec i ir si t lg pre id,
 intspec i<>None ->Some pre=BuildintPre i intspec ir si Inv0 V293_shared_li t lg ->
 (forall j,ir j=false) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd V293_shared_li Inv0 r ri pre(sprim(eoi id))
 (V293_irq_ready_closed i si(match intspec i with Some a=>a|None=>spec_done None end)t lg)t.
Proof.
 intros;eapply conseq_rule;[intros s Hs;exact Hs|apply V293_irq_ready_open_close| ].
 eapply V293_irq_ready_eoi;eassumption.
Qed.

Lemma V293_irq_clear_isr_inv : forall k,
 isrclr ** ATopis k ==> isr_inv.
Proof.
 intros k st Held;unfold isrclr in Held;sep normal in Held;sep destruct Held.
 apply astar_l_aconj_elim in Held;destruct Held as[Raw Pure].
 apply astar_l_apure_elim in Pure;destruct Pure as[Clear Empty].
 unfold isr_inv;exists x;split.
 - clear Empty;sep auto.
 - exists k;split;[sep auto| ].
   apply apure_intro;[ |intros;apply Clear].
   apply astar_l_aisr_elim in Raw;destruct Raw as[_ Raw].
   apply atopis_elim in Raw;exact(proj2 Raw).
Qed.

(* Closure to the actual interrupt-return builder retains all shared resources. *)
Theorem V293_irq_ready_return_resources : forall i ir si t lg,
 (forall j,ir j=false) ->
 V293_irq_ready_closed i si(spec_done None)t lg ==>
 iretasrt' i ir si Inv0 ** p_local V293_shared_li t lg.
Proof.
 intros i ir si t lg Clear st Held.
 assert(IR:isrupd ir i false=(fun _:hid=>false)).
 { apply functional_extensionality;intro j;unfold isrupd;destruct(Nat.eqb i j);auto. }
 unfold V293_irq_ready_closed,SWINV in Held;sep normal in Held;sep destruct Held.
 destruct st as [[[[[[ge le] M] irq] [[ie stack] cs]] O] op].
 assert(Raw:(ge,le,M,irq,(ie,stack,cs),O,op) |= isrclr ** Atrue)by(sep auto).
 pose proof(V293_shared_clear_state _ _ _ _ _ _ _ Raw)as ClearIRQ.
 assert(IRQ:irq=(fun _:hid=>false))by(apply functional_extensionality;exact ClearIRQ).
 clear Raw.
 assert(Raw:(ge,le,M,irq,(ie,stack,cs),O,op) |= ATopis x ** (Ais(i::si) ** Atrue))by(sep auto).
 apply astar_l_atopis_elim in Raw;destruct Raw as[Top Raw].
 apply astar_l_ais_elim in Raw;destruct Raw as[Stack Raw].
 simpl in Top,Stack;rewrite Stack in Top;simpl in Top;subst x;clear Raw.
 assert(Convert:isrclr ** Aie false ** ATopis i ==> isr_inv //\\ Aie false).
 { intros s H;split.
   - apply V293_irq_clear_isr_inv with(k:=i);sep auto.
   - unfold isrclr in H;sep normal in H;sep destruct H.
     apply astar_l_aconj_elim in H;destruct H as[H _];sep auto. }
 assert(Pack:(ge,le,M,irq,(ie,stack,cs),O,op) |=
 (isrclr ** Aie false ** ATopis i) **
 (invlth_isr Inv0 0 i ** <||spec_done None||> ** Ais(i::si) ** Acs nil **
 (A_dom_lenv nil ** p_local V293_shared_li t lg)))by(sep auto).
 eapply astar_mono in Pack;[ |exact Convert|intros s H;exact H].
 assert(End:Ais(i::si) ** invlth_isr Inv0 0 i ==>
 EX ii,EX k,[|hd_error ii=Some k|] ** Ais ii ** invlth_isr Inv0 0 k).
 { intros s H;exists (i::si);exists i;sep auto. }
 assert(Pack2:(ge,le,M,irq,(ie,stack,cs),O,op) |=
 ((isr_inv //\\ Aie false) ** (Ais(i::si) ** invlth_isr Inv0 0 i)) **
 (<||spec_done None||> ** Ais(i::si) ** Acs nil **
 (A_dom_lenv nil ** p_local V293_shared_li t lg)))by(clear Held;sep auto).
 eapply astar_mono in Pack2;[ |intros s H;eapply astar_mono in H;[exact H|intros ss HH;exact HH|exact End]|intros s H;exact H].
 assert(Close: (isr_inv //\\ Aie false) **
 (EX ii,EX k,[|hd_error ii=Some k|] ** Ais ii ** invlth_isr Inv0 0 k) ==> IRINV Inv0).
 { intros s H;right;exact H. }
 eapply astar_mono in Pack2;[ |exact Close|intros s H;exact H].
 unfold iretasrt';rewrite IR;clear Held Pack;sep auto.
Qed.
Theorem V293_irq_ready_exint : forall Spec sd intspec i ir si t lg ret,
 Some ret=BuildintRet i intspec ir si Inv0 V293_shared_li t lg ->
 (forall j,ir j=false) ->
 InfRules Spec sd V293_shared_li Inv0 arfalse ret
 (V293_irq_ready_closed i si(spec_done None)t lg)(sprim exint)Afalse t.
Proof.
 intros Spec sd intspec i ir si t lg ret Ret Clear.
 unfold BuildintRet in Ret;destruct(intspec i);[ |discriminate].
 inversion Ret;subst ret;apply iret_rule;apply V293_irq_ready_return_resources;exact Clear.
Qed.
End ReadyIRQBoundary.
