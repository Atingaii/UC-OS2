(* The new guard stays on the retained heap, not on a duplicated byte cell. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEntryControl.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_current_guard_separate : forall bc t tasks P Q,
 (P ==> EX nc:nat,[|nc<256|] **
   (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Atrue)) ->
 (P ** Q) //\\ V293_current_guard bc t tasks ==>
 (P //\\ V293_current_guard bc t tasks) ** Q.
Proof.
 intros bc t tasks P Q Own st [Resources Guard].
 destruct st as[[[[[[ge le] M]ir]aux]O]op].
 apply sat_split in Resources;destruct Resources as(m1&m2&o1&o2&JM&JO&HP&HQ).
 pose proof(Own _ HP)as Byte;destruct Byte as[n Byte].
 apply astar_l_apure_elim in Byte;destruct Byte as[Bound Byte].
 assert(L:load Tint8 m1(bc,0%Z)=Some(V293_byteval n)).
 { change(load Tint8(getmem(ge,le,m1,ir,aux,o1,op))(bc,0%Z)=Some(V293_byteval n)).
   eapply V293_star_load_l;[ |exact Byte].
   intros s[Map _];eapply mapstoval_load;[apply V293_byte_type;exact Bound|exact Map]. }
 assert(Full:load Tint8 M(bc,0%Z)=Some(V293_byteval n)).
 { rewrite(rulesoundlib.load_mono _ _ _ _ _ _ JM L);exact L. }
 pose proof(V293_current_guard_same bc t tasks n
   (ge,le,M,ir,aux,O,op) Bound Full Guard)as Cases.
 assert(Local:(ge,le,m1,ir,aux,o1,op)|=V293_current_guard bc t tasks).
 { unfold V293_current_guard;destruct Cases as[C|Highest].
   - left;exists n;apply astar_l_apure_intro;[exact Byte|exact C].
   - right;apply astar_l_apure_intro;[exact I|exact Highest]. }
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 repeat first[assumption|split].
Qed.

Section CurrentEntry.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let prefix:=V293_ready_irq_prefix bt bh bc bk.
Let controls:=[((brun,0%Z),Tint8);((bn,0%Z),Tint8);((bl,0%Z),Tint8)].
Let cells:=prefix++controls++rest.
Definition V293_irq_current_inv:=V293_ready_current_inv br bg bp target V293_tcb_type cells bc.
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let external:=V293_enter_bound_external running nesting lock brun bn bl Aemp.
Let efp:=V293_enter_bound_fpre running nesting lock brun bn bl Aemp Logic.I.
Let efq:=V293_enter_bound_fpost running nesting lock brun bn bl Aemp Logic.I.
Definition V293_irq_current_payload ct tasks events now:=
 V293_shared_ready_records br bg bp ct tasks events now **
 (V293_dispatch_cell target V293_tcb_type ** (V293_storage prefix ** V293_storage rest)).
Definition V293_irq_current_kept:=EX ct:tid,EX tasks:TcbMod.map,
 EX events:EcbMod.map,EX now:int32,
 V293_irq_current_payload ct tasks events now //\\ V293_current_guard bc ct tasks.
Definition V293_irq_current_snapshot run nest locked aop enabled ir si ci t:=
 external run nest locked aop enabled ir si ci t ** (V293_irq_current_kept ** A_dom_lenv nil).

Lemma V293_irq_current_payload_byte : forall ct tasks events now,
 V293_irq_current_payload ct tasks events now ==>
 EX nc:nat,[|nc<256|] ** (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Atrue).
Proof.
 intros ct tasks events now st H.
 unfold V293_irq_current_payload,prefix,V293_ready_irq_prefix in H.
 cbn[V293_storage]in H.
 assert(B:st|=V293_storage_cell(bc,0%Z)Tint8 ** Atrue)by(sep auto).
 eapply astar_mono in B;[ |apply V293_storage_byte_open|intros s K;exact K].
 sep normal in B;sep destruct B;exists x;clear H;sep auto.
Qed.
Lemma V293_irq_current_kept_good : GoodFrm V293_irq_current_kept.
Proof.
 unfold V293_irq_current_kept;cbn[GoodFrm];intros ct tasks events now;split.
 - unfold V293_irq_current_payload;split.
   + unfold V293_shared_ready_records;split.
     * unfold V293_shared_fields,CurTid,Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
     * apply V293_ready_payload_frame.
   + split.
     * unfold V293_dispatch_cell,Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
     * split;apply V293_storage_frame_good.
 - unfold V293_current_guard;cbn[GoodFrm];auto.
Qed.
Lemma V293_irq_current_core_open :
 V293_ready_current_core br bg bp target V293_tcb_type cells bc ==>
 V293_storage controls ** V293_irq_current_kept.
Proof.
 intros st[ct[tasks[events[now[Resources Guard]]]]].
 assert(P:st|=V293_irq_current_payload ct tasks events now ** V293_storage controls).
 { change(st|=V293_shared_ready_records br bg bp ct tasks events now **
    (V293_dispatch_cell target V293_tcb_type ** V293_storage cells))in Resources.
   assert(B:st|=V293_storage cells **
    (V293_shared_ready_records br bg bp ct tasks events now ** V293_dispatch_cell target V293_tcb_type))by(clear Guard;sep auto).
   unfold cells in B;eapply astar_mono in B;[ |apply V293_storage_split|intros s K;exact K].
   assert(C:st|=V293_storage(controls++rest) **
    (V293_shared_ready_records br bg bp ct tasks events now ** V293_dispatch_cell target V293_tcb_type ** V293_storage prefix))by(clear Resources Guard;sep auto).
   eapply astar_mono in C;[ |apply V293_storage_split|intros s K;exact K].
   unfold V293_irq_current_payload;clear Resources B Guard;sep auto. }
 assert(G:st|=(V293_irq_current_payload ct tasks events now //\\ V293_current_guard bc ct tasks) ** V293_storage controls).
 { apply V293_current_guard_separate;[apply V293_irq_current_payload_byte|split;assumption]. }
 unfold V293_irq_current_kept;clear Resources P Guard;sep auto.
Qed.

Theorem V293_irq_current_builder_open : forall i ir si aop t lg,
 ipreasrt' i ir si aop V293_irq_current_inv ** p_local li t lg ==>
 EX run,EX nest,EX locked,[|run<256 /\ nest<256 /\ locked<256|] **
 V293_irq_current_snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t.
Proof.
 intros i ir si aop t lg st H.
 unfold ipreasrt',invlth_noisr in H;rewrite Nat.sub_0_r in H.
 assert(B:st|=starinv_noisr V293_irq_current_inv 0 i **
 (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
 (isr_inv ** (A_dom_lenv nil ** p_local li t lg))))by(sep auto).
 eapply astar_mono in B;[ |intros s K;apply V293_current_noisr_core in K;exact K|intros s K;exact K].
 eapply astar_mono in B;[ |apply V293_irq_current_core_open|intros s K;exact K].
 unfold isr_inv in B;sep normal in B;sep destruct B.
 rename x into oldir;rename x0 into oldtop.
 assert(C:st|=V293_storage controls **
 (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
 (V293_irq_current_kept ** (A_dom_lenv nil ** p_local li t lg)))).
 { clear H;sep auto.
   destruct B as[B _];apply aisr_elim in B;exact(proj2 B). }
 eapply astar_mono in C;[ |apply V293_irq_entry_controls_open|intros s K;exact K].
 sep normal in C;sep destruct C;exists x;exists x0;exists x1.
 assert(Local:p_local li t lg ==>p_local li t nil).
 { unfold li,p_local,LINV,V293_irq_bound_li;intros s K;exact K. }
 assert(D:st|=p_local li t lg **
 ([|x<256 /\ x0<256 /\ x1<256|] ** <||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
 (Amapsto(brun,0%Z)Tint8 true(V293_byteval x) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval x0) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval x1) ** (V293_irq_current_kept ** A_dom_lenv nil))))))by(clear H B;sep auto).
 eapply astar_mono in D;[ |exact Local|intros s K;exact K].
 unfold V293_irq_current_snapshot,external,V293_enter_bound_external;clear H B C;sep auto.
Qed.
Definition V293_irq_current_physical run nest locked t:=
 Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
 (p_local li t nil ** (V293_irq_current_kept ** A_dom_lenv nil)))).
Lemma V293_irq_current_physical_good : forall run nest locked t,
 GoodFrm(V293_irq_current_physical run nest locked t).
Proof.
 intros;unfold V293_irq_current_physical;split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
 - apply V293_exact_local_frame;apply V293_irq_bound_good.
 - split;[apply V293_irq_current_kept_good|exact Logic.I].
Qed.
Lemma V293_irq_current_prefix : forall Spec sd r ri enter i ir si aop t id run nest locked,
 run<256 ->nest<256 ->locked<256 ->Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd li V293_irq_current_inv r ri
 (V293_irq_current_snapshot run nest locked aop false(isrupd ir i true)(i::si)nil t)
 (sseq(sprim(eoi id))(scall enter nil))
 (V293_irq_current_snapshot run(V293_interrupt_nest_after run nest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t)t.
Proof.
 intros Spec sd r ri enter i ir si aop t id run nest locked Run Nest Lock Enter Bound Index.
 eapply seq_rule with(p':=V293_irq_current_snapshot run nest locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t).
 - eapply conseq_rule with
   (p:=<||aop||> ** OS[isrupd ir i true,false,i::si,nil] ** V293_irq_current_physical run nest locked t)
   (q:=<||aop||> ** OS[isrupd(isrupd ir i true)i false,false,i::si,nil] ** V293_irq_current_physical run nest locked t).
   + unfold V293_irq_current_snapshot,external,V293_enter_bound_external,V293_irq_current_physical;intros s H;sep auto.
   + unfold V293_irq_current_snapshot,external,V293_enter_bound_external,V293_irq_current_physical;intros s H;sep auto.
   + apply eoi_ieoff_rule;[exact Bound|exact Index|apply V293_irq_current_physical_good].
 - unfold V293_irq_current_snapshot,external;apply(V293_OSIntEnter_bound_call running nesting lock brun bn bl Aemp Logic.I);try assumption.
   split;[apply V293_irq_current_kept_good|exact Logic.I].
Qed.
Definition V293_irq_current_after i ir si aop t:=
 EX run,EX oldnest,EX locked,[|run<256 /\ oldnest<256 /\ locked<256|] **
 V293_irq_current_snapshot run(V293_interrupt_nest_after run oldnest)locked aop false
 (isrupd(isrupd ir i true)i false)(i::si)nil t.
Theorem V293_interrupt_current_entry : forall Spec sd r ri enter intspec i ir si aop t lg pre id,
 intspec i=Some aop ->Some pre=BuildintPre i intspec ir si V293_irq_current_inv li t lg ->
 Spec enter=Some(efp,efq,(Tvoid,nil)) ->
 (0<=Int.unsigned id<Z.of_nat INUM)%Z ->i=Z.to_nat(Int.unsigned id) ->
 InfRules Spec sd li V293_irq_current_inv r ri pre
 (sseq(sprim(eoi id))(scall enter nil))(V293_irq_current_after i ir si aop t)t.
Proof.
 intros Spec sd r ri enter intspec i ir si aop t lg pre id Lookup Pre Enter Bound Index.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 eapply conseq_rule;[apply V293_irq_current_builder_open|intros s H;exact H| ].
 apply ex_intro_rule;intro run;apply ex_intro_rule;intro nest;apply ex_intro_rule;intro locked.
 eapply conseq_rule;[intros s H;apply astar_comm;exact H|intros s H;exact H| ].
 apply pure_split_rule;intros[Run[Nest Lock]].
 eapply conseq_rule;[intros s H;exact H| |eapply V293_irq_current_prefix;try eassumption].
 intros s H;unfold V293_irq_current_after;exists run;exists nest;exists locked;sep auto.
Qed.
(* Construction helper only; the stable entry theorem above has no guard premise. *)
Lemma V293_irq_current_core_enrich : forall R ct tasks st,
 st|=V293_ready_storage_core br bg bp target V293_tcb_type cells ** R ->
 get(getabst st)curtid=Some(oscurt ct) ->
 get(getabst st)abstcblsid=Some(abstcblist tasks) ->
 st|=V293_current_guard bc ct tasks ->
 st|=V293_ready_current_core br bg bp target V293_tcb_type cells bc ** R.
Proof.
 intros R ct tasks st H Current Tasks Guard.
 unfold V293_ready_storage_core,V293ReadyTaskInvariant.V293_ready_core in H.
 sep normal in H;sep destruct H.
 assert(C:get(getabst st)curtid=Some(oscurt x)).
 { eapply V293_star_abst_get_l;[apply V293_shared_abs_get| ].
   unfold V293_shared_ready_records,V293_shared_fields in H;clear Guard;sep auto. }
 assert(T:get(getabst st)abstcblsid=Some(abstcblist x0)).
 { eapply V293_star_abst_get_l;[apply V293_shared_abs_get| ].
   unfold V293_shared_ready_records,V293_shared_fields in H;clear Guard;sep auto. }
 assert(x=ct)by congruence;assert(x0=tasks)by congruence;subst x x0.
 assert(Own:(V293_shared_ready_records br bg bp ct tasks x1 x2 **
   V293_ready_storage_extra target V293_tcb_type cells) ==>
   EX nc:nat,[|nc<256|] ** (Amapsto(bc,0%Z)Tint8 true(V293_byteval nc) ** Atrue)).
 { intros ss K;unfold V293_ready_storage_extra,cells in K.
   assert(B:ss|=V293_storage(prefix++controls++rest) **
    (V293_shared_ready_records br bg bp ct tasks x1 x2 ** V293_dispatch_cell target V293_tcb_type))by(sep auto).
   eapply astar_mono in B;[ |apply V293_storage_split|intros s HH;exact HH].
   unfold prefix,V293_ready_irq_prefix in B;cbn[V293_storage]in B.
   assert(Byte:ss|=V293_storage_cell(bc,0%Z)Tint8 ** Atrue)by(clear K;sep auto).
   eapply astar_mono in Byte;[ |apply V293_storage_byte_open|intros s HH;exact HH].
   sep normal in Byte;sep destruct Byte;exists x;clear K B;sep auto. }
 assert(P:st|=(V293_shared_ready_records br bg bp ct tasks x1 x2 **
  V293_ready_storage_extra target V293_tcb_type cells) ** R)by(clear Guard;sep auto).
 assert(G:st|=((V293_shared_ready_records br bg bp ct tasks x1 x2 **
  V293_ready_storage_extra target V293_tcb_type cells) //\\ V293_current_guard bc ct tasks) ** R).
 { apply V293_current_guard_separate;[exact Own|split;assumption]. }
 eapply astar_mono;[ |intros ss HH;exact HH|exact G].
 intros ss HH;exists ct;exists tasks;exists x1;exists x2;exact HH.
Qed.
Theorem V293_irq_current_builder_enrich : forall i ir si aop t lg ct tasks st,
 st|=ipreasrt' i ir si aop
 (V293_ready_storage_inv br bg bp target V293_tcb_type cells) ** p_local li t lg ->
 get(getabst st)curtid=Some(oscurt ct) ->
 get(getabst st)abstcblsid=Some(abstcblist tasks) ->
 st|=V293_current_guard bc ct tasks ->
 st|=ipreasrt' i ir si aop V293_irq_current_inv ** p_local li t lg.
Proof.
 intros i ir si aop t lg ct tasks st H Current Tasks Guard.
 unfold ipreasrt',invlth_noisr in *;rewrite Nat.sub_0_r in *.
 assert(P:st|=starinv_noisr(V293_ready_storage_inv br bg bp target V293_tcb_type cells)0 i **
  (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
  (isr_inv ** (A_dom_lenv nil ** p_local li t lg))))by(clear Guard;sep auto).
 eapply astar_mono in P;[ |intros s K;apply V293_ready_storage_noisr_core in K;exact K|intros s K;exact K].
 pose proof(V293_irq_current_core_enrich _ ct tasks st P Current Tasks Guard)as New.
 eapply astar_mono in New;[ |intros s K;apply V293_current_noisr_core;exact K|intros s K;exact K].
 clear H P Guard;sep auto.
Qed.
Lemma V293_irq_current_builder_guard : forall i ir si aop t lg ge le M irq aux O op,
 (ge,le,M,irq,aux,O,op)|=ipreasrt' i ir si aop V293_irq_current_inv ** p_local li t lg ->
 exists ct tasks,get O curtid=Some(oscurt ct) /\
 get O abstcblsid=Some(abstcblist tasks) /\
 (ge,le,M,irq,aux,O,op)|=V293_current_guard bc ct tasks.
Proof.
 intros i ir si aop t lg ge le M irq aux O op H.
 unfold ipreasrt',invlth_noisr in H;rewrite Nat.sub_0_r in H.
 assert(P:(ge,le,M,irq,aux,O,op)|=starinv_noisr V293_irq_current_inv 0 i **
  (<||aop||> ** OS[isrupd ir i true,false,i::si,nil] **
  (isr_inv ** (A_dom_lenv nil ** p_local li t lg))))by(sep auto).
 eapply astar_mono in P;[ |intros s K;apply V293_current_noisr_core in K;exact K|intros s K;exact K].
 eapply V293_current_core_guard_frame;exact P.
Qed.
Theorem V293_irq_current_good : GoodI V293_irq_current_inv V293_scheduler li.
Proof. apply V293_irq_bound_GoodI;apply V293_ready_current_good. Qed.
Theorem V293_irq_current_enter_environment : forall enter,
 WFFunEnv(V293_OSIntEnter_unit enter running nesting)
 (V293_enter_bound_spec running nesting lock brun bn bl Aemp Logic.I enter)
 V293_scheduler li V293_irq_current_inv /\
 WFIFun(V293_OSIntEnter_unit enter running nesting)
 (V293_enter_bound_spec running nesting lock brun bn bl Aemp Logic.I enter)
 V293_scheduler V293_irq_current_inv li.
Proof. intro enter;split;[apply V293_OSIntEnter_bound_WFFunEnv|apply V293_OSIntEnter_bound_WFIFun]. Qed.
End CurrentEntry.

