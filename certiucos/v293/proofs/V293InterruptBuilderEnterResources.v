(* Same input builder, actual EOI and Enter call, same successor resources.
   The handler-entry cutpoint is not an initialized interrupt predecessor. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterCall.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEnterCallPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Section BuilderResources.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.
Let physical:=V293_irq_bound_physical target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.

Lemma V293_builder_snapshot_context : forall run nest locked aop enabled ir si ci t st,
 st|=snapshot run nest locked aop enabled ir si ci t ->
 getlenv st=emp /\ getisr(gettaskst st)=ir /\
 getie(gettaskst st)=enabled /\ getis(gettaskst st)=si /\
 getcs(gettaskst st)=ci /\ getabsop st=aop.
Proof.
 intros run nest locked aop enabled ir si ci t st Held.
 assert(Context:st|=A_dom_lenv nil ** (<||aop||> ** (Aisr ir **
   (Aie enabled ** (Ais si ** (Acs ci ** Atrue)))))).
 { clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in Held;sep auto. }
 apply astar_l_adomlenv_elim in Context;destruct Context as[Dom Context].
 apply astar_l_aop'_elim in Context;destruct Context as[Op Context].
 apply astar_l_aisr_elim in Context;destruct Context as[IR Context].
 apply astar_l_aie_elim in Context;destruct Context as[IE Context].
 apply astar_l_ais_elim in Context;destruct Context as[IS Context].
 apply astar_l_acs_elim in Context;destruct Context as[CS Context].
 split;[ |tauto].
 apply EnvMod.extensionality;intro x.
 change(get(getlenv st)x=get(emp:env)x).
 transitivity(@None(block*type));[exact(V293_interrupt_empty_local(getlenv st)x Dom)|symmetry;apply map_emp_get].
Qed.

(* EOI changes only the ISR observation; the ready/TCB/storage payload is
   transported by its proved GoodFrm, not re-assumed on another heap. *)
Lemma V293_builder_snapshot_isr : forall run nest locked aop enabled ir ir' si ci t ge le M O,
 (ge,le,M,ir,(enabled,si,ci),O,aop)|=snapshot run nest locked aop enabled ir si ci t ->
 (ge,le,M,ir',(enabled,si,ci),O,aop)|=snapshot run nest locked aop enabled ir' si ci t.
Proof.
 intros run nest locked aop enabled ir ir' si ci t ge le M O Held.
 assert(Payload:(ge,le,M,ir,(enabled,si,ci),O,aop)|=
 <||aop||> ** (Aisr ir ** (Aie enabled ** (Ais si ** (Acs ci ** physical run nest locked t))))).
 { clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
   physical,V293_irq_bound_physical in *;sep auto. }
 apply astar_l_aop'_elim in Payload;destruct Payload as[_ Payload].
 apply astar_l_aisr_elim in Payload;destruct Payload as[_ Payload].
 apply astar_l_aie_elim in Payload;destruct Payload as[_ Payload].
 apply astar_l_ais_elim in Payload;destruct Payload as[_ Payload].
 apply astar_l_acs_elim in Payload;destruct Payload as[_ Payload].
 assert(Changed:(ge,le,M,ir',(enabled,si,ci),O,aop)|=physical run nest locked t).
 { eapply goodfrm_prop;[apply V293_irq_bound_physical_good|exact Payload]. }
 assert(Pack:(ge,le,M,ir',(enabled,si,ci),O,aop)|=
 <||aop||> ** (Aisr ir' ** (Aie enabled ** (Ais si ** (Acs ci ** physical run nest locked t))))).
 { apply astar_l_aop'_intro;[ |reflexivity].
   apply astar_l_aisr_intro;[ |reflexivity].
   apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity].
   apply astar_l_acs_intro;[exact Changed|reflexivity]. }
 clear Held Payload Changed;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
 physical,V293_irq_bound_physical in *;sep auto.
Qed.

(* The resource update and the execution use definitionally the same memory.
   Non-running and saturated cases keep the original heap without a write. *)
Lemma V293_builder_snapshot_enter_memory : forall run nest locked aop enabled ir si ci t ge le M O,
 nest<256 ->
 (ge,le,M,ir,(enabled,si,ci),O,aop)|=snapshot run nest locked aop enabled ir si ci t ->
 (ge,le,V293_control_enter_memory bn(V293_control run nest locked)M,ir,(enabled,si,ci),O,aop)|=
 snapshot run(V293_interrupt_nest_after run nest)locked aop enabled ir si ci t.
Proof.
 intros run nest locked aop enabled ir si ci t ge le M O Bound Held.
 unfold V293_control_enter_memory,V293_interrupt_nest_after;cbn[V293_control_running V293_control_nesting].
 destruct(Nat.eqb run 1 && Nat.ltb nest 255)eqn:Write;[ |exact Held].
 apply Bool.andb_true_iff in Write;destruct Write as[Running Room];apply Nat.ltb_lt in Room.
 set(Frame:=<||aop||> ** OS[ir,enabled,si,ci] **
   (Amapsto(brun,0%Z)Tint8 true(V293_byteval run) **
   (Amapsto(bl,0%Z)Tint8 true(V293_byteval locked) **
   (p_local li t nil ** Aemp **
    (V293_quiet_irq_kept target bt bg br bh bp bc bk rest ** A_dom_lenv nil))))).
 assert(Owned:(ge,le,M,ir,(enabled,si,ci),O,aop)|=
 Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) ** Frame).
 { unfold Frame,li;clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external in Held;sep auto. }
 destruct(V293_builder_byte_writable _ _ _ _ Owned)as[v Writable].
 destruct(V293_tick_raw_slot_update(bn,0%Z)Tint8(V293_byteval nest)(V293_byteval(S nest))
 Frame ge le M ir(enabled,si,ci)O aop(V293_byte_type(S nest)ltac:(lia))Owned)
 as[Mf[Store Updated]].
 assert(Same:Mf=V293_put_byte M(bn,0%Z)(S nest)).
 { pose proof(V293_put_byte_store M(bn,0%Z)(S nest)v Writable);congruence. }
 subst Mf;clear Held Owned.
 unfold V293_owned_record_cell in Updated;apply astar_mono with
 (P':=Amapsto(bn,0%Z)Tint8 true(V293_byteval(S nest)))(Q':=Frame)in Updated.
 2:{ intros s K;apply astar_l_apure_elim in K;tauto. }
 2:{ intros s K;exact K. }
 unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,Frame,li in *;sep auto.
Qed.

(* Stable interface: the actual input task state, not just its memory
   projection, executes the prefix. The exact double ISR update needs no
   hidden assumption that the original entered bit was false. *)
Theorem V293_builder_enter_prefix : forall intspec i ir si t lg pre aop st P sd entry exit vector,
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 P entry=Some(V293_OSIntEnter_function running nesting) ->
 i=Z.to_nat(Int.unsigned vector) ->(0<=Int.unsigned vector<Z.of_nat INUM)%Z ->
 exists c Mf,
 V293_control_valid c /\
 V293_control_capture brun bn bl st=Some(getabst st,c) /\
 V293_local_steps P(curs(V293_irq_source_wrapper entry exit vector),(kenil,kstop))(gettaskst st)
 (curs(scall exit nil),(kenil,kseq(sprim exint)kstop))
 ((getgenv st,emp,Mf),isrupd(isrupd ir i true)i false,(false,i::si,nil)) /\
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)|=
 snapshot(V293_control_running c)(V293_control_nesting(V293_control_enter c))
 (V293_control_lock c)aop false(isrupd(isrupd ir i true)i false)(i::si)nil t /\
 V293_control_capture brun bn bl
 (getgenv st,emp,Mf,isrupd(isrupd ir i true)i false,(false,i::si,nil),getabst st,aop)=
 Some(getabst st,V293_control_enter c) /\
 V293_control_step sd V293_control_Enter(getabst st,c)
 (V293_control_Core(spec_done None))(getabst st,V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get(getmem st)a).
Proof.
 intros intspec i ir si t lg pre aop st P sd entry exit vector Lookup Pre Held Program Vector Range.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 apply V293_irq_bound_builder_open in Held.
 destruct Held as[run[nest[locked Held]]].
 apply astar_l_apure_elim in Held;destruct Held as[[R[N L]]Snapshot].
 destruct(V293_builder_snapshot_context _ _ _ _ _ _ _ _ _ _ Snapshot)as[LE[IR[IE[IS[CS OP]]]]].
 destruct st as[[[[[[ge le]M]ir0][[enabled stack]crit]]O]op].
 cbn in LE,IR,IE,IS,CS,OP.
 subst le ir0 enabled stack crit op.
 assert(Valid:V293_control_valid(V293_control run nest locked))by(repeat split;assumption).
 assert(Captured:V293_control_capture brun bn bl(ge,emp,M,isrupd ir i true,(false,i::si,nil),O,aop)=
 Some(O,V293_control run nest locked)).
 { eapply V293_control_capture_owned;try eassumption.
   eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 destruct(V293_builder_snapshot_memory target running nesting lock bt bg br bh bp bc bk brun bn bl rest
 _ _ _ _ _ _ _ _ _ _ R N L Snapshot)as[GR[GN[GL[LR[LN[LL[W[BR BL]]]]]]]].
 assert(Changed:(ge,emp,M,isrupd(isrupd ir i true)i false,(false,i::si,nil),O,aop)|=
 snapshot run nest locked aop false(isrupd(isrupd ir i true)i false)(i::si)nil t).
 { eapply V293_builder_snapshot_isr;exact Snapshot. }
 pose proof(V293_builder_snapshot_enter_memory _ _ _ _ _ _ _ _ _ _ _ _ _ N Changed)as After.
 destruct(V293_control_enter_observation brun bn bl(V293_control run nest locked)M Valid BR BL LR LN LL)
 as[Read Frame].
 exists(V293_control run nest locked);exists(V293_control_enter_memory bn(V293_control run nest locked)M).
 split;[exact Valid| ];split;[exact Captured| ];split.
 - unfold V293_irq_source_wrapper.
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_cons.
   { eapply eoi_step;[reflexivity|exact Vector|exact Range]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_control_enter_full_call;eassumption. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
   eapply V293_local_cons.
   { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
   apply V293_local_refl.
 - split;[exact After| ];split.
   + unfold V293_control_capture;cbn[getmem get_smem get_mem getabst];rewrite Read;reflexivity.
   + split;[constructor;exact Valid|exact Frame].
Qed.
End BuilderResources.
