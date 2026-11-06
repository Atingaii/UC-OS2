(* A resource-to-execution bridge at the already-entered interrupt cutpoint.
   It does not establish initialization, interleaving simulation or return. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptEnterCallPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_builder_byte_writable : forall b v R st,
 st |= Amapsto(b,0%Z)Tint8 true v ** R ->
 exists byte,get(getmem st)(b,0%Z)=Some(true,byte).
Proof.
 intros b v R [[[[[[ge le]M]ir]aux]O]op]Owned.
 pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ Owned)as W.
 destruct(W 0 ltac:(cbn;lia))as[byte Byte].
 exists byte;exact Byte.
Qed.

Lemma V293_builder_bytes_separate : forall b b' v v' R st,
 st |= Amapsto(b,0%Z)Tint8 true v ** (Amapsto(b',0%Z)Tint8 true v' ** R) ->b<>b'.
Proof.
 intros b b' v v' R [[[[[[ge le]M]ir]aux]O]op]Held Same;subst b'.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&H1&H2).
 assert(First:(ge,le,m1,ir,aux,o1,op)|=Amapsto(b,0%Z)Tint8 true v ** Aemp)by(sep auto).
 destruct(V293_builder_byte_writable _ _ _ _ First)as[u U].
 destruct(V293_builder_byte_writable _ _ _ _ H2)as[w W].
 cbn[getmem get_smem get_mem]in U,W.
 pose proof(@HalfPermMap.map_join_getp_some m1 m2 M(b,0%Z)(true,u)(true,w)(false,u)
 eq_refl JM U W eq_refl)as[_[Impossible _]];discriminate.
Qed.

Section BuilderExecution.
Variables target running nesting lock:var.
Variables bt bg br bh bp bc bk brun bn bl:block.
Variable rest:list(addr*type).
Let li:=V293_irq_bound_li running nesting lock brun bn bl.
Let Inv0:=V293_ready_dynamic_exit_inv target bt bg br bh bp bc bk brun bn bl rest.
Let snapshot:=V293_irq_bound_snapshot target running nesting lock
 bt bg br bh bp bc bk brun bn bl rest.

Lemma V293_builder_snapshot_memory : forall run nest locked aop enabled ir si ci t st,
 run<256 ->nest<256 ->locked<256 ->
 st|=snapshot run nest locked aop enabled ir si ci t ->
 get(getgenv st)running=Some(brun,Tint8) /\
 get(getgenv st)nesting=Some(bn,Tint8) /\
 get(getgenv st)lock=Some(bl,Tint8) /\
 load Tint8(getmem st)(brun,0%Z)=Some(V293_byteval run) /\
 load Tint8(getmem st)(bn,0%Z)=Some(V293_byteval nest) /\
 load Tint8(getmem st)(bl,0%Z)=Some(V293_byteval locked) /\
 (exists byte,get(getmem st)(bn,0%Z)=Some(true,byte)) /\brun<>bn /\bl<>bn.
Proof.
 intros run nest locked aop enabled ir si ci t st R N L Held.
 assert(Controls:st|=V293_irq_controls brun bn bl run nest locked).
 { eapply V293_irq_bound_snapshot_controls;exact Held. }
 destruct(V293_irq_controls_load _ _ _ _ _ _ _ R N L Controls)as[LR[LN LL]].
 assert(Globals:st|=V293_quiet_globals running nesting lock brun bn bl ** Atrue).
 { clear -Held;unfold snapshot,V293_irq_bound_snapshot,V293_enter_bound_external,
   p_local,LINV,V293_irq_bound_li in Held;sep auto. }
 assert(Bindings:get(getgenv st)running=Some(brun,Tint8) /\
 get(getgenv st)nesting=Some(bn,Tint8) /\get(getgenv st)lock=Some(bl,Tint8)).
 { eapply V293_star_env_l with(E:=fun ge le=>get ge running=Some(brun,Tint8) /\
   get ge nesting=Some(bn,Tint8) /\get ge lock=Some(bl,Tint8));[ |exact Globals].
   intros s[GR[GN GL]];apply agvarenv_elim in GR,GN,GL;tauto. }
 destruct Bindings as[GR[GN GL]].
 assert(Nest:st|=Amapsto(bn,0%Z)Tint8 true(V293_byteval nest) ** Atrue).
 { clear -Controls;unfold V293_irq_controls in Controls;sep auto. }
 assert(BR:brun<>bn).
 { eapply V293_builder_bytes_separate;unfold V293_irq_controls in Controls;exact Controls. }
 assert(BL:bl<>bn).
 { clear -Controls;eapply V293_builder_bytes_separate with(st:=st)(v:=V293_byteval locked)(v':=V293_byteval nest)(R:=Atrue).
   unfold V293_irq_controls in Controls;sep auto. }
 repeat split;try assumption;eapply V293_builder_byte_writable;exact Nest.
Qed.

(* This is the stable upper-layer interface. All memory and binding facts
   come from the same unfiltered builder. Its abstract state is not free. *)
Theorem V293_builder_enter_call : forall intspec i ir si t lg pre aop st P ks sd f,
 intspec i=Some aop ->
 Some pre=BuildintPre i intspec ir si Inv0 li t lg ->st|=pre ->
 P f=Some(V293_OSIntEnter_function running nesting) ->
 exists c Mf,
 V293_control_valid c /\
 V293_control_capture brun bn bl st=Some(getabst st,c) /\
 cstepstar P(curs(scall f nil),(kenil,ks))(getgenv st,getlenv st,getmem st)
 (curs(sskip None),(kenil,ks))(getgenv st,getlenv st,Mf) /\
 V293_control_read brun bn bl Mf=Some(V293_control_enter c) /\
 V293_control_step sd V293_control_Enter(getabst st,c)
 (V293_control_Core(spec_done None))(getabst st,V293_control_enter c) /\
 (forall a,a<>(bn,0%Z) ->get Mf a=get(getmem st)a).
Proof.
 intros intspec i ir si t lg pre aop st P ks sd f Lookup Pre Held Program.
 unfold BuildintPre in Pre;rewrite Lookup in Pre;inversion Pre;subst pre.
 apply V293_irq_bound_builder_open in Held.
 destruct Held as[run[nest[locked Held]]].
 apply astar_l_apure_elim in Held;destruct Held as[[R[N L]]Snapshot].
 assert(Valid:V293_control_valid(V293_control run nest locked))by(repeat split;assumption).
 assert(Capture:V293_control_capture brun bn bl st=Some(getabst st,V293_control run nest locked)).
 { eapply V293_control_capture_owned;try eassumption.
   eapply V293_irq_bound_snapshot_controls;exact Snapshot. }
 destruct(V293_builder_snapshot_memory _ _ _ _ _ _ _ _ _ _ R N L Snapshot)
 as[GR[GN[GL[LR[LN[LL[W[BR BL]]]]]]]].
 destruct(V293_control_enter_call_bridge P ks sd(getabst st)(getgenv st)(getlenv st)(getmem st)
 f running nesting brun bn bl(V293_control run nest locked)
 Program Valid BR BL GR GN LR LN LL W)as[Mf[Call[Read[Step Frame]]]].
 exists(V293_control run nest locked);exists Mf;repeat split;assumption.
Qed.
End BuilderExecution.
