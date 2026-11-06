(* Nonempty, independently constructed source-entry witnesses. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.framework.proof.join_prop.
Require Import Coq.Logic.FunctionalExtensionality Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Import ListNotations.
Local Open Scope nat_scope.

(* Unlike GoodInvAsrt, this explicit property permits changes to the ISR
   stack. Only the structurally checked byte/cell fixtures below use it. *)
Definition SX_context(A:asrt) := forall ge le M ir au O op ir' au',
 (ge,le,M,ir,au,O,op)|=A ->(ge,le,M,ir',au',O,op)|=A.
Lemma SX_star_context : forall A B,SX_context A ->SX_context B ->SX_context(A**B).
Proof.
 intros A B HA HB ge le M ir au O op ir' au' Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&H1&H2).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[eapply HA|eapply HB];eassumption.
Qed.
Lemma SX_cell_context : forall c,SX_context(V293_owned_record_cell c).
Proof. intros [[a tp]v] ge le M ir au O op ir' au' Held;exact Held. Qed.
Lemma SX_read_context : forall b off vs,SX_context(V293_read_bytes b off vs).
Proof.
 intros b off vs;revert off;induction vs;intro off;cbn.
 - intros ge le M ir au O op ir' au' Held;exact Held.
 - apply SX_star_context;[intros ge le M ir au O op ir' au' Held;exact Held|apply IHvs].
Qed.
Lemma SX_frame_context : SX_context FXframe.
Proof.
 unfold FXframe,RCframe.
 repeat match goal with
 | |-SX_context(V293_owned_record_cell _)=>apply SX_cell_context
 | |-SX_context(V293_read_bytes _ _ _)=>apply SX_read_context
 | |-SX_context(_**_)=>apply SX_star_context
 end.
Qed.
Lemma SX_ready_stack : forall br bg bp ct R ge le M ir si si' O op,
 SX_context R ->
 (ge,le,M,ir,(false,si,nil),O,op)|=SWINVt(V293_ready_inv br bg bp)ct**R ->
 (ge,le,M,ir,(false,si',nil),O,op)|=SWINVt(V293_ready_inv br bg bp)ct**R.
Proof.
 intros br bg bp ct R ge le M ir si si' O op Context Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Inv&Rest).
 unfold SWINVt in Inv;apply sat_split in Inv.
 destruct Inv as(mf&mt&oflags&ot&JMI&JOI&Switch&Current).
 apply V293_ready_switch_open in Switch;apply sat_split in Switch.
 destruct Switch as(mflags&mc&ofl&oc&JMF&JOF&Flags&Core).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split.
 - unfold SWINVt;apply sat_split';exists mf;exists mt;exists oflags;exists ot.
   split;[exact JMI| ];split;[exact JOI| ];split;[ |exact Current].
   apply V293_ready_switch_close;apply sat_split'.
   exists mflags;exists mc;exists ofl;exists oc.
   split;[exact JMF| ];split;[exact JOF| ];split.
   + unfold V293_shared_flags in *;apply sat_split in Flags.
     destruct Flags as(ml&mr&ol&orr&JML&JOL&Left&k&Top&Empty).
     apply sat_split';exists ml;exists mr;exists ol;exists orr.
     split;[exact JML| ];split;[exact JOL| ];split;[exact Left| ].
     exists(gettopis si');split;[reflexivity|exact Empty].
   + eapply V293_ready_core_aux;exact Core.
 - eapply Context;exact Rest.
Qed.

Definition SXprogram(fid:fid) := if Z.eq_dec fid 301%Z
 then Some(V293_OSIntEnter_function 113%Z 108%Z)else FXprogram fid.
Definition SXwrapper := V293_irq_source_wrapper 301%Z 300%Z(Int.repr 1).
Definition SXip : intunit := fun irq=>if Nat.eq_dec irq 1 then Some SXwrapper else None.
Definition SXpc : progunit := fun _=>None.
Definition SXpi : progunit := fun _=>None.
Definition SXp : lprog := (SXpc,(SXprogram,SXpi,SXip)).
Definition SXcode : code := (cure(econst32(Int.repr 7)),(keop1 negation Tint32 kenil,kstop)).
Definition SXT : tasks := set emp FXct SXcode.
Definition SXles : cltenvs := set emp FXct FXcaller.
Definition SXaus(enabled:bool):ltaskstset := set emp FXct((enabled,nil,nil):localst).
Definition SXpre := SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)FXct **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((95%positive,0%Z),Tint8,V293_byteval 0) **FXentry_frame 4)))).
Lemma SXindependent_entry :
 (FXge,emp,FXmemory 0 4,(fun _=>false),(false,[1],nil),RIabstract FXct,spec_done None)|=SXpre.
Proof.
 unfold SXpre;eapply V293_ready_lenv_frame with(le:=FXcaller).
 - unfold FXentry_frame,FXframe;repeat split;try exact I;exact RCframe_good.
 - eapply SX_ready_stack with(si:=nil).
   + unfold FXentry_frame.
     repeat match goal with
     | |-SX_context(V293_owned_record_cell _)=>apply SX_cell_context
     | |-SX_context FXframe=>apply SX_frame_context
     | |-SX_context(_**_)=>apply SX_star_context
     end.
   + exact(FXentry 0 4 ltac:(lia)ltac:(lia)).
Qed.
Lemma SXmerge : SXprogram=pumerge SXprogram SXpi.
Proof. apply functional_extensionality;intro f;unfold pumerge,SXpi;destruct(SXprogram f);reflexivity. Qed.
Theorem SXcomplete_roundtrip : forall cst,exists bs Mf,
 V293_global_steps SXp cst(SXT,(FXge,SXles,FXmemory 0 4,(fun _=>false),SXaus true),FXct)
 (SXT,(FXge,SXles,Mf,(fun _=>false),SXaus true),FXct) /\
 fresh(V293_put_byte(FXmemory 0 4)(94%positive,0%Z)1)bs /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 0) /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 (forall b j,b<>bs ->b<>93%positive ->(b,j)<>(91%positive,0%Z) ->(b,j)<>(94%positive,0%Z) ->
 get Mf(b,j)=get(FXmemory 0 4)(b,j)).
Proof.
 intro cst.
 exact(V293_interrupt_source_roundtrip 80%positive 81%positive 82%positive SXprogram
 SXpc SXprogram SXpi SXip SXT SXles(SXaus true)cst
 (cure(econst32(Int.repr 7)))(keop1 negation Tint32 kenil)FXcaller kstop
 FXge(FXmemory 0 4)(fun _=>false)1 nil(RIabstract FXct)(spec_done None)
 FXct FXframe OwnershipTasks 4 301%Z(Int.repr 1)
 300%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 108%Z 109%Z 113%Z 601%Z 110%Z 111%Z 112%Z
 92%positive 91%positive 93%positive 94%positive 95%positive 98%positive 96%positive
 (V293_byteval 88)(Vptr OwnershipWaiting)
 SXmerge ltac:(apply map_get_set)ltac:(apply map_get_set)ltac:(apply map_get_set)
 ltac:(exact I)ltac:(unfold higherint;intros;reflexivity)ltac:(unfold INUM;lia)eq_refl
 ltac:(change(0<=1<2)%Z;lia)eq_refl
 eq_refl eq_refl eq_refl ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks FXct)FXcurrent FXhighest
 ltac:(unfold FXframe;repeat split;try exact I;exact RCframe_good)
 (FXlookup 0 4)SXindependent_entry).
Qed.

Definition SXentered :=(curs SXwrapper,(kenil,
 kint(cure(econst32(Int.repr 7)))(keop1 negation Tint32 kenil)FXcaller kstop)).
Theorem SXenabled_actual_entry : forall cst,
 lpstep SXp SXT cst(FXge,SXles,FXmemory 0 4,(fun _=>false),SXaus true)FXct
 (set SXT FXct SXentered)cst
 (FXge,set SXles FXct emp,FXmemory 0 4,isrupd(fun _=>false)1 true,
 set(SXaus true)FXct(false,[1],nil))FXct.
Proof.
 intro cst;eapply V293_interrupt_source_enter.
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - unfold higherint;intros;reflexivity.
 - unfold INUM;lia.
 - reflexivity.
Qed.
Theorem SXdisabled_no_interrupt : forall Cf stf,
 ~lintstep SXip SXcode((FXge,FXcaller,FXmemory 0 4),(fun _=>false),(false,nil,nil))Cf stf.
Proof. intros Cf stf Step;inversion Step. Qed.
Theorem SXonly_IE_changed :
 get(SXaus false)FXct=Some((false,nil,nil):localst) /\
 get(SXaus true)FXct=Some((true,nil,nil):localst) /\
 (forall t,t<>FXct ->get(SXaus false)t=get(SXaus true)t) /\
 get SXT FXct=Some SXcode /\get SXles FXct=Some FXcaller /\
 SXip 1=Some SXwrapper.
Proof.
 split;[apply map_get_set| ];split;[apply map_get_set| ];split.
 - intros;unfold SXaus;rewrite !map_get_set' by congruence;reflexivity.
 - split;[apply map_get_set| ];split;[apply map_get_set|reflexivity].
Qed.

Lemma SXcell_live : forall b tp v R,
 b<>94%positive ->0<typelen tp ->
 (FXge,FXcaller,FXmemory 0 4,(fun _=>false),(false,nil,nil),RIabstract FXct,spec_done None)|=
 V293_owned_record_cell((b,0%Z),tp,v)**R ->
 indom(V293_put_byte(FXmemory 0 4)(94%positive,0%Z)1)(b,0%Z).
Proof.
 intros b tp v R N Len Held.
 assert(Raw:(FXge,FXcaller,FXmemory 0 4,(fun _=>false),(false,nil,nil),RIabstract FXct,spec_done None)|=
 Amapsto(b,0%Z)tp true v **R).
 { unfold V293_owned_record_cell in Held;sep auto. }
 pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ Raw)as Writable.
 destruct(Writable 0 ltac:(lia))as[d Cell];cbn in Cell.
 exists(true,d);rewrite V293_put_byte_other by congruence;exact Cell.
Qed.
Lemma SXcanary_live : forall b,In b[90%positive;97%positive;99%positive;100%positive] ->
 indom(V293_put_byte(FXmemory 0 4)(94%positive,0%Z)1)(b,0%Z).
Proof.
 intros b Member;pose proof(FXentry 0 4 ltac:(lia)ltac:(lia))as Held.
 unfold FXentry_frame,FXframe,RCframe in Held.
 cbn in Member;destruct Member as[Eq|[Eq|[Eq|[Eq|Impossible]]]];
 try contradiction;subst b.
 - eapply SXcell_live with(tp:=Tint8)(v:=V293_byteval 99)(R:=Atrue);[discriminate|cbn;lia|sep auto].
 - eapply SXcell_live with(tp:=Tint32)(v:=Vint32(Int.repr 19))(R:=Atrue);[discriminate|cbn;lia|sep auto].
 - eapply SXcell_live with(tp:=Tint8)(v:=V293_byteval 23)(R:=Atrue);[discriminate|cbn;lia|sep auto].
 - eapply SXcell_live with(tp:=Tint8)(v:=V293_byteval 0)(R:=Atrue);[discriminate|cbn;lia|sep auto].
Qed.
Lemma SXinitial_loads :
 load Tint32(FXmemory 0 4)(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8(FXmemory 0 4)(90%positive,0%Z)=Some(V293_byteval 99) /\
 load Tint8(FXmemory 0 4)(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8(FXmemory 0 4)(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 pose proof(FXentry 0 4 ltac:(lia)ltac:(lia))as Held.
 unfold FXentry_frame,FXframe,RCframe in Held.
 repeat split;eapply FXpluck with(ci:=nil)(R:=Atrue);sep auto.
Qed.
Theorem SXroundtrip_canaries : forall cst,exists bs Mf,
 V293_global_steps SXp cst(SXT,(FXge,SXles,FXmemory 0 4,(fun _=>false),SXaus true),FXct)
 (SXT,(FXge,SXles,Mf,(fun _=>false),SXaus true),FXct) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 0) /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 (forall k,k<4 ->get Mf(bs,Z.of_nat k)=None) /\
 load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 19)) /\
 load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99) /\
 load Tint8 Mf(99%positive,0%Z)=Some(V293_byteval 23) /\
 load Tint8 Mf(100%positive,0%Z)=Some(V293_byteval 0).
Proof.
 intro cst;destruct(SXcomplete_roundtrip cst)as(bs&Mf&Trace&Fresh&Nest&Target&Dead&Frame).
 assert(Outside:forall tp b,In b[90%positive;97%positive;99%positive;100%positive] ->
 load tp Mf(b,0%Z)=load tp(FXmemory 0 4)(b,0%Z)).
 { intros tp b Member;assert(N:b<>bs).
   { intro Eq;subst b;apply(Fresh(bs,0%Z)0%Z eq_refl);apply SXcanary_live;exact Member. }
   unfold load,loadm;rewrite V293_loadbytes_ext with(M:=FXmemory 0 4);[reflexivity| ].
   intros k Bound;apply Frame;[exact N| | | ];cbn in Member;intuition congruence. }
 exists bs;exists Mf;split;[exact Trace| ];split;[exact Nest| ];split;[exact Target| ];split;[exact Dead| ].
 destruct SXinitial_loads as(Count&Canary&Saved&Run).
 repeat split;rewrite Outside by(cbn;auto);assumption.
Qed.

(* Only EOI is neutralized, before either complete call. Both branches
   enter through the original interrupt rule; no whole-function ablation. *)
Definition SXcalls :=sseq(scall 301%Z nil)(sseq(scall 300%Z nil)(sprim exint)).
Definition SXcontrol_handler(clear:bool) :=sseq
 (if clear then sprim(eoi(Int.repr 1))else sskip None)SXcalls.
Definition SXcontrol_ip(clear:bool):intunit :=fun irq=>
 if Nat.eq_dec irq 1 then Some(SXcontrol_handler clear)else None.
Definition SXcontrol_p clear:lprog :=(SXpc,(SXprogram,SXpi,SXcontrol_ip clear)).
Definition SXprefix_code :=(curs SXcalls,(kenil,
 kint(cure(econst32(Int.repr 7)))(keop1 negation Tint32 kenil)FXcaller kstop)).
Definition SXprefix_ir(clear:bool) :=if clear then(fun _=>false)else isrupd(fun _=>false)1 true.
Theorem SXeoi_prefix_control : forall clear cst,
 V293_global_steps(SXcontrol_p clear)cst
 (SXT,(FXge,SXles,FXmemory 0 4,(fun _=>false),SXaus true),FXct)
 (set SXT FXct SXprefix_code,
 (FXge,set SXles FXct emp,FXmemory 0 4,SXprefix_ir clear,
 set(SXaus true)FXct(false,[1],nil)),FXct).
Proof.
 intros clear cst.
 assert(Local:V293_local_steps(pumerge SXprogram SXpi)
 (curs(SXcontrol_handler clear),(kenil,kstop))
 ((FXge,emp,FXmemory 0 4),isrupd(fun _=>false)1 true,(false,[1],nil))
 (curs SXcalls,(kenil,kstop))
 ((FXge,emp,FXmemory 0 4),SXprefix_ir clear,(false,[1],nil))).
 { unfold SXcontrol_handler;destruct clear.
   - eapply V293_local_cons.
     { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
     eapply V293_local_cons.
     { eapply eoi_step;[reflexivity|reflexivity|change(0<=1<2)%Z;lia]. }
     rewrite V293_interrupt_eoi_restores_ir by reflexivity.
     eapply V293_local_cons.
     { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
     apply V293_local_refl.
   - eapply V293_local_cons.
     { apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]. }
     eapply V293_local_cons.
     { apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]. }
     apply V293_local_refl. }
 pose proof(V293_interrupt_local_steps_global SXpc SXprogram SXpi(SXcontrol_ip clear)
 _ _ _ _ Local(cure(econst32(Int.repr 7)))(keop1 negation Tint32 kenil)FXcaller kstop
 SXT SXles(SXaus true)FXct cst I)as Lifted.
 unfold V293_global_steps;eapply rt1n_trans with(y:=
 (set SXT FXct(curs(SXcontrol_handler clear),(kenil,
 kint(cure(econst32(Int.repr 7)))(keop1 negation Tint32 kenil)FXcaller kstop)),
 (FXge,set SXles FXct emp,FXmemory 0 4,isrupd(fun _=>false)1 true,
 set(SXaus true)FXct(false,[1],nil)),FXct)).
 - eapply V293_interrupt_source_enter.
   + apply map_get_set.
   + apply map_get_set.
   + apply map_get_set.
   + unfold higherint;intros;reflexivity.
   + unfold INUM;lia.
   + reflexivity.
 - exact Lifted.
Qed.
Theorem SXeoi_only_effect :
 SXcontrol_p true=SXp /\
 SXcontrol_handler true=sseq(sprim(eoi(Int.repr 1)))SXcalls /\
 SXcontrol_handler false=sseq(sskip None)SXcalls /\
 (forall irq,irq<>1 ->SXcontrol_ip true irq=SXcontrol_ip false irq) /\
 SXprefix_ir true 1=false /\SXprefix_ir false 1=true.
Proof.
 split;[reflexivity| ];split;[reflexivity| ];split;[reflexivity| ];split.
 - intros irq N;unfold SXcontrol_ip;destruct(Nat.eq_dec irq 1);congruence.
 - split;reflexivity.
Qed.
