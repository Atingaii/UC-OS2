Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293ExitDispatchProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.

Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.auxlibs.MapLib.

Require Import CertiOS.audit.probes.V293ExitCallDispatchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.

Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.

Definition CPdispatch:=V293_exit_boundary_dispatch 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition CPfullbody:=V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z (V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition CPfunction:=V293_exit_boundary_function 112%Z 110%Z 111%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z (V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition CPpo:progunit:=fun f=>if Z.eq_dec f 114%Z then Some CPfunction else CGpo f.
Definition CPcall:=kcall 114%Z CPfullbody (emp:env) kstop.
Definition CPcritical:=sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch 110%Z 111%Z CPdispatch)(sprim excrit)).
Definition CPcode:code:=(curs CPcritical,(kenil,kseq sret CPcall)).
Definition CPtasks:tasks:=set emp OwnershipWaiting CPcode.
Definition CPstate M cs:osstate:=(CGge,sig OwnershipWaiting CGle,M,(fun _=>false),
 sig OwnershipWaiting ((false,nil,cs):localst)).
Definition CPdecr:=V293_exit_decrement_memory(NPinitial 2)96%positive 2.

Lemma CPdecrement : CPdecr=NPinitial 1.
Proof.
 unfold CPdecr,V293_exit_decrement_memory;cbn[Nat.eqb Nat.pred].
 unfold NPinitial,V293_write_byte;apply HalfPermMap.extensionality;intro a.
 change(get(set(set CEM(96%positive,0%Z)(true,Byte(Byte.repr 2)))
 (96%positive,0%Z)(true,Byte(Byte.repr 1)))a=
 get(set CEM(96%positive,0%Z)(true,Byte(Byte.repr 1)))a).
 destruct a as[b i];destruct(Pos.eq_dec b 96%positive)as[B|B].
 - subst b;destruct(Z.eq_dec i 0)as[E|E];[subst i;repeat rewrite map_get_set;reflexivity| ].
   repeat rewrite map_get_set' by congruence;reflexivity.
 - repeat rewrite map_get_set' by congruence;reflexivity.
Qed.

Definition CPother:asrt:=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((98%positive,0%Z),Tint32,Vint32 Int.zero) ** RCframe)))))).

Lemma CPtyped_updated : forall n cs,n<256 ->
 CGstate OwnershipWaiting(NPinitial n)cs |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval n) ** CPother.
Proof.
 intros n cs Bound.
 assert(Owned:CGstate OwnershipWaiting CEM cs |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) ** CPother).
 { pose proof(CEtyped_heap cs)as Held;unfold CPother,CGframe in *;
   cbn[CGextra V293_owned_record_cells]in Held;sep auto. }
 exact(proj2(V293_owned_byte_update (96%positive,0%Z)(V293_byteval 0)n CPother
 CGge CGle CEM(fun _=>false)(false,nil,cs)(RIabstract OwnershipWaiting)(spec_done None)Bound Owned)).
Qed.

Lemma CPsaved_release : exists Mf,free Tint32 98%positive CPdecr=Some Mf.
Proof.
 assert(Owned:CGstate OwnershipWaiting(NPinitial 1)nil |=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { pose proof(CPtyped_updated 1 nil ltac:(lia))as Held;
   unfold CPother,V293_owned_record_cell in Held;sep auto. }
 destruct(V293_cpu_release CGge CGle(NPinitial 1)(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)98%positive(Vint32 Int.zero)Atrue Owned)
 as(Mf&Free&Rest).
 exists Mf;rewrite CPdecrement;exact Free.
Qed.

Theorem CPquiet_return_simulation : forall cs ip,exists Mf,
 free Tint32 98%positive CPdecr=Some Mf /\
 (forall i,(0<=i<4)%Z ->get Mf(98%positive,i)=None) /\
 (forall b i,b<>98%positive ->get Mf(b,i)=get CPdecr(b,i)) /\
 ProgSim(RCprogram,(CPpo,CGempty,ip))CPtasks(CPstate(NPinitial 2)cs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros cs ip;destruct CPsaved_release as[Mf Free];exists Mf.
 split;[exact Free| ];split.
 - intros i Range;replace i with(0+Z.of_nat(Z.to_nat i))%Z by(rewrite Z2Nat.id;lia).
   eapply V293_freeb_removed;[exact Free|cbn;lia].
 - split;[intros;eapply V293_freeb_outside;[exact Free|left;assumption]| ].
   unfold CPtasks,CPcode,CPcritical,CPstate,CPcall.
   eapply V293_exit_quiet_return_progsim with(le:=CGle)(caller:=(emp:env))
   (si:=nil)(cs:=cs)(bs:=98%positive)(bn:=96%positive)(n:=2)(locked:=0)(Mf:=Mf);
   try reflexivity;try lia;try exact Free.
   + eapply V293_bound_call_inos;unfold CPpo,CPfunction;destruct(Z.eq_dec 114%Z 114%Z);[reflexivity|congruence].
   + unfold NPinitial;apply V293_write_byte_load;lia.
   + intros _;exists(Byte(Byte.repr 2));unfold NPinitial,V293_write_byte;apply map_get_set.
   + eapply SPterminal;[apply map_get_set| |reflexivity].
     unfold projS;simpl;repeat rewrite map_get_set;reflexivity.
Qed.

Theorem CPexcrit_stack_control : forall p ks m ir si cs,
 loststep p(curs(sprim excrit),(kenil,ks))(m,ir,(false,si,false::cs))
 (SKIP,(kenil,ks))(m,ir,(false,si,cs)) /\
 loststep p(curs(sprim excrit),(kenil,ks))(m,ir,(false,si,true::cs))
 (SKIP,(kenil,ks))(m,ir,(true,si,cs)) /\
 ~loststep p(curs(sprim excrit),(kenil,ks))(m,ir,(false,si,true::cs))
 (SKIP,(kenil,ks))(m,ir,(false,si,cs)).
Proof.
 intros;split;[apply excrit_step;reflexivity| ];split;[apply excrit_step;reflexivity| ].
 intro H;destruct(V293_excrit_successor _ _ _ _ _ _ _ _ _ _ H)as[_ E];discriminate.
Qed.

Lemma CPempty_stack_no_step : forall p ks m ir si C' st',
 ~loststep p(curs(sprim excrit),(kenil,ks))(m,ir,(false,si,nil))C' st'.
Proof.
 intros p ks m ir si C' st' H;inversion H;subst;try discriminate.
 exfalso;eapply V293_cstep_not_primitive;[eassumption|reflexivity].
Qed.

Theorem CPempty_stack_aborts : forall ip,
 lpstepabt(RCprogram,(CPpo,CGempty,ip))
 (set emp OwnershipWaiting(curs(sprim excrit),(kenil,CPcall)))HPcst
 (CPstate(NPinitial 2)nil)OwnershipWaiting.
Proof.
 intro ip.
 assert(Inside:InOS(curs(sprim excrit),(kenil,CPcall))(pumerge CPpo CGempty)).
 { unfold CPcall;eapply V293_bound_call_inos;unfold CPpo,CPfunction;
   destruct(Z.eq_dec 114%Z 114%Z);[reflexivity|congruence]. }
 eapply progabort.
 - exact None.
 - apply map_get_set.
 - unfold CPstate,projS;simpl;rewrite map_get_sig;reflexivity.
 - unfold IsSwitch;intros(?&?&E);discriminate.
 - unfold IsStkInit;intros(?&?&?&?&E);discriminate.
 - unfold IsStkFree;intros(?&?&E);discriminate.
 - unfold IsEnd;intros(?&E);discriminate.
 - eapply taskabort;[reflexivity| ].
   intros[(C'&st'&cs'&H)|(C'&st'&cs'&ev&H)];inversion H;subst;
   repeat match goal with E:(_,_) =(_,_) |- _ =>inversion E;subst;clear E end.
   + contradiction.
   + eapply CPempty_stack_no_step;eassumption.
   + contradiction.
Qed.
