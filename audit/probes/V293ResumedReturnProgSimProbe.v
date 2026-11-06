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
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ResumedReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.

Definition RPpending:code:=
 (SKIP,(kenil,kseq(sprim excrit)(kseq sret CPcall))).
Definition RPcode:code:=(curs(sprim(switch 106%Z)),(kenil,HPpending)).
Definition RPtasks:tasks:=set(sig OwnershipReady RPpending)OwnershipWaiting RPcode.
Definition RPenvs:cltenvs:=set(sig OwnershipReady(V293_cpu_lenv 120%Z 98%positive))OwnershipWaiting emp.
Definition RPaux cs ncs:ltaskstset:=
 set(sig OwnershipReady((false,nil,false::ncs):localst))OwnershipWaiting(false,nil,cs).
Definition RPstate M cs ncs:osstate:=(CGge,RPenvs,M,(fun _=>false),RPaux cs ncs).
Definition RPswitched:=set RPtasks OwnershipWaiting(SKIP,(kenil,HPpending)).
Definition RPfinal:=set RPswitched OwnershipReady(SKIP,(kenil,kstop)).
Definition RPreturned M cs ncs:osstate:=
 (CGge,set RPenvs OwnershipReady emp,M,(fun _=>false),set(RPaux cs ncs)OwnershipReady(false,nil,ncs)).

(* Construct both pointer writes and the local free from spatial ownership.
   No store-success or simulation hypothesis is provided by a caller. *)
Lemma RPstorage : exists M Msw Mret,
 store(Tptr V293_tcb_type)(NPinitial 1)(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 (CGge,CGle,Msw,(fun _=>false),(false,nil,false::nil),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue /\
 free Tint32 98%positive Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None) /\
 (forall b i,b<>98%positive ->get Mret(b,i)=get Msw(b,i)).
Proof.
 pose proof(CPtyped_updated 1(false::nil)ltac:(lia))as Held.
 assert(Owned:CGstate OwnershipWaiting(NPinitial 1)(false::nil)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue))).
 { unfold CPother,V293_owned_record_cell in *;sep auto. }
 destruct(V293_owned_record_cell_update (93%positive,0%Z)(Tptr V293_tcb_type)
 (Vptr OwnershipWaiting)(Vptr OwnershipReady) _ _ _ _ _ _ _ _ eq_refl Owned)
 as(M&TargetStore&AfterTarget).
 assert(SwitchOwned:CGstate OwnershipWaiting M(false::nil)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue)).
 { clear Held Owned;sep auto. }
 destruct(V293_ready_current_write 80%positive 81%positive 82%positive
 OwnershipWaiting OwnershipReady _ CGge CGle M(fun _=>false)(false,nil,false::nil)
 (RIabstract OwnershipWaiting)(spec_done None)1%positive V293_tcb_type SwitchOwned eq_refl)
 as(Msw&Store&AfterSwitch&ReadCurrent&Frame).
 assert(Saved:(CGge,CGle,Msw,(fun _=>false),(false,nil,false::nil),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { unfold CGstate,SPOf in *;clear Held Owned AfterTarget SwitchOwned;sep auto. }
 destruct(V293_cpu_release _ _ _ _ _ _ _ _ _ _ Saved)
 as(Mret&Free&Rest&Removed&Outside).
 exists M;exists Msw;exists Mret;split;[exact TargetStore| ];split.
 - eapply V293_store_readback;[reflexivity|exact TargetStore].
 - repeat split;assumption.
Qed.

Lemma RPbinding : CPpo 114%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,CPfullbody).
Proof. unfold CPpo,CPfunction;destruct(Z.eq_dec 114%Z 114%Z);[reflexivity|congruence]. Qed.

Lemma RPfinite_switch_and_return : forall M Msw Mret cs ncs ip,
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) ->
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw ->
 free Tint32 98%positive Msw=Some Mret ->
 (CGge,CGle,Msw,(fun _=>false),(false,nil,false::nil),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue ->
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (RPtasks,RPstate M cs ncs,OwnershipWaiting)
 (RPfinal,RPreturned Mret cs ncs,OwnershipReady).
Proof.
 intros M Msw Mret cs ncs ip Read Store Free Saved.
 assert(SavedNext:(CGge,V293_cpu_lenv 120%Z 98%positive,Msw,(fun _=>false),
 (false,nil,false::ncs),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { eapply good_inv_prop;[cbn;split;exact I|exact Saved]. }
 destruct(V293_int_exit_pending_return RCprogram CPpo CGempty ip RPswitched RPenvs
 (RPaux cs ncs)OwnershipReady HPcst CGge Msw(fun _=>false)false false nil ncs
 SPOf(spec_done None)Atrue 114%Z CPfullbody emp kstop Tvoid dnil
 (dcons 120%Z Tint32 dnil)120%Z 98%positive(Vint32 Int.zero)
 RPbinding I eq_refl eq_refl eq_refl SavedNext)
 as(Mf&Return&Free2&Rest&Removed&Frame).
 assert(Mf=Mret)by congruence;subst Mf.
 unfold V293_global_steps;eapply rt1n_trans;[ |exact Return].
 eapply V293_switch_progress with(le:=emp)(bt:=93%positive)(bc:=1%positive)
 (tp:=V293_tcb_type)(si:=nil)(cs:=cs);try reflexivity;try eassumption.
Qed.

Theorem RPactual_switch_and_resume_simulation : forall cs ncs ip,
 exists M Msw Mret,
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)M(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 free Tint32 98%positive Msw=Some Mret /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (RPtasks,RPstate M cs ncs,OwnershipWaiting)
 (RPfinal,RPreturned Mret cs ncs,OwnershipReady) /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None) /\
 (forall b i,b<>98%positive ->get Mret(b,i)=get Msw(b,i)) /\
 lpstep(RCprogram,(CPpo,CGempty,ip))RPtasks HPcst(RPstate M cs ncs)OwnershipWaiting
 RPswitched HPcst(RPstate Msw cs ncs)OwnershipReady /\
 ProgSim(RCprogram,(CPpo,CGempty,ip))RPtasks(RPstate M cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting /\
 get RPfinal OwnershipWaiting=Some(SKIP,(kenil,HPpending)) /\
 get(set RPenvs OwnershipReady emp)OwnershipWaiting=Some emp /\
 get(set(RPaux cs ncs)OwnershipReady(false,nil,ncs))OwnershipWaiting=Some(false,nil,cs).
Proof.
 intros cs ncs ip;destruct RPstorage as(M&Msw&Mret&TargetStore&Read&Store&Saved&Free&Removed&Frame).
 exists M;exists Msw;exists Mret;split;[exact Read| ];split;[exact Store| ];split;[exact Free| ];split.
 - eapply RPfinite_switch_and_return;eassumption.
 - split;[exact Removed| ];split;[exact Frame| ];split.
   + eapply V293_switch_progress with(le:=emp)(bt:=93%positive)(bc:=1%positive)
   (tp:=V293_tcb_type)(si:=nil)(cs:=cs);try reflexivity;try eassumption.
   + split.
     * eapply V293_switch_pending_exit_progsim with(le:=emp)(next:=OwnershipReady)
     (Msw:=Msw)(Mret:=Mret)(x:=106%Z)(ks:=HPpending)(bt:=93%positive)(bc:=1%positive)
     (tp:=V293_tcb_type)(si:=nil)(cs:=cs)(nsi:=nil)(ncs:=ncs)
     (f:=114%Z)(body:=CPfullbody)(caller:=emp)(tail:=kstop)(saved:=120%Z)(b:=98%positive)
     (Thf:=HPThf)(Of:=SPOf);try discriminate;try reflexivity;try eassumption.
       -- eapply hp_stepS;[apply HPschedule|apply hp_stepO].
       -- eapply SPterminal;[apply map_get_set| |unfold SPOf;apply map_get_set].
          unfold projS,projD;cbn;repeat rewrite map_get_set;reflexivity.
     * repeat split;unfold RPfinal,RPswitched,RPenvs,RPaux;
     rewrite map_get_set' by discriminate;apply map_get_set.
Qed.

(* Single-factor controls keep the physical heap and task code fixed. *)
Definition RPexcrit_tasks:=set RPswitched OwnershipReady
 (curs(sprim excrit),(kenil,kseq sret CPcall)).
Definition RPcritical_state M cs stack:osstate:=
 (CGge,RPenvs,M,(fun _=>false),set(RPaux cs nil)OwnershipReady(false,nil,stack)).

Theorem RPempty_stack_aborts : forall M cs ip,
 lpstepabt(RCprogram,(CPpo,CGempty,ip))RPexcrit_tasks HPcst
 (RPcritical_state M cs nil)OwnershipReady.
Proof.
 intros M cs ip.
 assert(Inside:InOS(curs(sprim excrit),(kenil,kseq sret CPcall))(pumerge CPpo CGempty)).
 { unfold CPcall;eapply V293_context_inos with(ks:=kcall 114%Z CPfullbody emp kstop);
   [eapply V293_bound_call_inos;exact RPbinding|reflexivity|reflexivity]. }
 eapply progabort.
 - exact None.
 - apply map_get_set.
 - unfold RPcritical_state,projS,projD;cbn;rewrite map_get_set;reflexivity.
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

Theorem RPnonempty_stack_steps : forall M cs ncs ip,
 lpstep(RCprogram,(CPpo,CGempty,ip))RPexcrit_tasks HPcst
 (RPcritical_state M cs(false::ncs))OwnershipReady
 (set RPexcrit_tasks OwnershipReady(SKIP,(kenil,kseq sret CPcall)))HPcst
 (CGge,RPenvs,M,(fun _=>false),
 set(set(RPaux cs nil)OwnershipReady(false,nil,false::ncs))OwnershipReady(false,nil,ncs))OwnershipReady.
Proof.
 intros M cs ncs ip.
 eapply V293_critical_progress with(le:=V293_cpu_lenv 120%Z 98%positive)
 (after:=(false,nil,ncs));try reflexivity.
 - unfold CPcall;eapply V293_context_inos with(ks:=kcall 114%Z CPfullbody emp kstop);
   [eapply V293_bound_call_inos;exact RPbinding|reflexivity|reflexivity].
 - apply excrit_step;reflexivity.
Qed.

Theorem RPzero_high_match_rejected : forall M cs ncs ip,
 ~ProgSim(RCprogram,(CPpo,CGempty,ip))RPfinal(RPreturned M cs ncs)
 SPph HPThf(RIabstract OwnershipWaiting)HPcst OwnershipReady.
Proof.
 intros M cs ncs ip H;inversion H.
 assert(get(RIabstract OwnershipWaiting)curtid=Some(oscurt OwnershipWaiting))by reflexivity.
 assert(OwnershipReady=OwnershipWaiting)by congruence;discriminate.
Qed.
