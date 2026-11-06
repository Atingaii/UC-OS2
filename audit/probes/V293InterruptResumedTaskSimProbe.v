(* Same RDprogram, nonempty real resources, explicit pending-context boundary.
   This does not claim the selected Ready task reaches the supplied context. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptResumedTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SelectedScalarTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.audit.probes.V293InterruptBuilderOwnedCPUProbe.
Require Import CertiOS.audit.probes.V293SelectedScalarTaskSimProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderDispatchGlobalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.audit.probes.V293InterruptControlSchedulerProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition RSbody:=V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition RSpending:code:=(SKIP,(kenil,kseq(sprim excrit)(kseq sret
 (kcall 300%Z RSbody emp(kseq(sprim exint)
 (kint(cure(econst32(Int.repr 7)))CSke BGcaller CSks)))))).
Definition RSaux:localst:=(false,(cons 0 nil),(cons false nil)).
Definition RSowned bs:=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **(SCcore **CurTid OwnershipReady).
Definition RSpost s:=satp(fst s)(snd s)(RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil).
Definition RSsimulation bs M O:=
 TaskSim BGglobal RSpending(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),RSaux)
 (GXempty,((fun _=>None),(fun _=>None),V293_scheduler))CSready O V293_shared_li SCinv RSpost OwnershipReady.

Lemma RSbinding : RDprogram 300%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,RSbody).
Proof. reflexivity. Qed.

Lemma RSrecontext : forall bs M O,
 (JBge,emp,M,(fun _=>false),(true,nil,nil),O,spec_done None)|=RSowned bs ->
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),RSaux,O,spec_done None)|=RSowned bs.
Proof.
 intros bs M O Held;unfold RSowned in *.
 apply sat_split in Held;destruct Held as(mc&mr&oc&orr&JM&JO&Cell&Rest).
 apply sat_split in Rest;destruct Rest as(ms&mt&os&ot&JS&JT&Core&Tid).
 assert(CoreLe:(JBge,V293_cpu_lenv 120%Z bs,ms,(fun _=>false),(true,nil,nil),os,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply good_inv_prop;[apply V293_current_core_good|exact Core]. }
 assert(CoreAux:(JBge,V293_cpu_lenv 120%Z bs,ms,(fun _=>false),RSaux,os,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply V293_current_core_aux;exact CoreLe. }
 apply sat_split';exists mc;exists mr;exists oc;exists orr;split;[exact JM| ];split;[exact JO| ];split;[exact Cell| ].
 apply sat_split';exists ms;exists mt;exists os;exists ot;split;[exact JS| ];split;[exact JT| ];split;assumption.
Qed.

(* Original TaskSim, not a local replacement relation or successor premise. *)
Lemma RSclosed : forall bs M O,
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),RSaux,O,spec_done None)|=RSowned bs ->
 RSsimulation bs M O.
Proof.
 intros bs M O Held;unfold RSsimulation,RSpending,RSaux,RSowned,RSpost in *.
 eapply V293_interrupt_pending_return_TaskSim with(op:=spec_done None).
 - exact RSbinding.
 - change(0<2);lia.
 - exact SCshape.
 - reflexivity.
 - exact Held.
Qed.

Lemma RSactual : forall bs M O,
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),RSaux,O,spec_done None)|=RSowned bs ->
 exists Mr,free Tint32 bs M=Some Mr /\
 (JBge,V293_cpu_lenv 120%Z bs,Mr,(fun _=>false),RSaux,O,spec_done None)|=SCcore **CurTid OwnershipReady /\
 (forall k,k<4 ->get Mr(bs,Z.of_nat k)=None) /\
 forall frame Mall,join M frame Mall ->exists Mall',join Mr frame Mall' /\
 V293_local_steps(pumerge RDprogram GXempty)RSpending
 (JBge,V293_cpu_lenv 120%Z bs,Mall,(fun _=>false),RSaux)
 CSready(JBge,BGcaller,Mall',(fun _=>false),(true,nil,nil)).
Proof.
 intros bs M O Held;unfold RSowned,RSaux in Held.
 destruct(V293_interrupt_pending_return_execution(pumerge RDprogram GXempty)
 300%Z RSbody emp(cure(econst32(Int.repr 7)))CSke BGcaller CSks
 JBge M(fun _=>false)0 nil nil 120%Z bs(Vint32 Int.zero)O(spec_done None)
 (SCcore **CurTid OwnershipReady)Held)as(Mr&Free&Rest&Trace).
 exists Mr;split;[exact Free| ];split;[exact Rest| ];split.
 - intros k Bound;replace(Z.of_nat k)with(0+Z.of_nat k)%Z by lia.
   eapply V293_freeb_removed;[exact Free|exact Bound].
 - exact Trace.
Qed.

(* The resource premise is inhabited on a partition of the actual builder
   endpoint.  Only resource recontextualization is asserted, NOT reachability
   of RSpending from the stored Ready or Waiting continuation. *)
Theorem RSnonempty : exists bs M frame Whole O Of Mr,
 join M frame Whole /\join O Of CSnext /\
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),RSaux,O,spec_done None)|=RSowned bs /\
 RSsimulation bs M O /\free Tint32 bs M=Some Mr /\
 (forall k,k<4 ->get Mr(bs,Z.of_nat k)=None) /\
 (forall F Mall,join M F Mall ->exists Mall',join Mr F Mall' /\
 V293_local_steps(pumerge RDprogram GXempty)RSpending
 (JBge,V293_cpu_lenv 120%Z bs,Mall,(fun _=>false),RSaux)
 CSready(JBge,BGcaller,Mall',(fun _=>false),(true,nil,nil))).
Proof.
 destruct(OCcompleted_owned SCclient)as(M0&F0&bs&Ms&Whole&J0&Prefix&Low&High&Packet&Core&Saved&Selected&Env&Aux).
 assert(Split:(JBge,emp,Whole,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 RSowned bs **SCframe).
 { unfold RSowned,OCframe,SCframe in *;clear Packet;sep auto. }
 apply sat_split in Split;destruct Split as(M&frame&O&Of&JM&JO&Owned&External).
 apply RSrecontext in Owned.
 pose proof(RSclosed bs M O Owned)as Sim.
 destruct(RSactual bs M O Owned)as(Mr&Free&Rest&Removed&Trace).
 exists bs;exists M;exists frame;exists Whole;exists O;exists Of;exists Mr.
 repeat first[assumption|split].
Qed.
