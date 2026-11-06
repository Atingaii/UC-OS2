(* Original selected TaskSim attached to the actual builder/switch heap. *)
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderDispatchGlobalProbe.
Require Import CertiOS.audit.probes.V293InterruptBuilderDispatchSwitchProbe.
Require Import CertiOS.audit.probes.V293InterruptControlSchedulerProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SelectedScalarTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlSwitchSimulation.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.

Definition SCcore:=V293_ready_current_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil 94%positive.
Definition SCinv:=V293_ready_current_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil 94%positive.
Definition SCframe:=V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **Atrue).
Definition SCpacket(M:mem):Prop:=exists Ms Mt Mf Mtail Os Ot Of Otail,
 join Mt Mf Mtail /\join Ms Mtail M /\join Ot Of Otail /\join Os Otail CSnext /\
 satp(JBge,emp,Ms,(fun _=>false),(true,nil,nil))Os(INV SCinv) /\
 satp(JBge,emp,Mt,(fun _=>false),(true,nil,nil))Ot(RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil) /\
 (JBge,emp,Mf,(fun _=>false),(true,nil,nil),Of,spec_done None)|=SCframe /\
 TaskSim BGglobal CSready(JBge,emp,Mt,(fun _=>false),(true,nil,nil))
 BDhigh CSready Ot V293_shared_li SCinv
 (fun s=>satp(fst s)(snd s)(RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.

Lemma SCshape : V293_scalar_client_state CSready.
Proof. left;exists(Int.repr 7);exists negation;exists Tint32;reflexivity. Qed.

Lemma SCafter_core : forall bs M,
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady **
 (V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **BDrest) ->
 (JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **SCframe).
Proof.
 intros bs M Held.
 unfold SWINVt in Held;fold(CurTid OwnershipReady)in Held.
 eapply astar_mono in Held;[ |eapply astar_mono;[apply V293_ready_switch_open|intros s H;exact H]|intros s H;exact H].
 assert(Target:forall m o,
 (JBge,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,(cons 0 nil),(cons false nil)),o,spec_done None)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ->
 (JBge,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,(cons 0 nil),(cons false nil)),o,spec_done None)|=V293_dispatch_cell 106%Z V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[Typed H].
   exists(Vptr OwnershipReady);apply astar_l_apure_intro;[ |exact Typed].
   exists 93%positive;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;reflexivity]. }
 assert(Pack:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil **
 (CurTid OwnershipReady **SCframe)).
 { unfold BDrest in Held;unfold V293_ready_storage_core,V293_ready_storage_extra;cbn[V293_storage].
   assert(Reorder:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
   V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
   (CurTid OwnershipReady **SCframe)))by(unfold SCframe;sep auto).
   apply sat_split in Reorder;destruct Reorder as(mt&mr&ot&orr&JM&JO&Cell&Rest).
   apply Target in Cell.
   assert(Named:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
   V293_dispatch_cell 106%Z V293_tcb_type **
   (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **(CurTid OwnershipReady **SCframe))).
   { apply sat_split';exists mt;exists mr;exists ot;exists orr;split;[exact JM| ];split;[exact JO| ];split;assumption. }
   clear Held;sep auto. }
 assert(Self:sched_self V293_scheduler CSnext).
 { exists OwnershipReady;split;[apply map_get_set|exists OwnershipTasks;split;[reflexivity|exact FXhighest]]. }
 apply V293_current_core_highest_frame with(bc:=94%positive)in Pack;[ |exact Self].
 fold SCcore in Pack.
 apply sat_split in Pack;destruct Pack as(mc&mr&oc&orr&JM&JO&Core&Rest).
 assert(CoreLocal:(JBge,emp,mc,(fun _=>false),(false,(cons 0 nil),(cons false nil)),oc,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply good_inv_prop;[apply V293_current_core_good|exact Core]. }
 assert(CoreReady:(JBge,emp,mc,(fun _=>false),(true,nil,nil),oc,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply V293_current_core_aux;exact CoreLocal. }
 assert(RestReady:(JBge,emp,mr,(fun _=>false),(true,nil,nil),orr,spec_done None)|=CurTid OwnershipReady **SCframe).
 { exact Rest. }
 apply sat_split';exists mc;exists mr;exists oc;exists orr.
 split;[exact JM| ];split;[exact JO| ];split;assumption.
Qed.

Lemma SCpartition : forall M,
 (JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **SCframe) ->SCpacket M.
Proof.
 intros M Held;unfold SCpacket.
 assert(Local:Aemp ==>LINV V293_shared_li OwnershipReady nil)by(apply V293_switch_local_empty).
 assert(Pack:(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **(LINV V293_shared_li OwnershipReady nil **SCframe))).
 { assert(E:(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 Aemp **(SCcore **(CurTid OwnershipReady **SCframe)))by(sep auto).
   eapply astar_mono in E;[ |exact Local|intros s H;exact H];sep auto. }
 exact(V293_scalar_current_TaskSim 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil 94%positive
 GXempty RDprogram GXempty BGip((fun _=>None),(fun _=>None),V293_scheduler)CSready
 V293_shared_li nil OwnershipReady SCframe JBge emp M(fun _=>false)true nil nil CSnext(spec_done None)
 SCshape ltac:(reflexivity)ltac:(discriminate)Pack).
Qed.

Theorem SCcompleted_simulation : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\
 V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady) /\
 lpstep BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting BGnextT cst(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 SCpacket Mf /\
 get BGnextT OwnershipWaiting=Some(SKIP,(kenil,BDK ## kint BGinterrupted CSke BGcaller CSks)) /\
 get BGnextT OwnershipReady=Some CSready /\
 get(BGcutL bs)OwnershipReady=Some emp /\
 @get tid localst ltaskstset TaskLStMap BGcutA OwnershipReady=Some(true,nil,nil).
Proof.
 intro cst;destruct(BGprepare cst)as(M&frame&bs&Ms&JM&Pre&Entry&Prefix&Owned&Read&OldCache).
 destruct(V293_control_switch_forward 80%positive 81%positive 82%positive
 99%positive 96%positive 97%positive GXempty RDprogram GXempty BGip
 (fun _=>None)(fun _=>None)V293_scheduler BGcutT CST cst OwnershipWaiting OwnershipReady
 106%Z BGtail CSke CSks(spec_done None)JBge(V293_cpu_lenv 120%Z bs)(BGcutL bs)Ms
 (fun _=>false)BGcutA (cons 0 nil)(cons false nil)93%positive 1%positive V293_tcb_type CSO(spec_done None)BDrest 1 0 0
 ltac:(lia)ltac:(lia)ltac:(lia)(map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 eq_refl Read eq_refl eq_refl CSchosen(map_get_set _ _ _)Owned)
 as(Mf&Low&Store&High&Event&After&Captured&Physical&Observed&All&Output&NoAbort&Frames).
 assert(Packet:SCpacket Mf)by(apply SCpartition;apply SCafter_core with(bs:=bs);exact After).
 assert(Full:V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady)).
 { eapply rt1n_trans with(y:=BGentered M);[exact Entry| ].
   eapply V293_global_trans;[exact Prefix| ].
   eapply rt1n_trans with(y:=(BGnextT,BGcutS bs Mf,OwnershipReady));[exact Low|apply rt1n_refl]. }
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 split;[exact JM| ];split;[exact Full| ];split;[exact Low| ];split;[exact High| ];split;[exact Packet| ].
 repeat first[split|solve[vm_compute;reflexivity]].
Qed.

Definition SCcenvs:cltenvs:=set emp OwnershipReady emp.
Definition SCclient:clientst:=(JBge,SCcenvs,emp).
Definition SCone:code:=(curs(sskip(Some(Vint32(Int.repr 7)))),(CSke,CSks)).
Definition SCtwo:code:=(curs(sskip(Some(Vint32(Int.not(Int.repr 7))))),(kenil,CSks)).
Definition SCend:code:=(SKIP,(kenil,kstop)).
Definition SCT1:=set BGnextT OwnershipReady SCone.
Definition SCT2:=set SCT1 OwnershipReady SCtwo.
Definition SCT3:=set SCT2 OwnershipReady SCend.
Definition SCH1:=set CSTnext OwnershipReady SCone.
Definition SCH2:=set SCH1 OwnershipReady SCtwo.
Definition SCH3:=set SCH2 OwnershipReady SCend.

Lemma SCclient_step : forall bs M T Th C C',
 get T OwnershipReady=Some C ->get Th OwnershipReady=Some C ->
 V293_scalar_client_state C ->
 (forall pu m,cstep pu C m C' m) ->
 lpstep BGglobal T SCclient(BGcutS bs M)OwnershipReady
 (set T OwnershipReady C')SCclient(BGcutS bs M)OwnershipReady /\
 hpstep BDhigh Th SCclient CSnext(set Th OwnershipReady C')SCclient CSnext.
Proof.
 intros bs M T Th C C' Get GetH Shape Step.
 assert(Projection:projS(BGcutS bs M)OwnershipReady=
 Some(JBge,emp,M,(fun _=>false),(true,nil,nil)))by(vm_compute;reflexivity).
 assert(EqualEnv:set SCcenvs OwnershipReady emp=SCcenvs).
 { apply get_set_same;apply map_get_set. }
 assert(ClientLow:forall o,ltstep BGglobal OwnershipReady C SCclient o C' SCclient o).
 { intro o;unfold BGglobal,SCclient;eapply clt_step;try reflexivity.
   - apply Step.
   - apply V293_scalar_client_not_os;exact Shape.
   - apply map_get_set.
   - rewrite EqualEnv;reflexivity. }
 split.
 - eapply pt_step;[exact Get|reflexivity|exact Projection|exact Projection| |apply ClientLow].
   unfold Steq,Dteq,Piteq;repeat split;intros;reflexivity.
 - eapply hp_step;[apply map_get_set| |exact GetH|reflexivity].
   unfold BDhigh,SCclient;eapply htclt_step;try reflexivity.
   + apply Step.
   + apply map_get_set.
   + rewrite EqualEnv;reflexivity.
Qed.

(* Three actual non-stuttering original steps, not merely a reflexive closure. *)
Theorem SCthree_steps : forall bs M,
 lpstep BGglobal BGnextT SCclient(BGcutS bs M)OwnershipReady SCT1 SCclient(BGcutS bs M)OwnershipReady /\
 lpstep BGglobal SCT1 SCclient(BGcutS bs M)OwnershipReady SCT2 SCclient(BGcutS bs M)OwnershipReady /\
 lpstep BGglobal SCT2 SCclient(BGcutS bs M)OwnershipReady SCT3 SCclient(BGcutS bs M)OwnershipReady /\
 hpstep BDhigh CSTnext SCclient CSnext SCH1 SCclient CSnext /\
 hpstep BDhigh SCH1 SCclient CSnext SCH2 SCclient CSnext /\
 hpstep BDhigh SCH2 SCclient CSnext SCH3 SCclient CSnext /\
 CSready<>SCone /\SCone<>SCtwo /\SCtwo<>SCend /\
 get SCT3 OwnershipWaiting=Some(SKIP,(kenil,BGtail)) /\
 get SCT3 OwnershipReady=Some SCend.
Proof.
 intros bs M.
 assert(One:forall pu m,cstep pu CSready m SCone m).
 { intros;eapply expr_step;[reflexivity|apply ec32_step]. }
 assert(Two:forall pu m,cstep pu SCone m SCtwo m).
 { intros;eapply expr_step;[reflexivity|apply evuop_step;reflexivity]. }
 assert(Three:forall pu m,cstep pu SCtwo m SCend m).
 { intros;eapply stmt_step;[reflexivity|apply svseq_step]. }
 destruct(SCclient_step bs M BGnextT CSTnext CSready SCone
 ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)SCshape One)as[L1 H1].
 destruct(SCclient_step bs M SCT1 SCH1 SCone SCtwo
 (map_get_set _ _ _)(map_get_set _ _ _)
 ltac:(right;left;exists(Vint32(Int.repr 7));exists negation;exists Tint32;reflexivity)Two)as[L2 H2].
 destruct(SCclient_step bs M SCT2 SCH2 SCtwo SCend
 (map_get_set _ _ _)(map_get_set _ _ _)
 ltac:(right;right;left;exists(Vint32(Int.not(Int.repr 7)));reflexivity)Three)as[L3 H3].
 split;[exact L1| ];split;[exact L2| ];split;[exact L3| ];
 split;[exact H1| ];split;[exact H2| ];split;[exact H3| ].
 repeat split;try discriminate;vm_compute;reflexivity.
Qed.

Theorem SCfull_client_run : exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\
 V293_global_steps BGglobal SCclient
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (SCT3,BGcutS bs Mf,OwnershipReady) /\
 lpstep BGglobal BGcutT SCclient(BGcutS bs Ms)OwnershipWaiting BGnextT SCclient(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST SCclient CSO CSTnext SCclient CSnext /\
 SCpacket Mf /\
 get SCT3 OwnershipWaiting=Some(SKIP,(kenil,BDK ## kint BGinterrupted CSke BGcaller CSks)) /\
 get SCT3 OwnershipReady=Some SCend.
Proof.
 destruct(SCcompleted_simulation SCclient)as(M&frame&bs&Ms&Mf&JM&Full&Low&High&Packet&Saved&Selected&Env&Aux).
 destruct(SCthree_steps bs Mf)as(L1&L2&L3&H1&H2&H3&N1&N2&N3&SavedFinal&End).
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 split;[exact JM| ];split.
 - eapply V293_global_trans;[exact Full| ].
   eapply rt1n_trans with(y:=(SCT1,BGcutS bs Mf,OwnershipReady));[exact L1| ];
   eapply rt1n_trans with(y:=(SCT2,BGcutS bs Mf,OwnershipReady));[exact L2| ];
   eapply rt1n_trans with(y:=(SCT3,BGcutS bs Mf,OwnershipReady));[exact L3|apply rt1n_refl].
 - split;[exact Low| ];split;[exact High| ];split;[exact Packet| ];split;assumption.
Qed.
