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

Require Import CertiOS.audit.probes.V293ResumedReturnProgSimProbe.

Local Open Scope nat_scope.
(* No extra production wrapper: instantiate the existing stable interface. *)
Definition DPprogram:=pumerge CPpo CGempty.
Definition DPtyped (M:mem) (cs:cs):=(CGge,(emp:env),M,((fun _=>false):isr),
 ((false,nil,cs):localst),RIabstract OwnershipWaiting,spec_done None).
Definition DPtasks:=set RPtasks OwnershipWaiting XPcode.

Lemma DPscheduled_canonical : forall ks,
 exists M,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
 cstepstar DPprogram
 (curs(V293_OSSched_unlocked_prefix 107%Z 105%Z 103%Z 106%Z),(kenil,ks))
 (CGge,(emp:env),CGmemory OwnershipWaiting true 0 0)
 (SKIP,(kenil,ks))(CGge,(emp:env),M) /\
 DPtyped M nil|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** EPbefore.
Proof.
 intros ks.
 assert(Held:DPtyped(CGmemory OwnershipWaiting true 0 0)nil|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe 0 0))))).
 { eapply V293_ready_lenv_frame;[repeat split;try exact I;apply CGframe_good| ].
   exact(CGentry OwnershipWaiting true 0 0 nil ltac:(lia)ltac:(lia)). }
 destruct(V293_ready_dispatch_call 80%positive 81%positive 82%positive DPprogram ks
 CGge (emp:env)(CGmemory OwnershipWaiting true 0 0)(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) ** CGframe 0 0))
 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 92%positive 91%positive 93%positive(V293_byteval 88)(Vptr OwnershipWaiting)
 ltac:(vm_compute;reflexivity)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 ltac:(repeat split;try exact I;apply CGframe_good)
 (CGlookup OwnershipWaiting true 0 0)Held)
 as(tasks&lo&hi&entries&next&message&b&Ms&Mskip&M&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&High&Exec&Store&After&Target&Sched&Pre&Live&Dead&CallFrame&TargetFrame).
 pose proof(RIfixed_tasks OwnershipWaiting).
 assert(tasks=OwnershipTasks)by congruence;subst tasks.
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];apply V293_ready_selection_range;assumption||reflexivity. }
 destruct(RTonly_ready _ _ _ Range Task)as[Selected[Next Message]];subst next message.
 rewrite Selected in After,Skipped,High.
 assert(Cells:DPtyped Mskip nil |=
 V293_owned_record_cells (((91%positive,0%Z),Tint8,V293_byteval 4)::nil) ** Atrue).
 { cbn[V293_owned_record_cells];clear -Skipped;sep auto. }
 destruct(V293_owned_cells_byte_writable (((91%positive,0%Z),Tint8,V293_byteval 4)::nil)
 (91%positive,0%Z)(V293_byteval 4)Atrue CGge (emp:env) Mskip(fun _=>false)
 (false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)
 ltac:(simpl;auto)Cells)as[raw Full].
 pose proof(V293_full_byte_load_encoding Mskip(91%positive,0%Z)4 raw Full High)as Output.
 assert(Canonical:Mskip=CFfinal).
 { apply HalfPermMap.extensionality;intros[c i].
   change(get Mskip(c,i)=get CFfinal(c,i)).
   destruct(Pos.eq_dec c 91%positive)as[E|E].
   - subst c;destruct(Z.eq_dec i 0)as[Z0|Z0].
     + subst i;unfold CFfinal,V293_write_byte;rewrite map_get_set;exact Output.
     + unfold CFfinal,V293_write_byte;rewrite map_get_set' by congruence.
       apply CallFrame;congruence.
   - unfold CFfinal,V293_write_byte;rewrite map_get_set' by congruence.
     apply CallFrame;congruence. }
 rewrite Canonical in Store.
 exists M;split;[exact Store| ];split;[exact Exec| ].
 unfold EPbefore,DPtyped;clear -After;sep auto.
Qed.


Definition DPtail:=sif(V293_OSSched_different 103%Z 108%Z)
 (sseq(V293_OSSched_increment 109%Z)
 (sseq(sskip None)(V293_interrupt_handoff 103%Z 108%Z 106%Z)))(sskip None).

Lemma DPdispatch_storage : forall ks, exists M M1 Mc Msw Mret,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
 evalval(V293_OSSched_different 103%Z 108%Z)(CGge,(emp:env),M)=Some(Vint32 Int.one) /\
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 store Tint32 M(95%positive,0%Z)(Vint32 Int.zero)=Some M1 /\
 load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4) /\
 store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc /\
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 (CGge,(emp:env),Msw,(fun _=>false),(false,nil,nil),SPOf,spec_done None)|=Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue /\
 free Tint32 98%positive Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None) /\
 (forall b i,b<>98%positive ->get Mret(b,i)=get Msw(b,i)) /\
 cstepstar DPprogram(curs XPbody,(kenil,ks))(CGge,(emp:env),CEM)
 (curs(sprim(switch 106%Z)),(kenil,ks))(CGge,(emp:env),Mc).
Proof.
 intros ks.
 destruct(DPscheduled_canonical(kseq DPtail ks))as(M&TargetStore&Schedule&Before).
 assert(Wrap:Int.add Int.mone Int.one=Int.zero)by(vm_compute;apply Int.mkint_eq;reflexivity).
 assert(Owned:DPtyped M(nil)|=
 V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** CGframe 0 0))))).
 { unfold EPbefore in Before;sep auto. }
 assert(Counter:load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone)).
 { eapply V293_record_star_load_l with(s:=DPtyped M(nil));
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Owned]. }
 assert(High0:load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=DPtyped M(nil))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold EPbefore in Before;sep auto. }
 assert(Cache0:load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6)).
 { eapply V293_record_star_load_l with(s:=DPtyped M(nil))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold EPbefore in Before;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval CGge (emp:env) M 103%Z 108%Z 91%positive 94%positive
 4 6 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl High0 Cache0)as[Guard _].
 change(evalval(V293_OSSched_different 103%Z 108%Z)(CGge,(emp:env),M)=Some(Vint32 Int.one))in Guard.
 destruct(V293_owned_record_cell_update (95%positive,0%Z) Tint32(Vint32 Int.mone)(Vint32 Int.zero)
 _ _ _ _ _ _ _ _ eq_refl Owned)as(M1&Increment&Updated).
 destruct(V293_exit_boundary_tail DPprogram ks CGge (emp:env) M(fun _=>false)
 (false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None) _
 103%Z 108%Z 109%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z)
 91%positive 94%positive 95%positive 4 6 Int.mone
 ltac:(lia)ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 High0 Cache0 Owned)as(Mtail&Prefix&Inc2&After2&Outside2).
 rewrite Wrap in Inc2;change(store Tint32 M(95%positive,0%Z)(Vint32 Int.zero)=Some Mtail)in Inc2.
 assert(Mtail=M1)by congruence;subst Mtail.
 assert(After:DPtyped M1(nil)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 6).
 { unfold JHpost;clear Before Owned;sep auto. }
 assert(High:load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=DPtyped M1(nil))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold JHpost in After;clear Before Owned Updated;sep auto. }
 assert(Counter1:load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero)).
 { eapply V293_record_star_load_l with(s:=DPtyped M1(nil));
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Updated]. }
 assert(Raw:DPtyped M1(nil)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0))))).
 { unfold JHpost in After;clear Before Owned Updated;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive DPprogram ks
 CGge (emp:env) M1(fun _=>false)(false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting(V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) ** CGframe 0 0)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)eq_refl eq_refl eq_refl eq_refl Raw)as(Mc&Copy&Store&Copied&OutsideCopy).
 assert(OldCopy:DPtyped Mc(nil)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting ** JHpost 4).
 { unfold JHpost;clear Before Owned Updated After Raw;sep auto. }
 assert(TargetCopy:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with(s:=DPtyped Mc(nil))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold JHpost in OldCopy;clear -OldCopy;sep auto. }
 assert(SwitchOwned:DPtyped Mc nil|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue)).
 { unfold JHpost,CGframe,CGextra,V293_owned_record_cells,V293_owned_record_cell in OldCopy;
   clear -OldCopy;sep auto. }
 destruct(V293_ready_current_write 80%positive 81%positive 82%positive
 OwnershipWaiting OwnershipReady _ CGge(emp:env)Mc(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)1%positive V293_tcb_type SwitchOwned eq_refl)
 as(Msw&PhysicalStore&AfterSwitch&ReadCurrent&Frame).
 assert(Saved:(CGge,(emp:env),Msw,(fun _=>false),(false,nil,nil),SPOf,spec_done None)|=Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { unfold SPOf;clear -AfterSwitch;sep auto. }
 destruct(V293_cpu_release _ _ _ _ _ _ _ _ _ _ Saved)
 as(Mret&Free&Rest&Removed&Outside).
 exists M;exists M1;exists Mc;exists Msw;exists Mret.
 split;[exact TargetStore| ];split;[exact Guard| ];split;[exact Counter| ];split.
 - exact Increment.
 - split;[exact Counter1| ];split;[exact High| ];split;[exact Store| ];split;[exact TargetCopy| ];split;[exact PhysicalStore| ];
   split;[exact Saved| ];split;[exact Free| ];split;[exact Removed| ];split;[exact Outside| ].
   unfold XPbody,V293_exit_boundary_dispatch.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans;[exact Schedule| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_cstepstar_trans;[exact Prefix|exact Copy].
Qed.

Lemma DPcontext : InOS(SKIP,(kenil,HPpending))DPprogram.
Proof.
 exists SKIP;exists kenil;exists HPpending;split;[reflexivity| ].
 right;left;exists 113%Z;exists CGle;exists kstop;exists Tvoid;exists dnil.
 exists(dcons 120%Z Tint32 dnil);exists CGbody;exists CGbody;split;reflexivity.
Qed.

Lemma DPprefix_global : forall Mc cs ncs ip,
 cstepstar DPprogram(curs XPbody,(kenil,CGpending))(CGge,(emp:env),CEM)
 (curs(sprim(switch 106%Z)),(kenil,CGpending))(CGge,(emp:env),Mc) ->
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (DPtasks,RPstate CEM cs ncs,OwnershipWaiting)
 (RPtasks,RPstate Mc cs ncs,OwnershipWaiting).
Proof.
 intros Mc cs ncs ip Trace.
 pose proof(V293_csteps_global RCprogram CPpo CGempty ip _ _ _ _ Trace
 113%Z CGbody CGle kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 DPtasks RPenvs OwnershipWaiting(fun _=>false)(RPaux cs ncs)(false,nil,cs)HPcst
 eq_refl eq_refl I)as Lift.
 change(V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (set DPtasks OwnershipWaiting XPcode,
 (CGge,set RPenvs OwnershipWaiting emp,CEM,(fun _=>false),RPaux cs ncs),OwnershipWaiting)
 (set DPtasks OwnershipWaiting RPcode,
 (CGge,set RPenvs OwnershipWaiting emp,Mc,(fun _=>false),RPaux cs ncs),OwnershipWaiting))in Lift.
 assert(Envs:set RPenvs OwnershipWaiting emp=RPenvs).
 { apply CltEnvMod.get_set_same;reflexivity. }
 assert(Start:set DPtasks OwnershipWaiting XPcode=DPtasks).
 { apply TasksMod.get_set_same;reflexivity. }
 assert(End:set DPtasks OwnershipWaiting RPcode=RPtasks).
 { unfold DPtasks;rewrite tasks_set_a_set_a;apply TasksMod.get_set_same;reflexivity. }
 rewrite Envs,Start,End in Lift;exact Lift.
Qed.

(* This is the new independent endpoint: both whole-prefix execution and
   original simulation start BEFORE the scheduler call on the same heap. *)
Theorem DPactual_dispatch_and_resume : forall cs ncs ip,
 exists M M1 Mc Msw Mret,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 store Tint32 M(95%positive,0%Z)(Vint32 Int.zero)=Some M1 /\
 load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 free Tint32 98%positive Msw=Some Mret /\
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (DPtasks,RPstate CEM cs ncs,OwnershipWaiting)
 (RPfinal,RPreturned Mret cs ncs,OwnershipReady) /\
 ProgSim(RCprogram,(CPpo,CGempty,ip))DPtasks(RPstate CEM cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None) /\
 (forall b i,b<>98%positive ->get Mret(b,i)=get Msw(b,i)) /\
 get RPfinal OwnershipWaiting=Some(SKIP,(kenil,HPpending)) /\
 get(set RPenvs OwnershipReady emp)OwnershipWaiting=Some emp /\
 get(set(RPaux cs ncs)OwnershipReady(false,nil,ncs))OwnershipWaiting=Some(false,nil,cs).
Proof.
 intros cs ncs ip.
 destruct(DPdispatch_storage CGpending)as
 (M&M1&Mc&Msw&Mret&TargetStore&Guard&Counter&Increment&Counter1&High&Copy&Target&Store&Saved&Free&Removed&Frame&Trace).
 assert(SavedForReturn:(CGge,CGle,Msw,(fun _=>false),(false,nil,false::nil),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { eapply good_inv_prop;[cbn;split;exact I|exact Saved]. }
 exists M;exists M1;exists Mc;exists Msw;exists Mret.
 split;[exact TargetStore| ];split;[exact Counter| ];split;[exact Increment| ];split.
 - exact Counter1.
 - split;[exact Store| ];split;[exact Free| ];split.
   + eapply V293_global_trans;[eapply DPprefix_global;exact Trace| ].
     eapply RPfinite_switch_and_return;eassumption.
   + split.
     * unfold RPstate.
       eapply V293_exit_call_resume_progsim with(le:=(emp:env))(Mt:=M)(M1:=M1)(Mc:=Mc)(Mf:=Msw)
       (next:=OwnershipReady)(current:=108%Z)(counter:=109%Z)(ks:=HPpending)
       (f:=107%Z)(unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(high:=103%Z)(y:=104%Z)
       (table:=105%Z)(target:=106%Z)(bt:=92%positive)(bg:=81%positive)(br:=80%positive)
       (bh:=91%positive)(bp:=82%positive)(bo:=93%positive)(lo:=16)(hi:=0)(g:=1)
       (oldhigh:=Byte(Byte.repr 88))(value:=Vptr OwnershipReady)
       (bk:=95%positive)(count:=Int.mone)(b:=94%positive)(v:=V293_byteval 4)
       (bc:=1%positive)(tp:=V293_tcb_type)(si:=nil)(cs:=cs)(Thf:=HPThf)(Of:=SPOf)
       (exitf:=114%Z)(body:=CPfullbody)(caller:=emp)(tail:=kstop)
       (tau:=Tvoid)(d1:=dnil)(d2:=dcons 120%Z Tint32 dnil)
       (saved:=120%Z)(bs:=98%positive)(nsi:=nil)(ncs:=ncs)(Mret:=Mret);
       try reflexivity;try eassumption;try discriminate;try lia.
       -- exact(proj1 CFinput).
       -- exact(proj2 CFinput).
       -- exists 4;left;repeat split;try lia;reflexivity.
       -- change(4<13);lia.
       -- exact XPtable.
       -- exact DPcontext.
       -- eapply hp_stepS;[apply HPschedule|apply hp_stepO].
       -- unfold DPtasks;rewrite tasks_set_a_set_a.
          eapply SPterminal;[apply map_get_set| |unfold SPOf;apply map_get_set].
          unfold projS,projD;cbn;repeat rewrite map_get_set;reflexivity.
     * split;[exact Removed| ];split;[exact Frame| ];repeat split;
       unfold RPfinal,RPswitched,RPenvs,RPaux;
       rewrite map_get_set' by discriminate;apply map_get_set.
Qed.

(* Only remove the target store; keep CFfinal and the source program fixed.
   This control is NOT a proof of the following counter/copy/free steps. *)
Theorem DPtarget_store_and_omission : exists M,
 store(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)(Vptr OwnershipReady)=Some M /\
 load(Tptr V293_tcb_type)M(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 CFfinal(91%positive,0%Z)=Some(V293_byteval 4) /\
 load(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)=Some(Vptr OwnershipWaiting) /\
 ~load(Tptr V293_tcb_type)CFfinal(93%positive,0%Z)=Some(Vptr OwnershipReady).
Proof.
 destruct(DPscheduled_canonical kstop)as(M&Store&Trace&Owned).
 exists M;split;[exact Store| ];split.
 - eapply V293_store_readback;[reflexivity|exact Store].
 - exact XPomit_target_rejected.
Qed.
