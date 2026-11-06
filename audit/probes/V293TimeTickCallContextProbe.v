(* Genuine Vundef scan bytes; same existing invariant, not typed Vundef. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
(* Existing SWINV boundary, independent literal-byte entry; disabled/clear only. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
(* New joint byte heap: scan starts at idle, NOT the nonempty head. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.audit.probes.V293TimeTickChainOpenProbe.
(* Canonical entry is packed directly from literal bytes, not from the new opening. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
(* Independent four-task literal heap; original while and exact residuals. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyChain.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.



Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.

Definition CCle:=V293_tick_locals 901%Z 904%Z 171%positive 172%positive.
Definition CCstate M O op:RstateOP:=(PCge,CCle,M,(fun _=>false),(false,[1],[false]),O,op).
(* The former scan70 is CALLER-OWNED data, never the freshly allocated scan. *)
Definition CCrest:=V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) **
 (Atrue ** (LINV V293_witness_li WhileReady [] ** V293_owned_record_cells WhileFrameCells)).
Definition CCbindings:=Alvarenv 901%Z(Tptr V293_tcb_type)(171%positive,0%Z) //\\
 A_notin_lenv 902%Z //\\ Agvarenv 902%Z(Tarray Tint8 2)(93%positive,0%Z) //\\
 A_notin_lenv 903%Z //\\ Agvarenv 903%Z Tint8(92%positive,0%Z) //\\
 A_notin_lenv 1001%Z //\\ Agvarenv 1001%Z Tint32(96%positive,0%Z) //\\
 A_notin_lenv 1002%Z //\\ Agvarenv 1002%Z Tint8(98%positive,0%Z) //\\
 A_notin_lenv 1003%Z //\\ Agvarenv 1003%Z(Tptr V293_tcb_type)(99%positive,0%Z).
Definition CCframe:=CCbindings ** CCrest.
Definition CCbare clock run:=V293_tick_call_shared WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run CCrest clock.
Definition CCshared clock run:=V293_tick_call_shared WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run CCframe clock.
Definition CCpre clock run:=<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCshared clock run.
Definition CCsuffix clock run:=V293_tick_call_suffix WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 171%positive 172%positive 98%positive 99%positive run CCframe clock.
Definition CCpost run:=V293_tick_scan_switch_result WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 171%positive 98%positive 99%positive run
 (V293_tick_saved_frame 172%positive CCframe)Vundef(fun _=>false)[1][false].

Lemma CCstrip : forall clock run,SCcore clock run ==> CCbare clock run.
Proof.
 intros clock run s H.
 unfold SCcore,V293_tick_switch_pre,V293_tick_switch_supplement,
   CCbare,V293_tick_call_shared,CCrest,PCframe in *;clear -H;sep auto.
Qed.
Lemma CCbare_good_fun : forall clock run,GoodFunAsrt(CCbare clock run).
Proof.
 intros clock run;unfold CCbare,V293_tick_call_shared;split.
 - unfold V293_tick_switch_view;split.
   + exact(proj1(V293_sched_critical_good SCinv [] [])).
   + split;[unfold V293_shared_fields;cbn[GoodFunAsrt];repeat split;exact I|exact I].
 - split;[apply V293_inv_function_assertion;apply V293_owned_cells_good| ].
   split;[apply V293_inv_function_assertion;apply V293_owned_cells_good| ].
   unfold CCrest;split.
   + unfold V293_owned_record_cell;cbn[GoodFunAsrt];split;exact I.
   + split;[exact I| ];split.
     * unfold LINV,V293_witness_li;cbn[GoodFunAsrt];split;exact I.
     * apply V293_inv_function_assertion;apply V293_owned_cells_good.
Qed.
Lemma CCbindings_spatial : CCstate emp emp(END None) |= CCbindings.
Proof.
 unfold CCbindings;repeat split.
 - exists 171%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 93%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 92%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 96%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 98%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
 - intros[v E];vm_compute in E;discriminate.
 - exists 99%positive;split;[vm_compute;reflexivity| ];repeat split;reflexivity.
Qed.

Lemma CCentry : forall clock run,run<256 ->
 CCstate(PCmemory clock run)(PCabs clock)(PCcode run) |= CCpre clock run.
Proof.
 intros clock run Range.
 pose proof(SCpack clock run _ _ _(PCjoint clock run false(PCcode run)Range))as Old.
 apply CCstrip in Old.
 pose proof(good_fun_asrt_absop _ (CCbare_good_fun clock run) _ _ _ _ _ _ _ Old CCle)as New.
 assert(Bind:CCstate emp emp(PCcode run) |= CCbindings).
 { eapply goodfrm_prop;[unfold CCbindings;cbn[GoodFrm];repeat split;exact I|exact CCbindings_spatial]. }
 assert(Both:CCstate(PCmemory clock run)(PCabs clock)(PCcode run) |= CCbindings ** CCbare clock run).
 { apply sat_split';exists(empmem:mem);exists(PCmemory clock run);exists(emp:osabst);exists(PCabs clock).
   split;[apply map_join_comm;apply map_join_emp| ];split;[apply map_join_comm;apply map_join_emp| ];split;assumption. }
 assert(Core:CCstate(PCmemory clock run)(PCabs clock)(PCcode run) |= CCshared clock run).
 { unfold CCbare,CCshared,V293_tick_call_shared,CCframe in *;clear -Both;sep auto. }
 assert(Control:CCstate(PCmemory clock run)(PCabs clock)(PCcode run) |=
   Aisr(fun _=>false) ** (Aie false ** (Ais ([1]) ** (Acs ([false]) ** CCshared clock run)))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact Core|reflexivity]. }
 unfold CCpre;apply astar_l_aop'_intro;[ |reflexivity];clear -Control;sep auto.
Qed.
Lemma CCfresh : forall clock run b,b=171%positive \/ b=172%positive ->fresh(PCmemory clock run)b.
Proof.
 intros clock run b Cases l i E [v Bound];subst l.
 assert(Outside:get(PCmemory clock run)(b,i)=None).
 { unfold PCmemory;rewrite map_merge_semp by reflexivity.
   rewrite OwnershipCellsOutside;[ |destruct Cases;subst b;vm_compute;intuition congruence].
   unfold WCcurrent;rewrite V293_encoded_memory_outside;[reflexivity|destruct Cases;subst b;left;discriminate]. }
 change(get(PCmemory clock run)(b,i)=Some v)in Bound.
 rewrite Outside in Bound;discriminate.
Qed.
Lemma CCfresh_saved : forall clock run,
 fresh(allocb(PCmemory clock run)171%positive 0%Z(typelen(Tptr V293_tcb_type)))172%positive.
Proof.
 intros clock run l i E [v Bound];subst l.
 change(get(allocb(PCmemory clock run)171%positive 0%Z(typelen(Tptr V293_tcb_type)))(172%positive,i)=Some v)in Bound.
 rewrite V293_success_allocb_outside in Bound by(left;discriminate).
 pose proof(CCfresh clock run 172%positive(or_intror eq_refl))as Fresh.
 apply(Fresh (172%positive,i) i eq_refl);exists v;exact Bound.
Qed.
Definition CCprogram:progunit:=fun f=>if Z.eq_dec f 2001%Z then
 Some(V293_tick_function 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z) else None.
Definition CCexecution ks clock run Ms:=V293_local_steps CCprogram
 (curs(scall 2001%Z nil),(kenil,ks))((PCge,emp,PCmemory clock run),(fun _=>false),(false,[1],[false]))
 (curs(scall 2002%Z nil),(kenil,
  kseq(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
   (kseq sret(kcall 2001%Z(sseq(V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)sret)emp ks))))
 ((PCge,CCle,Ms),(fun _=>false),(false,[1],[false])).
Theorem CCallocated_entry : forall ks clock run,run<256 ->exists Ms,
 CCexecution ks clock run Ms /\
 load(Tptr V293_tcb_type)Ms(171%positive,0%Z)=Some Vundef /\
 load Tint32 Ms(172%positive,0%Z)=Some(Vint32 Int.zero) /\
 CCstate Ms(PCabs clock)(PCcode run) |=
  <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run.
Proof.
 intros ks clock run Range.
 apply(V293_tick_call_shared_to_hook WhileBindings WhileIdle Vnull WhileReady ChainEvents
  93%positive 92%positive 94%positive 96%positive 171%positive 172%positive 98%positive 99%positive run CCframe
  CCprogram ks PCge emp(PCmemory clock run)(fun _=>false)[1][false](PCabs clock)clock
  2001%Z 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z).
 - reflexivity.
 - discriminate.
 - apply CCfresh;left;reflexivity.
 - apply CCfresh_saved.
 - apply CCentry;exact Range.
Qed.

Lemma CCframe_good : GoodFrm CCframe.
Proof.
 unfold CCframe,CCbindings,CCrest,V293_owned_record_cell,LINV,V293_witness_li;
 cbn[GoodFrm];repeat split;try exact I;apply V293_tick_cells_frame.
Qed.
Lemma CCframe_change : can_change_aop CCframe.
Proof.
 unfold CCframe,CCbindings,CCrest,V293_owned_record_cell,LINV,V293_witness_li;
 cbn[can_change_aop];repeat split;try exact I;
 apply V293_tick_update_change;apply V293_owned_cells_good.
Qed.
Lemma CCenv : forall st,st |= CCframe -> V293_tick_post_env 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
 171%positive 93%positive 92%positive 96%positive 98%positive 99%positive(getgenv st)(getlenv st).
Proof.
 intros st Held;eapply V293_star_env_l;[ |exact Held].
 intros s(Bc&Nr&Gr&Ng&Gg&Nn&Gn&Nu&Gu&Nh&Gh).
 destruct Bc as[b[B[E _]]];inversion E;subst b.
 destruct Gr as[br[R[Er _]]];inversion Er;subst br.
 destruct Gg as[bg[G[Eg _]]];inversion Eg;subst bg.
 destruct Gn as[bn[Gn[En _]]];inversion En;subst bn.
 destruct Gu as[bu[Gu[Eu _]]];inversion Eu;subst bu.
 destruct Gh as[bh[Gh[Eh _]]];inversion Eh;subst bh.
 destruct Nr as[Nr _];destruct Ng as[Ng _].
 destruct Nn as[Nn _];destruct Nu as[Nu _];destruct Nh as[Nh _].
 unfold V293_tick_post_env,V293_tick_delay_env;repeat split;try assumption;
 match goal with
 | N:~indom ?le ?x |- get ?le ?x=None =>
   destruct(get le x)eqn:V;[exfalso;apply N;eexists;exact V|exact V]
 end.
Qed.
Lemma CCcur : (CurTid WhileReady ** CCframe) ==> CurLINV V293_witness_li WhileReady.
Proof. unfold CCframe,CCrest,CurLINV;intros s H;exists([]:list logicvar);clear -H;sep auto. Qed.
Theorem CCrules : forall Spec sd r ri clock run,run<256 ->
 InfRules Spec sd V293_witness_li SCinv r ri
  (<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(CCpost run)WhileReady.
Proof.
 intros;apply V293_tick_call_suffix_hoare.
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - assumption.
 - exact CCenv.
 - exact CCcur.
 - exact CCframe_good.
 - exact CCframe_change.
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
Qed.
Theorem CCsemantics : forall Spec sd r ri clock run,run<256 ->
 simulation.RuleSem Spec sd V293_witness_li SCinv r ri
  (<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run)
  (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)(CCpost run)WhileReady.
Proof. intros;apply RuleSound;apply CCrules;assumption. Qed.
Theorem CCrunning : forall ks clock,exists Ms,
 CCexecution ks clock 1 Ms /\
 CCstate Ms(PCabs clock)(PCcode 1) |=
  <||PCcode 1||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock 1.
Proof.
 intros;destruct(CCallocated_entry ks clock 1 ltac:(lia))as(Ms&Exec&Scan&Saved&Held).
 exists Ms;split;assumption.
Qed.
Theorem CCstopped : forall ks clock run,run=0 \/ run=255 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(PCcode run) |=
  <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run.
Proof.
 intros ks clock run Case;destruct(CCallocated_entry ks clock run ltac:(lia))as(Ms&Exec&Scan&Saved&Held).
 exists Ms;split;assumption.
Qed.
Theorem CCwrap : forall ks,exists Ms,
 CCexecution ks(Int.repr 4294967295)1 Ms /\
 CCstate Ms(PCabs(Int.repr 4294967295))(PCcode 1) |=
  <||PCcode 1||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix(Int.repr 4294967295)1.
Proof. intros;apply CCrunning. Qed.

Definition CCbad_saved clock run:=V293_tick_scan_switch_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 171%positive 98%positive 99%positive run
 (V293_owned_record_cell((172%positive,0%Z),Tint32,Vint32 Int.one) ** CCframe)clock Vundef.
Lemma CCwrong_saved : forall clock run M O op,
 load Tint32 M(172%positive,0%Z)=Some(Vint32 Int.zero) ->
 ~ CCstate M O op |= <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCbad_saved clock run.
Proof.
 intros clock run M O op Zero Held.
 assert(Slot:CCstate M O op |= V293_owned_record_cell((172%positive,0%Z),Tint32,Vint32 Int.one) ** Atrue).
 { unfold CCbad_saved,V293_tick_scan_switch_pre,V293_tick_scan_supplement in Held;clear -Held;sep auto. }
 assert(Read:load Tint32 M(172%positive,0%Z)=Some(Vint32 Int.one)).
 { change(load Tint32(getmem(CCstate M O op))(172%positive,0%Z)=Some(Vint32 Int.one)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Slot]. }
 rewrite Zero in Read;vm_compute in Read;discriminate.
Qed.
Lemma CCwrong_env : forall M O op,
 ~ CCstate M O op |= Alvarenv 901%Z(Tptr V293_tcb_type)(70%positive,0%Z) ** Atrue.
Proof.
 intros M O op Held;apply sat_split in Held.
 destruct Held as(m1&m2&o1&o2&JM&JO&[b[B[E Empty]]]&Rest).
 change(get CCle 901%Z=Some(b,Tptr V293_tcb_type))in B.
 vm_compute in B;inversion B;subst b;vm_compute in E;discriminate.
Qed.
Lemma CCcaller_cells : forall clock run M O op,
 CCstate M O op |= <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run ->
 load Tint32 M(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)M(70%positive,0%Z)=Some(Vptr WhileIdle).
Proof.
 intros clock run M O op Held.
 assert(Cells:CCstate M O op |=
  V293_owned_record_cells WhileFrameCells ** Atrue).
 { unfold CCsuffix,V293_tick_call_suffix,V293_tick_scan_switch_pre,V293_tick_scan_supplement,
   V293_tick_saved_frame,CCframe,CCrest in Held;clear -Held;sep auto. }
 split.
 - change(load Tint32(getmem(CCstate M O op))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Cells].
   intros st H;eapply V293_owned_record_cells_load with(cells:=WhileFrameCells);
   [unfold WhileFrameCells;left;reflexivity|exact H].
 - assert(Slot:CCstate M O op |= V293_owned_record_cell(V293_tick_pointer_cell 70%positive WhileIdle) ** Atrue).
   { unfold CCsuffix,V293_tick_call_suffix,V293_tick_scan_switch_pre,V293_tick_scan_supplement,
     V293_tick_saved_frame,CCframe,CCrest in Held;clear -Held;sep auto. }
   change(load(Tptr V293_tcb_type)(getmem(CCstate M O op))(70%positive,0%Z)=Some(Vptr WhileIdle)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Slot].
Qed.
Theorem CCsame_endpoint_controls : forall ks clock run,run<256 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(PCcode run) |=
  <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run /\
 load(Tptr V293_tcb_type)Ms(171%positive,0%Z)=Some Vundef /\
 load Tint32 Ms(172%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)Ms(70%positive,0%Z)=Some(Vptr WhileIdle) /\
 ~ CCstate Ms(PCabs clock)(PCcode run) |=
  <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCbad_saved clock run.
Proof.
 intros ks clock run Range.
 destruct(CCallocated_entry ks clock run Range)as(Ms&Exec&Scan&Saved&Held).
 destruct(CCcaller_cells clock run Ms(PCabs clock)(PCcode run)Held)as[Canary OldSlot].
 exists Ms;split;[exact Exec| ];split;[exact Held| ];split;[exact Scan| ];split;[exact Saved| ];
 split;[exact Canary| ];split;[exact OldSlot| ];apply CCwrong_saved;exact Saved.
Qed.
