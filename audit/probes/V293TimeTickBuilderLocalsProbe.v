(* Independent builder fixtures; the original CPU hook remains absent. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickHookContractProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickShared.
Require Import CertiOS.audit.probes.V293TimeTickChainOpenProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.framework.proof.soundness.
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
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBodyHoare.
Require Import CertiOS.audit.probes.V293TimeTickReturnTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.audit.probes.V293TimeTickBodyHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickBuilderLocals.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickHookContract.
Import ListNotations.
Local Open Scope nat_scope.
Definition BLglobals:=Agvarenv 902%Z(Tarray Tint8 2)(93%positive,0%Z) //\\
 Agvarenv 903%Z Tint8(92%positive,0%Z) //\\
 Agvarenv 1001%Z Tint32(96%positive,0%Z) //\\
 Agvarenv 1002%Z Tint8(98%positive,0%Z) //\\
 Agvarenv 1003%Z(Tptr V293_tcb_type)(99%positive,0%Z).
Definition BLrest:=BLglobals ** CCrest.
Definition BLresource clock run:=V293_tick_builder_resource WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest clock(fun _=>false)[1][false].
Definition BLentry old scan clock run:=V293_tick_builder_entry WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 171%positive 172%positive 904%Z (V293_tick_builder_caller 901%Z 904%Z 171%positive)
 old scan clock(fun _=>false)[1][false].
Definition BLpre clock run:=V293_tick_builder_pre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 901%Z 904%Z clock(fun _=>false)[1][false].
Definition BLpost run:=V293_tick_builder_post WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 901%Z 904%Z(fun _=>false)[1][false].
Lemma BLrest_good : GoodFunAsrt BLrest.
Proof. unfold BLrest,BLglobals;split;[cbn[GoodFunAsrt];repeat split;exact I|exact TRrest_good]. Qed.
Lemma BLgood : forall clock run,GoodFunAsrt(BLresource clock run).
Proof. intros;apply V293_tick_builder_resource_good;exact BLrest_good. Qed.
Definition BLfpre clock run:=V293_tick_builder_fpre WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 clock(fun _=>false)[1][false](BLgood clock run).
Definition BLfpost run:=V293_tick_builder_fpost WhileBindings WhileIdle
 93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run BLrest
 (fun _=>false)[1][false] BLrest_good.
Definition BLspec clock run:funspec:=fun f=>if Z.eq_dec f 2002%Z then
 Some(V293_tick_hook_fpre WhileReady(BLresource clock run)(BLgood clock run),
 V293_tick_hook_fpost WhileReady(BLresource clock run)(BLgood clock run),(Tvoid,[]))else None.

Lemma BLdomain : eq_dom_env CCle
 (cons(901%Z,Tptr V293_tcb_type)(cons(904%Z,Tint32)nil)).
Proof.
 unfold CCle,V293_tick_locals,eq_dom_env;intros x t.
 destruct(Z.eq_dec x 904%Z)as[E|Other].
 - subst x;rewrite map_get_set;cbn;split.
   + intros[Bad|[E|Bad]];try discriminate;try contradiction;inversion E;subst t;eexists;reflexivity.
   + intros[b E];inversion E;right;left;reflexivity.
 - destruct(Z.eq_dec x 901%Z)as[E|Other2].
   + subst x;rewrite map_get_set' by discriminate;rewrite map_get_set;cbn;split.
     * intros[E|[Bad|Bad]];try discriminate;try contradiction;inversion E;subst t;eexists;reflexivity.
     * intros[b E];inversion E;left;reflexivity.
   + rewrite map_get_set' by congruence;rewrite map_get_set' by congruence;rewrite map_emp_get;cbn;split.
     * intros[E|[F|Bad]];[inversion E;congruence|inversion F;congruence|contradiction].
     * intros[b E];discriminate.
Qed.
Lemma BLadd_domain : forall M O op p,
 CCstate M O op |= p -> CCstate M O op |= V293_tick_builder_domain 901%Z 904%Z ** p.
Proof. intros;apply astar_l_adomlenv_intro;[exact H|exact BLdomain]. Qed.
Lemma BLbindings_split : CCbindings ==>
 Alvarenv 901%Z(Tptr V293_tcb_type)(171%positive,0%Z) ** BLglobals.
Proof.
 intros s(Bc&Nr&Gr&Ng&Gg&Nn&Gn&Nu&Gu&Nh&Gh).
 pose proof Bc as El;apply alvarenv_elim in El;destruct El as[[Zero Env]Empty].
 apply astar_l_alvarenv_intro;[unfold BLglobals;repeat split;assumption|split;[reflexivity|exact Env]].
Qed.
Lemma BLallocated : forall clock run,run<256 ->
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BLentry Vundef Vundef clock run /\
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BLpre clock run.
Proof.
 intros clock run Range;pose proof(BHallocated_entry clock run Range)as H.
 apply BLadd_domain in H.
 assert(K:CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= CCbindings **
  (V293_tick_builder_domain 901%Z 904%Z **
   (<||PCcode run||> ** V293_time_cell true 904%Z 172%positive Vundef **
    OS[(fun _=>false),false,[1],[false]] **
    (Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef ** CCbare clock run)))).
 { unfold BHentry,V293_tick_body_entry,V293_tick_call_shared,CCbare,CCframe in *;clear -H;sep auto. }
 eapply astar_mono in K.
 2:{ apply BLbindings_split. }
 2:{ intros s Hs;exact Hs. }
 unfold BLentry,BLpre,V293_tick_builder_pre,V293_tick_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
 V293_tick_builder_entry,V293_tick_builder_caller,V293_tick_builder_resource,BLresource,
 BLrest,CCbare,V293_tick_call_shared,V293_time_cell,V293_time_binding in *;split;clear -K;sep auto.
Qed.
Lemma BLscan_load : forall old scan clock run M,
 (scan=Vundef \/exists a,scan=Vptr a) ->
 CCstate M(PCabs clock)(PCcode run) |= BLentry old scan clock run ->
 load(Tptr V293_tcb_type)M(171%positive,0%Z)=Some scan.
Proof.
 intros old scan clock run M Values Held.
 assert(Slot:CCstate M(PCabs clock)(PCcode run) |=
 Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true scan ** Atrue).
 { unfold BLentry,V293_tick_builder_entry in Held;clear -Held;sep auto. }
 change(load(Tptr V293_tcb_type)(getmem(CCstate M(PCabs clock)(PCcode run)))(171%positive,0%Z)=Some scan).
 eapply V293_record_star_load_l;[ |exact Slot].
 intros st H;apply V293_tick_raw_pointer_load;assumption.
Qed.
Theorem BLsame_allocated_controls : forall clock run,run<256 ->
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BLpre clock run /\
 CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BLentry Vundef Vundef clock run /\
 ~CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |= BLentry Vundef(Vptr WhileIdle)clock run.
Proof.
 intros clock run Range;destruct(BLallocated clock run Range)as[Entry Pre].
 split;[exact Pre| ];split;[exact Entry| ];intro Bad.
 pose proof(BLscan_load _ _ _ _ _ (or_introl eq_refl)Entry)as Read.
 pose proof(BLscan_load _ _ _ _ _ (or_intror(ex_intro _ WhileIdle eq_refl))Bad)as Wrong;congruence.
Qed.

(* Only this independent fixture changes scan. This is not C initialization. *)
Theorem BLarbitrary_scan_nonvacuous : forall clock run,run<256 ->exists Ms,
 store(Tptr V293_tcb_type)(BHmemory clock run)(171%positive,0%Z)(Vptr WhileIdle)=Some Ms /\
 CCstate Ms(PCabs clock)(PCcode run) |= BLentry Vundef(Vptr WhileIdle)clock run /\
 CCstate Ms(PCabs clock)(PCcode run) |= BLpre clock run /\
 ~CCstate Ms(PCabs clock)(PCcode run) |= BHentry Vundef clock run.
Proof.
 intros clock run Range;destruct(BLallocated clock run Range)as[Entry Pre].
 assert(Raw:CCstate(BHmemory clock run)(PCabs clock)(PCcode run) |=
 Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef **
 (<||PCcode run||> ** V293_time_cell true 904%Z 172%positive Vundef **
  OS[(fun _=>false),false,[1],[false]] **
  V293_tick_call_shared WhileBindings WhileIdle Vnull WhileReady ChainEvents
   93%positive 92%positive 94%positive 96%positive 98%positive 99%positive run
   (V293_tick_builder_caller 901%Z 904%Z 171%positive ** BLrest)clock)).
 { unfold BLentry,V293_tick_builder_entry in Entry;clear -Entry;sep auto. }
 destruct(V293_tick_raw_slot_update (171%positive,0%Z) (Tptr V293_tcb_type) Vundef (Vptr WhileIdle)_ _ _ _ _ _ _ _ eq_refl Raw)
  as(Ms&Store&Owned).
 assert(New:CCstate Ms(PCabs clock)(PCcode run) |= BLentry Vundef(Vptr WhileIdle)clock run).
 { unfold BLentry,V293_tick_builder_entry,V293_owned_record_cell in *;clear -Owned;sep auto. }
 exists Ms;split;[exact Store| ];split;[exact New| ];split.
 - unfold BLpre,V293_tick_builder_pre,V293_tick_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
   V293_tick_builder_resource,BLentry,V293_tick_builder_entry,V293_tick_builder_caller,
   V293_time_cell,V293_time_binding,V293_tick_call_shared in *;clear -New;sep auto.
 - intro Bad.
   pose proof(BLscan_load _ _ _ _ _ (or_intror(ex_intro _ WhileIdle eq_refl))New)as Read.
   assert(Slot:CCstate Ms(PCabs clock)(PCcode run) |=
    Amapsto(171%positive,0%Z)(Tptr V293_tcb_type)true Vundef ** Atrue).
   { unfold BHentry,V293_tick_body_entry in Bad;clear -Bad;sep auto. }
   assert(Wrong:load(Tptr V293_tcb_type)Ms(171%positive,0%Z)=Some Vundef).
   { change(load(Tptr V293_tcb_type)(getmem(CCstate Ms(PCabs clock)(PCcode run)))(171%positive,0%Z)=Some Vundef).
     eapply V293_record_star_load_l;[ |exact Slot].
     intros st H;apply V293_tick_raw_pointer_load;[left;reflexivity|exact H]. }
   congruence.
Qed.

Lemma BLnot_shadow : forall le x,
 x<>901%Z ->x<>904%Z ->
 eq_dom_env le(cons(901%Z,Tptr V293_tcb_type)(cons(904%Z,Tint32)nil)) ->get le x=None.
Proof.
 intros le x A B Dom;destruct(get le x)as[[b t]| ]eqn:E;[ |reflexivity].
 exfalso;pose proof(proj2(Dom x t)(ex_intro _ b E))as Member.
 destruct Member as[E1|[E2|Bad]];[inversion E1;congruence|inversion E2;congruence|contradiction].
Qed.
Lemma BLenv : forall bc st,
 st |= V293_tick_builder_caller 901%Z 904%Z bc ** BLrest ->
 V293_tick_post_env 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z
 bc 93%positive 92%positive 96%positive 98%positive 99%positive(getgenv st)(getlenv st).
Proof.
 intros bc st H.
 assert(K:st |= ((Alvarenv 901%Z(Tptr V293_tcb_type)(bc,0%Z) ** BLglobals) **
  V293_tick_builder_domain 901%Z 904%Z) ** CCrest).
 { unfold V293_tick_builder_caller,BLrest in H;clear -H;sep auto. }
 eapply V293_star_env_l;[ |exact K].
 intros s Held;apply astar_comm in Held;apply astar_l_adomlenv_elim in Held.
 destruct Held as[Dom Held].
 assert(B:get(getlenv s)901%Z=Some(bc,Tptr V293_tcb_type)).
 { eapply V293_star_env_l with(E:=fun ge le=>get le 901%Z=Some(bc,Tptr V293_tcb_type));[ |exact Held].
   intros cellst Bind;apply alvarenv_elim in Bind;exact(proj2(proj1 Bind)). }
 assert(G:get(getgenv s)902%Z=Some(93%positive,Tarray Tint8 2) /\
  get(getgenv s)903%Z=Some(92%positive,Tint8) /\
  get(getgenv s)1001%Z=Some(96%positive,Tint32) /\
  get(getgenv s)1002%Z=Some(98%positive,Tint8) /\
  get(getgenv s)1003%Z=Some(99%positive,Tptr V293_tcb_type)).
 { eapply V293_star_env_r with(E:=fun ge le=>
   get ge 902%Z=Some(93%positive,Tarray Tint8 2) /\ get ge 903%Z=Some(92%positive,Tint8) /\
   get ge 1001%Z=Some(96%positive,Tint32) /\ get ge 1002%Z=Some(98%positive,Tint8) /\
   get ge 1003%Z=Some(99%positive,Tptr V293_tcb_type));[ |exact Held].
   intros cellst(Gr&Gg&Gn&Gu&Gh).
   apply agvarenv_elim in Gr;apply agvarenv_elim in Gg;apply agvarenv_elim in Gn;
   apply agvarenv_elim in Gu;apply agvarenv_elim in Gh.
   repeat split;[exact(proj2(proj1 Gr))|exact(proj2(proj1 Gg))|exact(proj2(proj1 Gn))|
    exact(proj2(proj1 Gu))|exact(proj2(proj1 Gh))]. }
 destruct G as[Gr[Gg[Gn[Gu Gh]]]].
 unfold V293_tick_post_env,V293_tick_delay_env;repeat split;try assumption;
 apply BLnot_shadow;try discriminate;exact Dom.
Qed.
Lemma BLcur : (CurTid WhileReady ** BLrest) ==> CurLINV V293_witness_li WhileReady.
Proof. unfold BLrest,CCrest,CurLINV;intros s H;exists([]:list logicvar);clear -H;sep auto. Qed.
Lemma BLframe : GoodFrm BLrest /\ can_change_aop BLrest.
Proof.
 unfold BLrest,BLglobals;split;split;try(cbn[GoodFrm can_change_aop];repeat split;exact I).
Qed.
Theorem BLbuilders : forall clock run lg,
 Some(BLpre clock run)=BuildPreI CCprogram 2001%Z[]lg(BLfpre clock run)WhileReady /\
 Some(BLpost run)=BuildRetI CCprogram 2001%Z[]lg(BLfpost run)WhileReady.
Proof. intros;split;reflexivity. Qed.
Theorem BLcontract : forall sd clock run vl lg pre post,run<256 ->
 Some pre=BuildPreI CCprogram 2001%Z vl lg(BLfpre clock run)WhileReady ->
 Some post=BuildRetI CCprogram 2001%Z vl lg(BLfpost run)WhileReady ->
 InfRules(BLspec clock run)sd V293_witness_li SCinv post Afalse pre BHbody Afalse WhileReady.
Proof.
 intros sd clock run vl lg pre post Range Pre Post.
 eapply V293_tick_builder_internal_contract with(good:=BLgood clock run)(Good:=BLrest_good);
 try exact Pre;try exact Post.
 - discriminate.
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact Range.
 - exact BLenv.
 - exact BLcur.
 - exact(proj1 BLframe).
 - exact(proj2 BLframe).
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Theorem BLsemantics : forall sd clock run (lg:list logicvar),run<256 ->
 simulation.RuleSem(BLspec clock run)sd V293_witness_li SCinv(BLpost run)Afalse
 (BLpre clock run)BHbody Afalse WhileReady.
Proof.
 intros;apply RuleSound;eapply BLcontract;[exact H|exact(proj1(BLbuilders clock run lg))|
 exact(proj2(BLbuilders clock run lg))].
Qed.
Theorem BLwrong_return : forall run v s,~s |= BLpost run(Some v).
Proof.
 intros run v s Held;unfold BLpost,V293_tick_builder_post in Held.
 assert(K:s |= [|Some v=None|] ** Atrue)by(clear -Held;sep auto).
 apply astar_l_apure_elim in K;destruct K as[Bad _];discriminate.
Qed.

(* A separate stopped full BuildRetI witness, not a complete tick execution. *)
Theorem BLstopped_return_nonvacuous : forall ks clock run,run<256 ->run<>1 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(END None) |= BLpost run None /\
 ~CCstate Ms(PCabs clock)(END None) |= BLpost run(Some(Vint32 Int.zero)).
Proof.
 intros ks clock run Range Stopped.
 destruct(BHstopped_return_fixture ks clock run Range Stopped)as(Ms&Prefix&Post&Bad).
 apply BLadd_domain in Post.
 assert(K:CCstate Ms(PCabs clock)(END None) |= CCbindings **
  (V293_tick_builder_domain 901%Z 904%Z **
  V293_tick_scan_switch_result WhileBindings WhileIdle 93%positive 92%positive 94%positive 96%positive
  171%positive 98%positive 99%positive run(V293_tick_saved_frame 172%positive(BHbind ** CCrest))
  Vundef(fun _=>false)[1][false])).
 { unfold BHreturn,V293_tick_body_return,V293_tick_scan_switch_result in *.
   assert(Off:Nat.eqb run 1=false)by(apply Nat.eqb_neq;exact Stopped);rewrite Off in *.
   unfold V293_tick_scan_supplement,V293_tick_saved_frame,BHbind,CCframe in *;clear -Post;sep auto. }
 eapply astar_mono in K;[ |apply BLbindings_split|intros s H;exact H].
 assert(Full:CCstate Ms(PCabs clock)(END None) |= BLpost run None).
 { unfold BLpost,V293_tick_builder_post,V293_tick_builder_cells,Alvarmapsto,Alvarenv',Aptrmapsto,
   V293_tick_return_resources,V293_tick_scan_switch_result in *.
   assert(Off:Nat.eqb run 1=false)by(apply Nat.eqb_neq;exact Stopped);rewrite Off in *.
   unfold V293_tick_scan_supplement,V293_tick_saved_frame,V293_owned_record_cell,
    BLrest,BHbind,V293_time_binding in *;clear -K;sep auto. }
 exists Ms;split;[exact Prefix| ];split;[exact Full|apply BLwrong_return].
Qed.
Theorem BLmissing_hook_still_blocked : forall ks m ir au,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,ir,au)C' state'.
Proof. apply HCmissing_no_step. Qed.
