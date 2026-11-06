(* Typed hook boundary on the SAME allocated endpoint from stage170.
   The external hook body is intentionally absent from CCprogram. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickHookContract.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.audit.probes.V293TimeTickCallContextProbe.
Require Import CertiOS.audit.probes.V293TimeTickPostHookCoreProbe.
Require Import CertiOS.audit.probes.V293TimeTickSwitchBoundaryProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileRecordsProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileSharedProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyChainProbe.
Require Import CertiOS.audit.probes.V293TimeTickReadyUpdateProbe.
Require Import CertiOS.audit.probes.V293TimeTickWhileCoreProbe.
Require Import CertiOS.audit.probes.V293TimeTickDelayHoareProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition HCresource clock run:=V293_tick_hook_resource
 WhileBindings WhileIdle Vnull WhileReady ChainEvents
 93%positive 92%positive 94%positive 96%positive 171%positive 172%positive
 98%positive 99%positive run CCrest clock(fun _=>false)[1][false].
Lemma HCgood : forall clock run,GoodFunAsrt(HCresource clock run).
Proof.
 intros;apply V293_tick_hook_resource_good.
 unfold CCrest;split.
 - unfold V293_owned_record_cell;cbn[GoodFunAsrt];split;exact I.
 - split;[exact I| ];split.
   + unfold LINV,V293_witness_li;cbn[GoodFunAsrt];split;exact I.
   + apply V293_inv_function_assertion;apply V293_owned_cells_good.
Qed.
Lemma HCcur : (CurTid WhileReady ** CCrest) ==> CurLINV V293_witness_li WhileReady.
Proof. unfold CCrest,CurLINV;intros s H;exists([]:list logicvar);clear -H;sep auto. Qed.
Lemma HClocal : forall clock run,HCresource clock run ==> CurLINV V293_witness_li WhileReady.
Proof. intros clock run s Held;eapply V293_tick_hook_resource_local;[exact HCcur|exact Held]. Qed.
Lemma HCfactor : forall clock run s,
 (s |= <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run) <->
 (s |= HCresource clock run ** CCbindings).
Proof. intros;apply V293_tick_hook_resource_factor. Qed.

Definition HCspec clock run:funspec:=fun f=>if Z.eq_dec f 2002%Z then
 Some(V293_tick_hook_fpre WhileReady(HCresource clock run)(HCgood clock run),
      V293_tick_hook_fpost WhileReady(HCresource clock run)(HCgood clock run),(Tvoid,[]))
 else None.
Theorem HCrules : forall sd r ri clock run,run<256 ->
 InfRules(HCspec clock run)sd V293_witness_li SCinv r ri
 (<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run)
 (sseq(scall 2002%Z[])(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z))
 (CCpost run)WhileReady.
Proof.
 intros sd r ri clock run Range.
 apply V293_tick_hook_then_suffix with(good:=HCgood clock run).
 - exact RUnoabs.
 - change(368+50<=4294967295)%Z;lia.
 - exact WhileBindingsValid.
 - exact WhileKeysUnique.
 - exact Range.
 - exact CCenv.
 - exact HCcur.
 - exact(proj1 CCframe_good).
 - exact(proj2 CCframe_good).
 - exact(proj1 CCframe_change).
 - exact(proj2 CCframe_change).
 - change(1<=INUM)%nat;unfold INUM;lia.
 - reflexivity.
 - reflexivity.
Qed.
Theorem HCsemantics : forall sd r ri clock run,run<256 ->
 simulation.RuleSem(HCspec clock run)sd V293_witness_li SCinv r ri
 (<||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCsuffix clock run)
 (sseq(scall 2002%Z[])(V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z))
 (CCpost run)WhileReady.
Proof. intros;apply RuleSound;apply HCrules;assumption. Qed.

(* Guard controls keep the resource fixed, varying ONLY one witness. *)
Lemma HCnil_required : forall clock run owner lg wrong s,
 wrong<>[] ->
 ~s |= getasrt(V293_tick_hook_fpre WhileReady(HCresource clock run)(HCgood clock run)wrong lg owner) ** Atrue.
Proof.
 intros clock run owner lg wrong s Nonempty Held;destruct s as[[[[[[ge le]M]ir]aux]O]op].
 cbn[V293_tick_hook_fpre getasrt]in Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Pre&Rest).
 apply sat_split in Pre;destruct Pre as(n1&n2&a1&a2&JN&JA&[Guard Empty]&Resource).
 destruct Guard as[Equal _];apply Nonempty;exact Equal.
Qed.
Lemma HCvoid_required : forall clock run owner lg vl v s,
 ~s |= getasrt(V293_tick_hook_fpost WhileReady(HCresource clock run)(HCgood clock run)vl(Some v)lg owner) ** Atrue.
Proof.
 intros clock run owner lg vl v s Held;destruct s as[[[[[[ge le]M]ir]aux]O]op].
 cbn[V293_tick_hook_fpost getasrt]in Held.
 apply sat_split in Held;destruct Held as(m1&m2&o1&o2&JM&JO&Pre&Rest).
 apply sat_split in Pre;destruct Pre as(n1&n2&a1&a2&JN&JA&[Guard Empty]&Resource).
 destruct Guard as[_[_[_ Equal]]];discriminate.
Qed.
Lemma HCcaller_not_fun : ~GoodFunAsrt CCbindings.
Proof. unfold CCbindings;cbn[GoodFunAsrt];tauto. Qed.

Theorem HCsame_endpoint : forall ks clock run,run<256 ->exists Ms,
 CCexecution ks clock run Ms /\
 CCstate Ms(PCabs clock)(PCcode run) |= HCresource clock run ** CCbindings /\
 load(Tptr V293_tcb_type)Ms(171%positive,0%Z)=Some Vundef /\
 load Tint32 Ms(172%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 load(Tptr V293_tcb_type)Ms(70%positive,0%Z)=Some(Vptr WhileIdle) /\
 ~ CCstate Ms(PCabs clock)(PCcode run) |=
  <||PCcode run||> ** OS[(fun _=>false),false,[1],[false]] ** CCbad_saved clock run.
Proof.
 intros ks clock run Range.
 destruct(CCsame_endpoint_controls ks clock run Range)as(Ms&Exec&Held&Scan&Saved&Canary&Old&Bad).
 exists Ms;split;[exact Exec| ];split;[apply(proj1(HCfactor clock run _));exact Held| ];
 split;[exact Scan| ];split;[exact Saved| ];split;[exact Canary| ];split;assumption.
Qed.

(* Concrete absence of a body prevents an actual return, even though HCspec
   above admits a conditional logical call derivation. *)
Theorem HCmissing_no_step : forall ks m ir au,
 ~exists C' state',loststep CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,ir,au)C' state'.
Proof. intros;apply V293_missing_port_has_no_step;reflexivity. Qed.
Theorem HCmissing_no_return : forall ks ks' m ir au state',
 ~V293_local_steps CCprogram(curs(sfexec 2002%Z[][]),(kenil,ks))(m,ir,au)
    (curs(sskip None),(kenil,ks'))state'.
Proof.
 intros ks ks' m ir au state' Run;unfold V293_local_steps in Run.
 inversion Run as [ | y z Step Rest];subst.
 destruct y as[C1 state1];cbn in Step.
 apply(HCmissing_no_step ks m ir au);exists C1;exists state1;exact Step.
Qed.

Lemma HCaccepted_guards : forall clock run s,
 s |= HCresource clock run ** CCbindings ->
 s |= getasrt(V293_tick_hook_fpre WhileReady(HCresource clock run)(HCgood clock run)[][]WhileReady) ** CCbindings /\
 s |= getasrt(V293_tick_hook_fpost WhileReady(HCresource clock run)(HCgood clock run)[]None[]WhileReady) ** CCbindings.
Proof.
 intros clock run s Held;split;cbn[V293_tick_hook_fpre V293_tick_hook_fpost getasrt];
 clear -Held;sep auto.
Qed.
Theorem HCsame_guard_controls : forall clock run s,
 s |= HCresource clock run ** CCbindings ->
 (s |= getasrt(V293_tick_hook_fpre WhileReady(HCresource clock run)(HCgood clock run)[][]WhileReady) ** CCbindings) /\
 (~s |= getasrt(V293_tick_hook_fpre WhileReady(HCresource clock run)(HCgood clock run)[Vint32 Int.zero][]WhileReady) ** CCbindings) /\
 (s |= getasrt(V293_tick_hook_fpost WhileReady(HCresource clock run)(HCgood clock run)[]None[]WhileReady) ** CCbindings) /\
 (~s |= getasrt(V293_tick_hook_fpost WhileReady(HCresource clock run)(HCgood clock run)[](Some(Vint32 Int.zero))[]WhileReady) ** CCbindings).
Proof.
 intros clock run s Held;destruct(HCaccepted_guards clock run s Held)as[Pre Post].
 split;[exact Pre| ];split.
 - intro Bad;apply(HCnil_required clock run WhileReady[][Vint32 Int.zero]s ltac:(discriminate)).
   eapply astar_mono;[intros st H;exact H|intros st H;exact I|exact Bad].
 - split;[exact Post| ];intro Bad.
   apply(HCvoid_required clock run WhileReady[][](Vint32 Int.zero)s).
   eapply astar_mono;[intros st H;exact H|intros st H;exact I|exact Bad].
Qed.
