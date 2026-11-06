(* One existential pool and one caller for every nesting byte. Test-only
   empty LINV; no reachability claim for ISR nesting with all flags clear. *)
Require Import CertiOS.audit.probes.V293TaskCreateEnabledRejectProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateDynamicReject.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
(* Enabled-IE literal minimal early-exit fixtures: original 12 declarations, distinct byte
   ownership. Independent of success/empty TCB fixtures; empty LINV is test-only.
   Controls concern the actual critical-exit primitive and saved IE, not full function traces. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DRCore := V293_create_reject_pool 502%positive 501%positive 11 Aemp.
Definition DRStorage :=
 V293_storage_cell(501%positive,0%Z)Tint8 **
 V293_storage_cell(502%positive,44%Z)(Tptr V293_tcb_type) **
 (V293_create_rejection_globals V293_create_occupied_priority 502%positive 501%positive ** Aemp).
Lemma DRTypedCell : forall a tp v,
 rule_type_val_match tp v=true -> Amapsto a tp true v ==> V293_storage_cell a tp.
Proof. intros a tp v Typed s H. exists v. sep auto. Qed.
Lemma DRCoreStorage : DRCore ==> DRStorage.
Proof.
 intros s H. unfold DRCore,V293_create_reject_pool in H.
 destruct H as[n[slot H]]. apply astar_l_apure_elim in H. destruct H as[Range H].
 unfold V293_create_dynamic_owned,V293_create_dynamic_cells in H. cbn[V293_rdy_raw_cells]in H.
 unfold DRStorage.
 eapply astar_mono;[apply DRTypedCell;apply V293_byte_type;exact Range| |exact H].
 eapply astar_mono;[apply DRTypedCell;reflexivity|intros st HS;exact HS].
Qed.
Lemma DRCorePrecise : precise DRCore.
Proof.
 assert(P:precise DRStorage).
 { unfold DRStorage. apply precise_star;[apply V293_storage_cell_precise| ].
   apply precise_star;[apply V293_storage_cell_precise| ].
   apply precise_star;[apply ERGlobalsPrecise|apply EREmptyPrecise;intros [[[[[[ge le] M] ir] aux] O] op] H;exact H]. }
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 eapply P;[apply DRCoreStorage;exact H1|apply DRCoreStorage;exact H2|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma DRCoreGood : GoodInvAsrt DRCore.
Proof.
 cbn[DRCore V293_create_reject_pool V293_create_dynamic_owned V293_create_dynamic_cells
 V293_create_rejection_globals V293_rdy_raw_cells GoodInvAsrt]. repeat split;exact I.
Qed.
Lemma DRCoreISR : assertion.inv_isr_prop DRCore.
Proof.
 unfold assertion.inv_isr_prop,DRCore,V293_create_reject_pool,V293_create_dynamic_owned,
 V293_create_dynamic_cells. cbn[V293_create_rejection_globals V293_rdy_raw_cells].
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition DRInv : Inv := fun i=>match i with
 | O=>mkinvasrt DRCoreGood(conj DRCorePrecise DRCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma DRNoisrTail : forall n i,starinv_noisr DRInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr DRInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma DRNoisrCore : forall n,starinv_noisr DRInv 0 n <==> DRCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= DRCore ** starinv_noisr DRInv 1 n <-> s |= DRCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply DRNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply DRNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem DRBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr DRInv 0 n <==> Aisr(fun _=>false) ** DRCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply DRNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply DRNoisrCore;exact H2.
Qed.

Definition DRExtra n := merge(RIByte 501%positive Tint8(V293_byteval n))
 (V293_encoded_memory 502%positive 44%Z true(encode_val(Tptr V293_tcb_type)(Vptr RISlot))).
Definition DRWhole n := merge(RIMemory V293_create_occupied_priority)(DRExtra n).
Theorem DRExtraSpatial : forall n,
 RIState(DRExtra n) |= V293_create_dynamic_owned 502%positive 501%positive 11 n RISlot Aemp.
Proof.
 intro n. unfold V293_create_dynamic_owned,V293_create_dynamic_cells.
 apply V293_raw_cells_join. eapply RIStar with(m1:=DRExtra n)(m2:=emp).
 - apply map_join_emp.
 - cbn[V293_rdy_raw_cells]. eapply RIStar.
   + unfold DRExtra. RIApart 501%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_r_aemp_intro. split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply astar_r_aemp_intro. apply RIGlobals.
Qed.
Theorem DRLiteralPool : forall n,n<256 -> RIState(DRExtra n) |= DRCore.
Proof.
 intros n Range. apply(V293_create_dynamic_close 502%positive 501%positive 11 n RISlot Aemp Range). apply DRExtraSpatial.
Qed.
Theorem DRLiteralAmbient : forall n,n<256 -> RIState(DRExtra n) |= invlth_isr DRInv 0 INUM.
Proof.
 intros n Range. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply DRNoisrCore. apply DRLiteralPool;exact Range.
Qed.
Theorem DRLiteralDisjoint : forall n,
 join(RIMemory V293_create_occupied_priority)(DRExtra n)(DRWhole n).
Proof.
 intro n. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;left;unfold RIMemory,RILocals,RICurrent,RIByte;RIOutside| ].
 destruct(Pos.eq_dec b 502%positive);[subst b;left;unfold RIMemory,RILocals,RICurrent,RIByte;RIOutside|right;left].
 unfold DRExtra,RIByte;RIOutside.
Qed.
Definition DRFpre := ERFpre V293_create_occupied_priority.
Definition DRFpost := V293_create_dynamic_fpost RIR(spec_done None)(fun _=>false)[][]RIRFun.
Definition DRPre := ERPre V293_create_occupied_priority.
Definition DRPost : retasrt := fun result=>V293_create_internal_post_cells **
 getasrt(DRFpost(RIArgs V293_create_occupied_priority)result[]RITid) ** V293_create_internal_domain.
Theorem DRRealBuilders :
 Some DRPre=BuildPreI ERProgram 903%Z(rev(RIArgs V293_create_occupied_priority))[]DRFpre RITid /\
 Some DRPost=BuildRetI ERProgram 903%Z(rev(RIArgs V293_create_occupied_priority))[]DRFpost RITid.
Proof.
 split;[apply ERRealBuilders| ]. unfold BuildRetI,ERProgram.
 destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
Qed.
Theorem DRLiteralBuilderEntry : RIState(RIMemory V293_create_occupied_priority) |= DRPre.
Proof. apply ERLiteralBuilderEntry. Qed.
Theorem DRCallerHasNoSharedByte :
 get(RIMemory V293_create_occupied_priority)(501%positive,0%Z)=None.
Proof. apply ERSharedByteNotInCaller. Qed.
Theorem DRContractChecked :
 InfRules(fun _=>None)V293_scheduler V293_witness_li DRInv
 DRPost Afalse DRPre(V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 904%Z 902%Z 900%Z)Afalse RITid.
Proof.
 eapply V293_OSTaskCreateExt_dynamic_rejection_contract with(P:=ERProgram)
 (creator:=903%Z)(p:=11)(K:=Aemp)
 (vl:=rev(RIArgs V293_create_occupied_priority))(lg:=[])(good:=RIRFun)
 (isr:=fun _=>false)(is:=[])(cs:=[])(table:=502%positive)(bn:=501%positive)
 (R:=RIR)(aop:=spec_done None)(target:=17%Z)(argv:=Vnull)(inputtop:=Vnull)
 (identity:=Vint32 Int.zero)(bottom:=Vnull)(size:=Vint32 Int.zero)(ext:=Vnull)(options:=Vint32 Int.zero).
 - lia.
 - reflexivity.
 - apply RIRFrame.
 - apply RIRInv.
 - apply DRBorrowEquivalence.
 - unfold ERProgram. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply DRRealBuilders.
 - apply DRRealBuilders.
Qed.
Theorem DRPhysicalLoads : forall n,n<256 ->
 load Tint8(DRWhole n)(501%positive,0%Z)=Some(V293_byteval n) /\
 load(Tptr V293_tcb_type)(DRWhole n)(502%positive,44%Z)=Some(Vptr RISlot).
Proof.
 intros n Bound. pose proof(DRExtraSpatial n)as H.
 unfold V293_create_dynamic_owned in H.
 assert(N:load Tint8(DRExtra n)(501%positive,0%Z)=Some(V293_byteval n)).
 { change(load Tint8(getmem(RIState(DRExtra n)))(501%positive,0%Z)=Some(V293_byteval n)).
   eapply V293_rdy_raw_load with(cells:=V293_create_dynamic_cells 502%positive 501%positive 11 n RISlot);
   [left;reflexivity|apply V293_byte_type;exact Bound|exact H]. }
 assert(T:load(Tptr V293_tcb_type)(DRExtra n)(502%positive,44%Z)=Some(Vptr RISlot)).
 { change(load(Tptr V293_tcb_type)(getmem(RIState(DRExtra n)))(502%positive,44%Z)=Some(Vptr RISlot)).
   eapply V293_rdy_raw_load with(cells:=V293_create_dynamic_cells 502%positive 501%positive 11 n RISlot);
   [right;left;reflexivity|reflexivity|exact H]. }
 split;[exact(@load_local _ _ _ _ (DRExtra n)(RIMemory V293_create_occupied_priority)
   ltac:(apply map_join_comm;apply DRLiteralDisjoint) N)|
 exact(@load_local _ _ _ _ (DRExtra n)(RIMemory V293_create_occupied_priority)
   ltac:(apply map_join_comm;apply DRLiteralDisjoint) T)].
Qed.
Definition DRNestExpr := ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32).
Theorem DRTypedNestingGuard : forall n,n<256 ->
 evalval DRNestExpr(RIGE,RILE,DRWhole n)=Some(Vint32(if Nat.eqb n 0 then Int.zero else Int.one)) /\
 evaltype DRNestExpr(RIGE,RILE,DRWhole n)=Some Tint32.
Proof.
 intros n Bound. pose proof(proj1(DRPhysicalLoads n Bound))as NestingRead.
 assert(Nn:get RILE 99%Z=None)by(vm_compute;reflexivity).
 assert(Gn:get RIGE 99%Z=Some(501%positive,Tint8))by(vm_compute;reflexivity).
 remember RIGE as ge in *. remember RILE as le in *. remember(DRWhole n)as M in *.
 clear Heqge Heqle HeqM. unfold DRNestExpr. split.
 - cbn[evalval evaltype get_lenv get_genv get_mem].
   cbv delta[env var memory.ident Modules.ident block]in *. rewrite Nn,Gn.
   cbn beta iota. rewrite NestingRead.
   cbn[cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu].
   unfold Int.ltu. rewrite !Int.unsigned_repr by
    (unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
   change (Int.unsigned Int.zero) with 0%Z.
   destruct n as [ | n].
   + reflexivity.
   + cbn[Nat.eqb]. destruct(zlt 0(Z.of_nat(S n)));[reflexivity|lia].
 - cbn[evaltype get_lenv get_genv].
   cbv delta[env var memory.ident Modules.ident block]in *. rewrite Nn,Gn. reflexivity.
Qed.
Print Assumptions DRContractChecked.
Print Assumptions DRTypedNestingGuard.
