(* Literal full-byte publication inputs; no production Inv or Hook body claim. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition PPGE : env := set(set(set(set FPGE
 93%Z(701%positive,Tptr V293_tcb_type))94%Z(702%positive,Tint8))
 95%Z(703%positive,Tarray Tint8 2))96%Z(704%positive,Tint8).
Definition PPState M cs : RstateOP :=
 (PPGE,FPLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition PPNew := Vptr(501%positive,Int.zero).
Definition PPOld := Vptr(511%positive,Int.zero).
Definition PPTail := Vptr(512%positive,Int.zero).
Definition PPDefaults (cells:list(addr*type)) := map(fun '(a,tp)=>(a,tp,FPDefault tp))cells.
Definition PPNodeRows b prev next := PPDefaults(V293_tcb_active_payload_cells b 0) ++
 [((b,20%Z),Tcom_ptr 410%Z,next);((b,24%Z),Tcom_ptr 410%Z,prev)].
Definition PPSpareRows := PPDefaults(V293_tcb_publication_spare_cells 501%positive 0).
Definition PPSharedRows (present:bool) y :=
 [((701%positive,0%Z),Tptr V293_tcb_type,if present then PPOld else Vnull);
 ((702%positive,0%Z),Tint8,V293_byteval 0);
 ((703%positive,Z.of_nat y),Tint8,V293_byteval 16);
 ((703%positive,Z.of_nat(1-y)),Tint8,V293_byteval 99);
 ((704%positive,0%Z),Tint8,V293_byteval(if present then 2 else 0))] ++
 if present then PPNodeRows 511%positive Vnull PPTail ++ PPNodeRows 512%positive PPOld Vnull else [].
Definition PPPrivateRows y :=
 [((208%positive,0%Z),Tptr V293_tcb_type,PPNew);
 ((501%positive,52%Z),Tint8,V293_byteval y);
 ((501%positive,54%Z),Tint8,V293_byteval(2^y));
 ((501%positive,53%Z),Tint8,V293_byteval(2^5));
 ((501%positive,20%Z),Tcom_ptr 410%Z,Vnull);
 ((501%positive,24%Z),Tcom_ptr 410%Z,Vnull)] ++ PPSpareRows.
Definition PPInputRows present y := PPPrivateRows y ++ PPSharedRows present y.
Definition PPInput present y := merge(FPMemory(PPInputRows present y))(merge FPCurrent FPSentinel).
Definition PPPre (present:bool) y cs :=
 V293_tcb_publication_input 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99 Vnull Vnull FPR
 (spec_done None)(fun _=>false)nil cs.
Definition PPPost (present:bool) y cs :=
 V293_tcb_publication_output 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y
 (S(if present then 2 else 0))(Nat.setbit 0 y)(Nat.setbit 16 5)99 FPR
 (spec_done None)(fun _=>false)nil cs.
Lemma PPStar : forall m1 m2 m cs p q,
 join m1 m2 m -> PPState m1 cs |= p -> PPState m2 cs |= q -> PPState m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma PPRSpatial : forall cs,PPState(merge FPCurrent FPSentinel)cs |= FPR.
Proof.
 intros. unfold FPR. eapply PPStar with(m1:=FPCurrent)(m2:=FPSentinel).
 - FPRapart 402%positive.
 - exists Tvoid. exists 402%positive. eapply PPStar with(m1:=emp)(m2:=FPCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply PPStar with(m1:=emp)(m2:=FPSentinel);[apply map_join_comm;apply map_join_emp| | ].
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro;[split;reflexivity|apply V293_witness_li_good].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PPBindings : forall cs,PPState emp cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive.
Proof.
 intro cs. unfold V293_pub_bindings. repeat split;first[
 solve[exists 208%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 701%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 702%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 703%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 704%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[intros[v H];vm_compute in H;discriminate]].
Qed.
Ltac PPRaw :=
 lazymatch goal with
 | |- PPState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?cs |= _ =>
 let bytes:=eval cbv in(Z.of_nat(typelen tp))in
 eapply PPStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
 [FPApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|PPRaw]
 | |- PPState emp _ |= Aemp =>split;reflexivity
 end.
Lemma PPLiteralRaw : forall (present upper:bool) cs,
 PPState(FPMemory(PPInputRows present(if upper then 1 else 0)))cs |=
 V293_rdy_raw_cells(PPInputRows present(if upper then 1 else 0))Aemp.
Proof.
 intros. destruct present,upper;unfold PPInputRows,PPPrivateRows,PPSpareRows,PPSharedRows,PPNodeRows,
 PPDefaults,V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells.
 all:cbn[app map FPMemory V293_rdy_raw_cells];PPRaw.
Qed.
Lemma PPDefaultsStorage : forall cells R,
 Forall(fun '(_,tp)=>rule_type_val_match tp(FPDefault tp)=true)cells ->
 V293_rdy_raw_cells(PPDefaults cells)R ==> V293_storage cells ** R.
Proof.
 intros cells R T. induction T as[ |[a tp]xs Ty Ts IH];intros s H.
 - cbn[PPDefaults map V293_rdy_raw_cells V293_storage]in *;clear -H;sep auto.
 - cbn[PPDefaults map V293_rdy_raw_cells V293_storage]in *.
   assert(B:s |= V293_storage_cell a tp ** V293_rdy_raw_cells(PPDefaults xs)R).
   { eapply astar_mono;[ |intros st HS;exact HS|exact H]. intros st HS.
     exists(FPDefault tp). apply astar_l_apure_intro;[exact HS|exact Ty]. }
   eapply astar_mono in B;[ |intros st HS;exact HS|exact IH]. clear -B;sep auto.
Qed.
Lemma PPNodeFold : forall b prev next R,
 rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 V293_rdy_raw_cells(PPNodeRows b prev next)R ==>
 V293_tcb_active_payload b 0 **
 (Amapsto(b,20%Z)(Tcom_ptr 410%Z)true next ** (Amapsto(b,24%Z)(Tcom_ptr 410%Z)true prev ** R)).
Proof.
 intros b prev next R Typed s H. unfold PPNodeRows in H. rewrite V293_raw_cells_append in H.
 eapply PPDefaultsStorage in H.
 - cbn[V293_rdy_raw_cells]in H. exact H.
 - unfold V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells. cbn[app]. repeat constructor.
Qed.
Lemma PPChainFold : forall (present:bool) R,
 V293_rdy_raw_cells(if present then PPNodeRows 511%positive Vnull PPTail ++ PPNodeRows 512%positive PPOld Vnull else [])R ==>
 V293_tcb_active_chain(if present then 2 else 0)Vnull(if present then PPOld else Vnull) ** R.
Proof.
 intros present R s H. assert(B:(55<=Int.max_unsigned)%Z)by(vm_compute;congruence). destruct present.
 - rewrite V293_raw_cells_append in H. apply PPNodeFold in H;[ |reflexivity].
   eapply astar_mono in H;[ |intros st HS;exact HS| ].
   2:{ apply astar_mono;[intros st HS;exact HS| ].
       apply astar_mono;[intros st HS;exact HS|apply PPNodeFold;reflexivity]. }
   cbn[PPOld PPTail V293_tcb_active_chain Int.unsigned]. sep normal.
   exists PPTail. cbn[PPTail V293_tcb_active_chain Int.unsigned]. sep normal. exists Vnull.
   cbn[V293_tcb_active_chain]. clear -H B;sep auto.
 - cbn[V293_rdy_raw_cells V293_tcb_active_chain]in *. clear -H;sep auto.
Qed.
Lemma PPSharedFold : forall (present:bool) y,
 V293_rdy_raw_cells(PPSharedRows present y)Aemp ==>
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive y
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99.
Proof.
 intros present y s H. unfold PPSharedRows in H. rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply PPChainFold].
 unfold V293_tcb_publication_pool. cbn[V293_rdy_raw_cells]in H. clear -H;sep auto.
Qed.
Lemma PPPrivateFold : forall y R,
 V293_rdy_raw_cells(PPPrivateRows y)R ==>
 Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0 y 5 Vnull Vnull ** R).
Proof.
 intros y R s H. unfold PPPrivateRows,PPSpareRows in H. rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply PPDefaultsStorage;unfold V293_tcb_publication_spare_cells;repeat constructor].
 unfold V293_tcb_publication_new. cbn[V293_rdy_raw_cells]in H|-*. clear -H;sep auto.
Qed.
Lemma PPPhysicalView : forall (present:bool) y,
 V293_rdy_raw_cells(PPInputRows present y)Aemp ==>
 Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0 y 5 Vnull Vnull **
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive y
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99).
Proof.
 intros present y s H. unfold PPInputRows in H. rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply PPSharedFold]. apply PPPrivateFold in H. exact H.
Qed.
Lemma PPInputRaw : forall (present upper:bool) cs,
 PPState(PPInput present(if upper then 1 else 0))cs |=
 V293_rdy_raw_cells(PPInputRows present(if upper then 1 else 0))Aemp ** FPR.
Proof.
 intros present upper cs. unfold PPInput.
 eapply PPStar;[ |apply PPLiteralRaw|apply PPRSpatial].
   apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ];
   try(destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left]);
   unfold PPInputRows,PPPrivateRows,PPSpareRows,PPSharedRows,PPNodeRows,PPDefaults,
   V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells,FPCurrent,FPSentinel,FPBytes;
   destruct present,upper;cbn[app map FPMemory];FPOutside.
Qed.
Theorem PPLiteralInput : forall (present upper:bool) cs,
 PPState(PPInput present(if upper then 1 else 0))cs |= PPPre present(if upper then 1 else 0)cs.
Proof.
 intros present upper cs. pose proof(PPInputRaw present upper cs)as S. unfold PPInput in S|-*.
 eapply astar_mono in S;[ |apply PPPhysicalView|intros st HS;exact HS].
 assert(C:PPState(merge(FPMemory(PPInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive **
 ((Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0(if upper then 1 else 0)5 Vnull Vnull **
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99)) ** FPR)).
 { eapply PPStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply PPBindings|exact S]. }
 apply astar_l_aop'_intro with(aop:=spec_done None)in C;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in C;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in C;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in C;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cs)in C;[ |reflexivity].
 unfold PPPre,V293_tcb_publication_input. clear -C;sep auto.
Qed.
Theorem PPBodyChecked : forall Spec sd I r ri (present upper:bool) cs,
 InfRules Spec sd V293_witness_li I r ri(PPPre present(if upper then 1 else 0)cs)
 (V293_TCB_publish_body 108%Z 93%Z 94%Z 95%Z 96%Z)
 (PPPost present(if upper then 1 else 0)cs)FPTid.
Proof.
 intros. unfold PPPre,PPPost. change PPOld with(V293_pub_old_head true 511%positive 0).
 destruct present;destruct upper.
 all:first[apply V293_OS_TCBInit_publish_pool_body with(bo:=511%positive)(obase:=0%Z)(k:=1)(present:=true)|apply V293_OS_TCBInit_publish_pool_body with(bo:=511%positive)(obase:=0%Z)(k:=1)(present:=false)];
 try(solve[vm_compute;intuition congruence]);try lia;apply FPRCurLINV.
Qed.

(* Isolated first two physical link stores of the real publication body.
   Globals/bitmap/count remain unchanged here; this is not a mutated AST trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Definition PPLinkPrivate next :=
 [((208%positive,0%Z),Tptr V293_tcb_type,PPNew);
 ((501%positive,52%Z),Tint8,V293_byteval 0);
 ((501%positive,54%Z),Tint8,V293_byteval 1);
 ((501%positive,53%Z),Tint8,V293_byteval 32);
 ((501%positive,20%Z),Tcom_ptr 410%Z,next);
 ((501%positive,24%Z),Tcom_ptr 410%Z,Vnull)] ++ PPSpareRows.
Definition PPLinkHeader := firstn 5(PPSharedRows true 0).
Definition PPLinkRows next back := PPLinkPrivate next ++ PPLinkHeader ++
 PPNodeRows 511%positive back PPTail ++ PPNodeRows 512%positive PPOld Vnull.
Definition PPNextStore := store(Tcom_ptr 410%Z)(PPInput true 0)(501%positive,20%Z)PPOld.
Definition PPLinkResult (perform_write:bool) :=
 match PPNextStore with
 | None=>None
 | Some M=>if perform_write then store(Tcom_ptr 410%Z)M(511%positive,24%Z)PPNew else Some M
 end.
Lemma PPRawWrite : forall before a tp old after replacement R M cs,
 rule_type_val_match tp replacement=true ->
 PPState M cs |= V293_rdy_raw_cells(before++(a,tp,old)::after)R ->
 exists Mf,store tp M a replacement=Some Mf /\
 PPState Mf cs |= V293_rdy_raw_cells(before++(a,tp,replacement)::after)R.
Proof.
 intros before a tp old after replacement R M cs Valid H.
 apply V293_rdy_cell_out in H.
 destruct(V293_tick_raw_slot_update _ _ _ _ _ _ _ _ _ _ _ _ Valid H)as(Mf&Store&Final).
 exists Mf. split;[exact Store|apply V293_rdy_cell_in].
 unfold V293_owned_record_cell in Final. apply astar_assoc_elim in Final.
 apply astar_l_apure_elim in Final. exact(proj2 Final).
Qed.
Ltac PPWrite H target replacement newM storeH :=
 lazymatch type of H with
 | PPState ?M ?cs |= V293_rdy_raw_cells ?rows ?R =>
  let cells:=eval cbv[PPLinkRows PPLinkPrivate PPLinkHeader PPInputRows PPPrivateRows PPSpareRows
    PPSharedRows PPNodeRows PPDefaults V293_tcb_active_payload_cells V293_tcb_publication_spare_cells
    firstn app map]in rows in
  let rec find before rest :=
   lazymatch rest with
   | (?a,?tp,?old)::?tail =>
     first[unify a target;
       let K:=fresh "Updated" in
       destruct(@PPRawWrite before a tp old tail replacement R M cs eq_refl H)as(newM&storeH&K);
       clear H;rename K into H|
       find(before++[(a,tp,old)])tail]
   end in find (@nil V293_record_cell)cells
 end.
Lemma PPNextStoreChecked : forall cs,exists M,
 PPNextStore=Some M /\ PPState M cs |= V293_rdy_raw_cells(PPLinkRows PPOld Vnull)FPR.
Proof.
 intro cs. pose proof(PPInputRaw true false cs)as H.
 apply astar_comm in H. apply V293_raw_cells_unmove_frame in H.
 eapply V293_raw_cells_mono in H;[ |intros st HS;apply astar_r_aemp_elim;exact HS].
 (* Give the update helper a single raw list, without expanding memory. *)
 change(PPState(PPInput true 0)cs |= V293_rdy_raw_cells(PPLinkRows Vnull Vnull)FPR)in H.
 PPWrite H (501%positive,20%Z) PPOld M Store.
 exists M. split;[exact Store|exact H].
Qed.
Lemma PPBackStoreChecked : forall M cs,
 PPState M cs |= V293_rdy_raw_cells(PPLinkRows PPOld Vnull)FPR ->
 exists Mf,store(Tcom_ptr 410%Z)M(511%positive,24%Z)PPNew=Some Mf /\
 PPState Mf cs |= V293_rdy_raw_cells(PPLinkRows PPOld PPNew)FPR.
Proof.
 intros M cs H. PPWrite H (511%positive,24%Z) PPNew Mf Store.
 exists Mf. split;[exact Store|exact H].
Qed.
Lemma PPLinkPrivateFold : forall next R,
 V293_rdy_raw_cells(PPLinkPrivate next)R ==>
 Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0 0 5 next Vnull ** R).
Proof.
 intros next R s H. unfold PPLinkPrivate,PPSpareRows in H.
 rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply PPDefaultsStorage;unfold V293_tcb_publication_spare_cells;repeat constructor].
 unfold V293_tcb_publication_new. cbn[V293_rdy_raw_cells]in H|-*. clear -H;sep auto.
Qed.
Lemma PPOldChainFold : forall prev R,
 V293_rdy_raw_cells(PPNodeRows 511%positive prev PPTail ++ PPNodeRows 512%positive PPOld Vnull)R ==>
 V293_tcb_active_chain 2 prev PPOld ** R.
Proof.
 intros prev R s H. assert(B:(55<=Int.max_unsigned)%Z)by(vm_compute;congruence).
 rewrite V293_raw_cells_append in H. apply PPNodeFold in H;[ |reflexivity].
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2:{ apply astar_mono;[intros st HS;exact HS| ].
     apply astar_mono;[intros st HS;exact HS|apply PPNodeFold;reflexivity]. }
 cbn[PPOld PPTail V293_tcb_active_chain Int.unsigned]. sep normal.
 exists PPTail. cbn[PPTail V293_tcb_active_chain Int.unsigned]. sep normal. exists Vnull.
 cbn[V293_tcb_active_chain]. clear -H B;sep auto.
Qed.
Lemma PPLinkChainFold : forall R,
 V293_rdy_raw_cells(PPLinkRows PPOld PPNew)R ==>
 V293_tcb_active_chain 3 Vnull PPNew ** Atrue.
Proof.
 intros R s H. unfold PPLinkRows in H. rewrite !V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply V293_raw_cells_mono;apply PPOldChainFold].
 apply PPLinkPrivateFold in H.
 assert(B:s |= V293_rdy_raw_cells
 ([((501%positive,52%Z),Tint8,V293_byteval 0);
 ((501%positive,54%Z),Tint8,V293_byteval 1);
 ((501%positive,53%Z),Tint8,V293_byteval 32)])
 (V293_storage(V293_tcb_publication_spare_cells 501%positive 0)) **
 (Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true PPOld **
 (Amapsto(501%positive,24%Z)(Tcom_ptr 410%Z)true Vnull **
 (V293_tcb_active_chain 2 PPNew PPOld **
 (Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_rdy_raw_cells PPLinkHeader Aemp ** R)))))).
 { unfold V293_tcb_publication_new,PPLinkHeader,PPSharedRows in H.
   unfold PPLinkHeader,PPSharedRows. cbn[firstn app V293_rdy_raw_cells Z.add Nat.pow Nat.mul Nat.add]in *;clear -H;sep auto.
 }
 eapply astar_mono in B;[ |apply V293_tcb_publication_payload_fold with(b:=501%positive)(base:=0%Z)(y:=0)(x:=5);lia|intros st HS;exact HS].
 eapply astar_mono with(Q:=Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_rdy_raw_cells PPLinkHeader Aemp ** R));[intros st HS;exact HS|intros st HS;exact I| ].
 cbn[PPNew V293_tcb_active_chain Int.unsigned]. sep normal. exists PPOld.
 assert(Bound:(55<=Int.max_unsigned)%Z)by(vm_compute;congruence).
 clear -B Bound;sep auto.
Qed.
Lemma PPFinalChainBacklink : forall s,
 s |= V293_tcb_active_chain 3 Vnull PPNew ** Atrue ->
 load(Tcom_ptr 410%Z)(getmem s)(501%positive,20%Z)=Some PPOld ->
 load(Tcom_ptr 410%Z)(getmem s)(511%positive,24%Z)=Some PPNew.
Proof.
 intros s H Next.
 assert(N:s |= EX next:val,[|rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 (Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true next **
 (V293_tcb_active_chain 2 PPNew next **
 (V293_tcb_active_payload 501%positive 0 **
 (Amapsto(501%positive,24%Z)(Tcom_ptr 410%Z)true Vnull ** Atrue))))).
 { cbn[PPNew V293_tcb_active_chain Int.unsigned]in H.
   sep normal in H. sep destruct H. sep normal. exists x. clear -H;sep auto. }
 destruct N as[next N]. apply astar_l_apure_elim in N. destruct N as[Typed N].
 assert(L:load(Tcom_ptr 410%Z)(getmem s)(501%positive,20%Z)=Some next).
 { eapply V293_star_load_l;[ |exact N]. intros st[HM _].
   eapply mapstoval_load;[exact Typed|exact HM]. }
 assert(next=PPOld)by congruence. subst next.
 eapply V293_star_load_r;[ |exact N]. intros st HS.
 eapply V293_star_load_l;[ |exact HS]. intros st1 H1.
 cbn[PPOld V293_tcb_active_chain Int.unsigned]in H1.
 apply astar_l_apure_elim in H1. destruct H1 as[_ H1].
 eapply V293_star_load_r;[ |exact H1]. intros st2 H2.
 destruct H2 as[tail H2]. apply astar_l_apure_elim in H2. destruct H2 as[_ H2].
 eapply V293_star_load_r;[ |exact H2]. intros st3 H3.
 eapply V293_star_load_l;[ |exact H3]. intros st4[HM _].
 eapply mapstoval_load;[reflexivity|exact HM].
Qed.
Lemma PPNormalChainChecked : forall cs,exists M,
 PPLinkResult true=Some M /\ PPState M cs |= V293_tcb_active_chain 3 Vnull PPNew ** Atrue.
Proof.
 intro cs. destruct(PPNextStoreChecked cs)as(M&First&Owned).
 destruct(PPBackStoreChecked M cs Owned)as(Mf&Second&Final).
 exists Mf. split;[unfold PPLinkResult;rewrite First;exact Second| ].
 apply PPLinkChainFold in Final. exact Final.
Qed.
Lemma PPOmittedBreaksFinalChain : forall M cs,
 PPLinkResult false=Some M ->
 ~ PPState M cs |= V293_tcb_active_chain 3 Vnull PPNew ** Atrue.
Proof.
 intros M cs Result Chain. destruct(PPNextStoreChecked cs)as(M0&First&Owned).
 unfold PPLinkResult in Result. rewrite First in Result. inversion Result;subst M0.
 assert(Next:load(Tcom_ptr 410%Z)M(501%positive,20%Z)=Some PPOld).
 { change(load(Tcom_ptr 410%Z)(getmem(PPState M cs))(501%positive,20%Z)=Some PPOld).
   eapply V293_rdy_raw_load;[ |reflexivity|exact Owned].
   cbv[PPLinkRows PPLinkPrivate PPLinkHeader PPSharedRows PPNodeRows PPSpareRows PPDefaults
     V293_tcb_active_payload_cells V293_tcb_publication_spare_cells firstn app map].
   repeat(first[solve[left;reflexivity]|right]). }
 assert(Prev:load(Tcom_ptr 410%Z)M(511%positive,24%Z)=Some Vnull).
 { change(load(Tcom_ptr 410%Z)(getmem(PPState M cs))(511%positive,24%Z)=Some Vnull).
   eapply V293_rdy_raw_load;[ |reflexivity|exact Owned].
   cbv[PPLinkRows PPLinkPrivate PPLinkHeader PPSharedRows PPNodeRows PPSpareRows PPDefaults
     V293_tcb_active_payload_cells V293_tcb_publication_spare_cells firstn app map].
   repeat(first[solve[left;reflexivity]|right]). }
 pose proof(PPFinalChainBacklink _ Chain Next). change(load(Tcom_ptr 410%Z)M(511%positive,24%Z)=Some PPNew)in H. rewrite Prev in H. discriminate.
Qed.
