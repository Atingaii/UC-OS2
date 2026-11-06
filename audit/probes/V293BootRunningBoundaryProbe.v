(* Same literal bytes as stage49; only the current global identifier is bound
   to framework OSTCBCur (60), rather than the old alpha-renamed identifier26.
   This is an initializer witness and a single-store control, not OSStart. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293InitChainProbe.
Require Import CertiOS.certiucos.v293.proofs.V293BootRunningBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293StartCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition BRGE : env := set ChainGE OSTCBCur(166%positive,Tptr V293_tcb_type).
Definition BRState M := V293_wstate BRGE ChainCaller M.
Definition BRProgram f :=
 if Z.eq_dec f 202%Z then
 Some(V293_InitRdyList_function 21%Z 22%Z 23%Z 24%Z 25%Z OSTCBCur 41%Z)
 else ChainProgram f.
Definition BRCore := V293_create_joint_core 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive 182%positive (209%positive,Int.zero).
Definition BRTarget : tid := (82%positive,Int.zero).

(* Only scalar bindings are transferred, each checked. Raw byte assertions
   do not inspect the global environment. No blanket program renaming axiom. *)
Lemma BRResourcesRebind : forall slots cells ge ge' le M ir aux O op,
 (forall d,In d slots -> get ge'(init_name d)=Some(init_block d,init_type d)) ->
 (ge,le,M,ir,aux,O,op) |= V293_init_resources slots false(V293_rdy_raw_cells cells Atrue) ->
 (ge',le,M,ir,aux,O,op) |= V293_init_resources slots false(V293_rdy_raw_cells cells Atrue).
Proof.
 induction slots as[ | d ds IH];intros cells ge ge' le M ir aux O op Bindings Owned.
 - eapply V293_raw_cells_environment;[right;reflexivity|exact Owned].
 - cbn[V293_init_resources]in *. apply sat_split in Owned.
   destruct Owned as(m1&m2&o1&o2&JM&JO&One&Tail).
   apply sat_split'. exists m1. exists m2. exists o1. exists o2.
   split;[exact JM| ]. split;[exact JO| ]. split.
   + apply sat_split in One. destruct One as(mb&mv&ob&ov&JMb&JOb&[Global Local]&Value).
     apply sat_split'. exists mb. exists mv. exists ob. exists ov.
     split;[exact JMb| ]. split;[exact JOb| ]. split;[ | exact Value].
     split;[ | exact Local]. destruct Global as(b&Old&Addr&EM&EO).
     exists(init_block d). split;[apply Bindings;left;reflexivity| ].
     split;[reflexivity| ]. split;assumption.
   + eapply IH;[intros x Member;apply Bindings;right;exact Member|exact Tail].
Qed.
Lemma BRLiteralEntry : V293_wstate BRGE emp ChainEntryMemory |=
 V293_init_resources ChainSlots false(V293_rdy_raw_cells ChainTail Atrue).
Proof.
 eapply BRResourcesRebind;[ | exact ChainLiteralFullEntry].
 intros d Member. vm_compute in Member.
 repeat(destruct Member as[Same|Member];[subst d;reflexivity| ]);contradiction.
Qed.
Lemma BRReadyEnvironment : forall bi,
 V293_rdy_env BRGE(V293_rdy_locals 41%Z bi)21%Z 22%Z 23%Z 24%Z 25%Z OSTCBCur 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi;repeat split;reflexivity. Qed.
Lemma BRTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env BRGE(V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros;repeat split;reflexivity. Qed.
Theorem BRActualInitialization : forall ks,exists Mf,
 cstepstar BRProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BRGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BRGE,ChainCaller,Mf) /\
 BRState Mf |= V293_rdy_raw_cells ChainFinalCells Atrue /\
 BRState Mf |= BRCore ** V293_rdy_raw_cells ChainFrame Atrue /\
 load(Tptr V293_tcb_type)Mf(166%positive,0%Z)=Some Vnull /\
 load Tint8 Mf(185%positive,0%Z)=Some(Vint32 Int.zero).
Proof.
 intro ks.
 destruct(V293_OSInit_three_calls ChainSlots(repeat Vundef 728)
 (repeat(Vint32(Int.repr 255))52)ChainFrame BRProgram ks BRGE ChainCaller ChainEntryMemory
 (fun _=>false)(false,nil,nil)emp(spec_done None)
 201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z OSTCBCur 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
 (Vint32(Int.repr 7))(Vint32(Int.repr 3))Vundef(Vint32(Int.repr 5))
 (Vint32(Int.repr 9))(Vptr(211%positive,Int.zero))(Vptr(212%positive,Int.zero))
 (Vptr(121%positive,Int.zero))(Vptr(122%positive,Int.zero))
 ltac:(unfold ChainSlots,V293_InitMisc_slots;repeat(apply Forall_cons;[unfold V293_init_scalar;cbn;auto| ]);apply Forall_nil)
 ltac:(reflexivity)ltac:(reflexivity)ltac:(reflexivity)ltac:(reflexivity)
 ltac:(discriminate)ltac:(lia)ltac:(lia)ltac:(lia)
 BRReadyEnvironment BRTCBEnvironment ltac:(intros;reflexivity)ltac:(reflexivity)
 ltac:(apply repeat_length)ltac:(apply repeat_length)BRLiteralEntry)
 as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&EM&ER&ET&Final&FR&FT).
 exists Mf. split;[exact Exec| ]. split;[exact Final| ]. split.
 - unfold BRCore. eapply V293_init_three_result_creator_joint with
   (slots:=ChainSlots)
   (cd:=Build_V293_init_slot 1004%Z Tint8 184%positive)
   (nd:=Build_V293_init_slot 1002%Z Tint8 182%positive);
   [unfold ChainSlots,V293_InitMisc_slots;cbn;auto|reflexivity|reflexivity|
    unfold ChainSlots,V293_InitMisc_slots;cbn;auto|reflexivity|reflexivity|discriminate|exact Final].
 - split.
   + change(load(Tptr V293_tcb_type)(getmem(BRState Mf))(166%positive,0%Z)=Some Vnull).
     eapply V293_rdy_raw_load;[ | reflexivity|exact Final].
     unfold ChainFinalCells,V293_tcb_call_result. do 4(apply in_or_app;right).
     unfold ChainExtraCells. apply in_or_app;left. unfold ChainReadyZero,V293_rdy_globals.
     do 6 right;left;reflexivity.
   + change(load Tint8(getmem(BRState Mf))(185%positive,0%Z)=Some(Vint32 Int.zero)).
     eapply V293_rdy_raw_load;[ | reflexivity|exact Final].
     unfold ChainFinalCells,V293_tcb_call_result. do 4(apply in_or_app;right).
     unfold ChainExtraCells. apply in_or_app;right. apply in_or_app;left.
     unfold V293_misc_zero_cells,ChainSlots,V293_InitMisc_slots.
     do 4 right;left;reflexivity.
Qed.
Theorem BRBootRejectsRunningEntry : forall ks,exists Mf,
 cstepstar BRProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BRGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BRGE,ChainCaller,Mf) /\
 (forall li t,~(BRState Mf |= CurLINV li t)) /\
 (forall envs ir lst O I li lg,~initst((BRGE,envs,Mf),ir,lst)O I li lg).
Proof.
 intro ks. destruct(BRActualInitialization ks)as(Mf&Exec&Raw&Joint&Null&Running).
 exists Mf. split;[exact Exec| ]. split.
 - intros li t. eapply V293_null_current_no_CurLINV;[reflexivity|exact Null].
 - intros. eapply V293_null_current_no_initst;[reflexivity|exact Null].
Qed.

(* Single factor: the same boot memory, same target, same binding, same
   unrelated fields. Only one real current-pointer store is omitted. *)
Theorem BRCurrentStoreControl : forall M,
 BRState M |= V293_rdy_raw_cells ChainFinalCells Atrue ->
 exists Mf,
 store(Tptr V293_tcb_type)M(166%positive,0%Z)(Vptr BRTarget)=Some Mf /\
 load(Tptr V293_tcb_type)Mf(166%positive,0%Z)=Some(Vptr BRTarget) /\
 (BRState Mf |= CurTid BRTarget ** CurTid BRTarget ** Atrue) /\
 (BRState Mf |= CurLINV V293_witness_li BRTarget) /\
 load(Tptr V293_tcb_type)M(166%positive,0%Z)=Some Vnull /\
 (forall li t,~(BRState M |= CurLINV li t)).
Proof.
 intros M Raw.
 set(before:=V293_tcb_call_heads 94%positive 95%positive Vnull(Vptr(82%positive,Int.zero))++
 V293_tcb_linked_next 82%positive++V293_tcb_untouched_cells 82%positive 0 13++
 V293_null_pointer_cells 84%positive 0 13++firstn 6 ChainReadyZero).
 set(after:=V293_misc_zero_cells ChainSlots++ChainFrame).
 assert(Order:ChainFinalCells=before++((166%positive,0%Z),Tptr V293_tcb_type,Vnull)::after).
 { unfold before,after,ChainFinalCells,V293_tcb_call_result,ChainExtraCells,
   ChainReadyZero,V293_rdy_globals. repeat rewrite <-app_assoc. reflexivity. }
 rewrite Order in Raw. apply V293_rdy_cell_out in Raw.
 assert(Null:load(Tptr V293_tcb_type)M(166%positive,0%Z)=Some Vnull).
 { change(load(Tptr V293_tcb_type)(getmem(BRState M))(166%positive,0%Z)=Some Vnull).
   eapply V293_record_star_load_l;[ | exact Raw].
   intros st[H _];eapply mapstoval_load;[reflexivity|exact H]. }
 assert(Owned:BRState M |= V293_owned_record_cell
  ((166%positive,0%Z),Tptr V293_tcb_type,Vnull) ** V293_rdy_raw_cells(before++after)Atrue).
 { eapply astar_mono;[ | intros st H;exact H|exact Raw].
   intros st H. unfold V293_owned_record_cell. apply astar_l_apure_intro;[exact H|reflexivity]. }
 destruct(V293_owned_record_cell_update (166%positive,0%Z)(Tptr V293_tcb_type)Vnull(Vptr BRTarget)
  _ _ _ _ _ _ _ _ eq_refl Owned)as(Mf&Store&Final).
 assert(Pointer:BRState Mf |= Amapsto(166%positive,0%Z)(Tptr V293_tcb_type)true(Vptr BRTarget) ** Atrue).
 { unfold V293_owned_record_cell in Final.
   apply astar_assoc_elim in Final. apply astar_l_apure_elim in Final.
   destruct Final as[_ Final]. clear -Final;sep auto. }
 assert(Read:load(Tptr V293_tcb_type)Mf(166%positive,0%Z)=Some(Vptr BRTarget)).
 { change(load(Tptr V293_tcb_type)(getmem(BRState Mf))(166%positive,0%Z)=Some(Vptr BRTarget)).
   eapply V293_record_star_load_l;[ | exact Pointer].
   intros st[H _];eapply mapstoval_load;[reflexivity|exact H]. }
 assert(Global:BRState Mf |= (GV OSTCBCur @ (Tptr V293_tcb_type) |-> Vptr BRTarget) ** Atrue).
 { unfold BRState,V293_wstate in Pointer |- *.
   apply sat_split in Pointer. destruct Pointer as(m1&m2&o1&o2&JM&JO&Head&Tail).
   apply sat_split'. exists m1. exists m2. exists o1. exists o2.
   split;[exact JM| ]. split;[exact JO| ]. split;[ | exact Tail].
   eapply V293_start_global_owned;[reflexivity|exact Head]. }
 exists Mf. split;[exact Store| ]. split;[exact Read| ].
 split.
 - apply GV_separate_rw_frm in Global. unfold CurTid. clear -Global;sep auto.
 - split.
   + unfold CurLINV. exists (nil:list logicvar). unfold LINV,V293_witness_li.
     pose proof V293_witness_li_good as Good.
     apply GV_separate_rw_frm in Global. unfold CurTid. clear -Global Good;sep auto.
   + split;[exact Null| ]. intros li t.
     eapply V293_null_current_no_CurLINV;[reflexivity|exact Null].
Qed.

(* Explicit ghost-only boot placeholder. It does not denote a live task;
   no physical/abstract task, event or ready refinement is claimed. *)
Definition BRPlaceholder : tid := (209%positive,Int.zero).
Definition BRAbstract := merge(sig curtid(oscurt BRPlaceholder))
 (merge(sig abstcblsid(abstcblist(emp:TcbMod.map)))
 (merge(sig absecblsid(absecblist(emp:EcbMod.map)))(sig ostmid(ostm Int.zero)))).
Definition BRGhostState M O : RstateOP :=
 (BRGE,ChainCaller,M,(fun _=>false),(false,nil,nil),O,spec_done None).
Lemma BRGhostStar : forall m1 m2 m o1 o2 o p q,
 join m1 m2 m -> join o1 o2 o ->
 BRGhostState m1 o1 |= p -> BRGhostState m2 o2 |= q -> BRGhostState m o |= p ** q.
Proof.
 intros. exists m1. exists m2. exists m. exists o1. exists o2. exists o.
 repeat first[assumption|reflexivity|split].
Qed.
Ltac BRAbsApart :=
 apply map_join_merge;apply map_disjoint;let k:=fresh "key" in intro k;destruct k;vm_compute;auto.
Lemma BRAbstractSpatial :
 BRGhostState emp BRAbstract |= V293_shared_fields BRPlaceholder emp emp Int.zero.
Proof.
 unfold V293_shared_fields,BRAbstract.
 repeat(eapply BRGhostStar with(m1:=emp)(m2:=emp);
  [apply map_join_emp|BRAbsApart|split;reflexivity| ]).
 split;reflexivity.
Qed.
Theorem BRBootAbstractOwnership : forall ks,exists Mf,
 cstepstar BRProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BRGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BRGE,ChainCaller,Mf) /\
 (BRGhostState Mf BRAbstract |=
   V293_shared_fields BRPlaceholder emp emp Int.zero ** V293_rdy_raw_cells ChainFinalCells Atrue) /\
 (forall Of OO,join BRAbstract Of OO -> Of=emp) /\
 (forall li t,~(BRGhostState Mf BRAbstract |= CurLINV li t)).
Proof.
 intro ks. destruct(BRActualInitialization ks)as(Mf&Exec&Raw&Joint&Null&Running).
 assert(Owned:BRGhostState Mf BRAbstract |=
   V293_shared_fields BRPlaceholder emp emp Int.zero ** V293_rdy_raw_cells ChainFinalCells Atrue).
 { eapply BRGhostStar with(m1:=emp)(m2:=Mf)(o1:=BRAbstract)(o2:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply map_join_emp.
   - exact BRAbstractSpatial.
   - exact Raw. }
 exists Mf. split;[exact Exec| ]. split;[exact Owned| ]. split.
 - intros Of OO Joined.
   change(join(getabst(BRGhostState Mf BRAbstract))Of OO)in Joined.
   eapply V293_fields_no_abstract_frame;[exact Owned|exact Joined].
 - intros li t. eapply V293_null_current_no_CurLINV;[reflexivity|exact Null].
Qed.

(* Connect the one-store control to this actual initializer's SAME Mf.
   Even the positive local-entry result is not initst, OSStart or GoodI. *)
Theorem BRReachableCurrentStoreControl : forall ks,exists M Mf,
 cstepstar BRProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BRGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BRGE,ChainCaller,M) /\
 store(Tptr V293_tcb_type)M(166%positive,0%Z)(Vptr BRTarget)=Some Mf /\
 load(Tptr V293_tcb_type)Mf(166%positive,0%Z)=Some(Vptr BRTarget) /\
 (BRState Mf |= CurTid BRTarget ** CurTid BRTarget ** Atrue) /\
 (BRState Mf |= CurLINV V293_witness_li BRTarget) /\
 load(Tptr V293_tcb_type)M(166%positive,0%Z)=Some Vnull /\
 (forall li t,~(BRState M |= CurLINV li t)).
Proof.
 intro ks. destruct(BRActualInitialization ks)as(M&Exec&Raw&Joint&Null&Running).
 destruct(BRCurrentStoreControl M Raw)as(Mf&Store&Read&Halves&Entry&Old&NoEntry).
 exists M. exists Mf. split;[exact Exec| ].
 split;[exact Store| ]. split;[exact Read| ]. split;[exact Halves| ].
 split;[exact Entry| ]. split;assumption.
Qed.
