Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
(* Same-memory refinement after the real OS_InitTCBList call.
   This does not establish the production interrupt invariant or GOOD_OS. *)
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteAllocator.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBList.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition V293_init_zero_value (tp:type) :=
 match tp with Tint8|Tint16|Tint32=>Vint32 Int.zero|_=>Vnull end.
Lemma V293_init_zero_typed_owned : forall b off tp v n R,
 encode_val tp v=repeat(Byte Byte.zero)n ->
 V293_rdy_raw_cells(V293_clr_bytes b off(repeat(Vint32 Int.zero)n))R ==>
 Amapsto(b,off)tp true v ** R.
Proof.
 intros b off tp v n R Enc s H. apply V293_raw_cells_separate in H.
 eapply astar_mono;[ |intros st HS;exact HS|exact H].
 intros st HS. destruct(V293_zero_bytes_memory n b off st HS)as[Bytes Empty].
 split;[ |exact Empty]. exists(repeat(Byte Byte.zero)n). split;[exact Enc|exact Bytes].
Qed.
Fixpoint V293_init_zero_run b off (types:list type) : list V293_record_cell :=
 match types with []=>[]|tp::rest=>
 ((b,off),tp,V293_init_zero_value tp)::V293_init_zero_run b(off+Z.of_nat(typelen tp))rest end.
Lemma V293_init_zero_run_fold : forall types b off R,
 Forall(fun tp=>encode_val tp(V293_init_zero_value tp)=repeat(Byte Byte.zero)(typelen tp))types ->
 V293_rdy_raw_cells(V293_clr_bytes b off(repeat(Vint32 Int.zero)
  (fold_right(fun tp n=>(typelen tp+n)%nat)0%nat types)))R ==>
 V293_rdy_raw_cells(V293_init_zero_run b off types)R.
Proof.
 induction types as[ |tp rest IH];intros b off R Valid s H;[exact H| ].
 inversion Valid as[ |? ? Enc Tail];subst.
 cbn[fold_right]in H. rewrite V293_zero_bytes_split,V293_raw_cells_append in H.
 apply(V293_init_zero_typed_owned b off tp(V293_init_zero_value tp)(typelen tp)_ Enc)in H.
 cbn[V293_init_zero_run V293_rdy_raw_cells].
 eapply astar_mono;[intros st HS;exact HS|apply IH;exact Tail|exact H].
Qed.
Lemma V293_init_raw_storage : forall cells R,
 Forall(fun c=>rule_type_val_match(snd(fst c))(snd c)=true)cells ->
 V293_rdy_raw_cells cells R ==> V293_storage(map(fun c=>fst c)cells) ** R.
Proof.
 induction cells as[ |[[a tp]v]rest IH];intros R Valid s H.
 - cbn[V293_rdy_raw_cells V293_storage map]in *. clear -H;sep auto.
 - inversion Valid as[ |? ? Typed Tail];subst.
   cbn[V293_rdy_raw_cells map V293_storage fst snd]in *.
   assert(K:s |= V293_storage_cell a tp ** (V293_storage(map(fun c:V293_record_cell=>fst c)rest) ** R)).
   { eapply astar_mono;[ |apply IH;exact Tail|exact H].
     intros st HS. exists v. apply astar_l_apure_intro;[exact HS|exact Typed]. }
   clear -K;sep auto.
Qed.

Lemma V293_tcb_init_zero_payload : forall b base R,
 V293_rdy_raw_cells
 (V293_clr_bytes b base(repeat(Vint32 Int.zero)20)++
  V293_clr_bytes b(base+24)(repeat(Vint32 Int.zero)32))R ==>
 V293_tcb_free_payload b base ** R.
Proof.
 intros b base R s H. rewrite V293_raw_cells_append in H.
 pose proof(V293_init_zero_run_fold
 (Tptr Tint32::Tptr Tvoid::Tptr Tint32::Tint32::Tint16::Tint16::nil)
 b base _ ltac:(repeat constructor;reflexivity) s H)as K.
 assert(Tail:V293_rdy_raw_cells(V293_clr_bytes b(base+24)(repeat(Vint32 Int.zero)32))R ==>
 V293_rdy_raw_cells(V293_init_zero_run b(base+24)
 (Tcom_ptr 410::Tcom_ptr 411::Tptr Tvoid::Tcom_ptr 412::Tint16::Tint8::Tint8::Tint32::
  Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::nil))R).
 { exact(V293_init_zero_run_fold
   (Tcom_ptr 410::Tcom_ptr 411::Tptr Tvoid::Tcom_ptr 412::Tint16::Tint8::Tint8::Tint32::
    Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::Tint8::nil)
   b(base+24)R ltac:(repeat constructor;reflexivity)). }
 pose proof(V293_raw_cells_mono _ _ _ Tail s K)as J.
 rewrite <-V293_raw_cells_append in J.
 lazymatch type of J with _ |= V293_rdy_raw_cells ?cells _ =>
 apply(V293_init_raw_storage cells R ltac:(repeat constructor;reflexivity))in J end.
 cbn[V293_init_zero_run map app fst snd Z.of_nat typelen]in J.
 repeat rewrite <-Z.add_assoc in J. cbn[Z.add]in J.
 unfold V293_tcb_free_payload,V293_tcb_free_payload_cells.
 cbn[V293_storage]in J|-*. rewrite Z.add_0_r.
 clear -J;sep auto.
Qed.

Fixpoint V293_init_free_links b off n : list V293_record_cell :=
 match n with O=>[]|S k=>
 ((b,off+20),Tcom_ptr 410,match k with O=>Vnull|S _=>Vptr(b,Int.repr(off+56))end)::
 V293_init_free_links b(off+56)k end.
Definition V293_init_free_head b off n :=
 match n with O=>Vnull|S _=>Vptr(b,Int.repr off)end.
Lemma V293_tcb_init_chain_fold : forall n b off sites R,
 0<=off -> off+56*Z.of_nat n<=Int.max_unsigned ->
 (forall i,(i<n)%nat -> In(b,Int.repr(off+56*Z.of_nat i))sites) ->
 V293_rdy_raw_cells(V293_init_free_links b off n)
 (V293_rdy_raw_cells(V293_tcb_untouched_cells b off n)R) ==>
 V293_tcb_site_free_chain sites n(V293_init_free_head b off n) ** R.
Proof.
 induction n as[ |n IH];intros b off sites R Start Limit Members s H.
 - cbn[V293_init_free_links V293_tcb_untouched_cells V293_rdy_raw_cells
    V293_init_free_head V293_tcb_site_free_chain]in *;clear -H;sep auto.
 - cbn[V293_init_free_links V293_tcb_untouched_cells V293_rdy_raw_cells]in H.
   repeat rewrite V293_raw_cells_append in H.
   assert(Swap:s |= Amapsto(b,off+20)(Tcom_ptr 410)true
    (match n with O=>Vnull|S _=>Vptr(b,Int.repr(off+56))end) **
    V293_rdy_raw_cells
     (V293_clr_bytes b off(repeat(Vint32 Int.zero)20)++
      V293_clr_bytes b(off+24)(repeat(Vint32 Int.zero)32))
     (V293_rdy_raw_cells(V293_init_free_links b(off+56)n)
      (V293_rdy_raw_cells(V293_tcb_untouched_cells b(off+56)n)R))).
   { eapply astar_mono;[intros st HS;exact HS| |exact H].
     intros st HS.
     change(st |= V293_rdy_raw_cells(V293_init_free_links b(off+56)n)
      (V293_rdy_raw_cells
       (V293_clr_bytes b off(repeat(Vint32 Int.zero)20)++
        V293_clr_bytes b(off+24)(repeat(Vint32 Int.zero)32))
       (V293_rdy_raw_cells(V293_tcb_untouched_cells b(off+56)n)R)))in HS.
     eapply V293_raw_cells_swap;exact HS. }
   assert(K:s |= Amapsto(b,off+20)(Tcom_ptr 410)true
    (match n with O=>Vnull|S _=>Vptr(b,Int.repr(off+56))end) **
    (V293_tcb_free_payload b off **
     (V293_tcb_site_free_chain sites n(V293_init_free_head b(off+56)n) ** R))).
   { eapply astar_mono;[intros st HS;exact HS| |exact Swap].
     intros st HS. apply V293_tcb_init_zero_payload in HS.
     eapply astar_mono;[intros st' H';exact H'| |exact HS].
     apply IH;[lia|rewrite Nat2Z.inj_succ in Limit;lia| ].
     intros i Range. replace(off+56+56*Z.of_nat i)with(off+56*Z.of_nat(S i))by(rewrite Nat2Z.inj_succ;lia).
     apply Members;lia. }
   assert(Bound:off+55<=Int.max_unsigned)by(rewrite Nat2Z.inj_succ in Limit;pose proof(Nat2Z.is_nonneg n);lia).
   assert(Member:In(b,Int.repr off)sites).
   { specialize(Members 0%nat ltac:(lia)). cbn in Members. rewrite Z.add_0_r in Members;exact Members. }
   assert(Typed:rule_type_val_match(Tcom_ptr 410)
    (match n with O=>Vnull|S _=>Vptr(b,Int.repr(off+56))end)=true)by(destruct n;reflexivity).
   cbn[V293_init_free_head V293_tcb_site_free_chain].
   rewrite Int.unsigned_repr by lia.
   clear -K Typed Bound Member;unfold V293_init_free_head in K;sep auto.
Qed.
Lemma V293_tcb_init_linked_pool : forall bt bf R,
 Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
 V293_rdy_raw_cells(V293_tcb_linked_next bt)
 (V293_rdy_raw_cells(V293_tcb_untouched_cells bt 0 13)R) ==>
 V293_tcb_site_free_pool bt bf ** R.
Proof.
 intros bt bf R s H.
 assert(Links:V293_tcb_linked_next bt=V293_init_free_links bt 0 13)by reflexivity.
 rewrite Links in H.
 assert(K:s |= Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
  (V293_tcb_site_free_chain(V293_tcb_table_sites bt)13(Vptr(bt,Int.zero)) ** R)).
 { eapply astar_mono;[intros st HS;exact HS| |exact H].
   apply(V293_tcb_init_chain_fold 13 bt 0(V293_tcb_table_sites bt)R).
   - lia.
   - vm_compute;congruence.
   - intros i Range. unfold V293_tcb_table_sites. apply in_map_iff.
     exists i. split;[reflexivity|apply in_seq;lia]. }
 unfold V293_tcb_site_free_pool. sep normal. exists(Vptr(bt,Int.zero)). clear -K;sep auto.
Qed.
Definition V293_init_tcb_pool_rest bl bp frame :=
 Amapsto(bl,0)(Tptr V293_tcb_type)true Vnull **
 V293_rdy_raw_cells(V293_null_pointer_cells bp 0 13++frame)Atrue.
Lemma V293_tcb_call_result_pool : forall bl bf bt bp frame,
 V293_rdy_raw_cells(V293_tcb_call_result bl bf bt bp frame)Atrue ==>
 V293_tcb_site_free_pool bt bf ** V293_init_tcb_pool_rest bl bp frame.
Proof.
 intros bl bf bt bp frame s H.
 unfold V293_tcb_call_result,V293_tcb_call_heads in H.
 repeat rewrite V293_raw_cells_append in H.
 change(s |= Amapsto(bl,0)(Tptr V293_tcb_type)true Vnull **
  (Amapsto(bf,0)(Tptr V293_tcb_type)true(Vptr(bt,Int.zero)) **
  V293_rdy_raw_cells(V293_tcb_linked_next bt)
  (V293_rdy_raw_cells(V293_tcb_untouched_cells bt 0 13)
  (V293_rdy_raw_cells(V293_null_pointer_cells bp 0 13++frame)Atrue))))in H.
 eapply astar_mono in H;[ |intros st HS;exact HS|apply V293_tcb_init_linked_pool].
 unfold V293_init_tcb_pool_rest. clear -H;sep auto.
Qed.

Theorem V293_OS_InitTCBList_call_finite_pool : forall oldtcbs oldprios frame P ks ge caller M
  ir aux O op f clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2
  bt bp bl bf bi bn b1 b2 vl vf,
  P f=Some (V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  ix<ix_next -> ix_next<ptcb1 -> ptcb1<ptcb2 ->
  NoDup (V293_tcb_call_blocks bi bn b1 b2) ->
  fresh M bi -> fresh M bn -> fresh M b1 -> fresh M b2 ->
  V293_tcb_link_env ge (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2 ->
  get (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2) priorities=None ->
  get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (forall a tp v, In (a,tp,v) (V293_tcb_call_result bl bf bt bp frame) ->
    ~In (fst a) (V293_tcb_call_blocks bi bn b1 b2)) ->
  (ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++
      V293_tcb_call_heads bl bf vl vf++frame) Atrue ->
  exists Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |=
      V293_tcb_site_free_pool bt bf ** V293_init_tcb_pool_rest bl bp frame /\
    (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intros oldtcbs oldprios frame P ks ge caller M ir aux O op f clear dest size table priorities
    list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf bi bn b1 b2 vl vf
    Program Clear Names A B C ND Fi Fn F1 F2 Env Prn Prg Lt Lp Away Owned.
 destruct(V293_OS_InitTCBList_call_return oldtcbs oldprios frame P ks ge caller M ir aux O op
    f clear dest size table priorities list_head free_head ix ix_next ptcb1 ptcb2
    bt bp bl bf bi bn b1 b2 vl vf Program Clear Names A B C ND Fi Fn F1 F2 Env Prn Prg Lt Lp Away Owned)
    as(Ms&Mf&Exec&BodyResult&Returned&Outside&Freed).
 exists Mf. split;[exact Exec| ]. split;[apply V293_tcb_call_result_pool;exact Returned|exact Freed].
Qed.
Print Assumptions V293_OS_InitTCBList_call_finite_pool.
