(* Fixed OSTimeTick: real two-local call prefix and post-hook void return.
   Explicit sret maps C's implicit void fall-through; this is a manual source
   model, not a verified frontend. The CPU hook remains a call/OPEN boundary. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_function ptcb rows group saved now running head hook :=
  (Tvoid,dnil,dcons ptcb (Tptr V293_tcb_type) (dcons saved Tint32 dnil),
    sseq (V293_tick_body ptcb rows group saved now running head hook) sret).
Definition V293_tick_locals ptcb saved bc bs : env :=
  set (set emp ptcb (bc,Tptr V293_tcb_type)) saved (bs,Tint32).

(* The spatial frame is evaluated in the final callee environment throughout;
   only the operational semantics changes environments during allocation. *)
Lemma V293_tick_allocate_frame : forall ge le M ir aux O op b tp R,
  fresh M b -> (ge,le,M,ir,aux,O,op) |= R ->
  (ge,le,allocb M b 0%Z (typelen tp),ir,aux,O,op) |=
    Amapsto (b,0%Z) tp true Vundef ** R.
Proof.
  intros ge le M ir aux O op b tp R Fresh Frame.
  exists (allocb empmem b 0%Z (typelen tp)). exists M.
  exists (allocb M b 0%Z (typelen tp)).
  exists (emp:osabst). exists O. exists O.
  split; [reflexivity | ]. split.
  - eapply join_allocb with (m1:=empmem) (m2:=M);
      [apply map_join_comm;apply map_join_emp | reflexivity | reflexivity | exact Fresh].
  - split; [reflexivity | ]. split; [apply map_join_comm;apply map_join_emp | ].
    split; [split; [apply alloc_empmem_mapstoval | reflexivity] | exact Frame].
Qed.

Theorem V293_tick_call_to_hook :
  forall P ks ge caller M ir enabled si ci O op tickfn ptcb rows group saved now running head hook bc bs R,
  P tickfn = Some (V293_tick_function ptcb rows group saved now running head hook) ->
  ptcb <> saved -> fresh M bc ->
  fresh (allocb M bc 0%Z (typelen (Tptr V293_tcb_type))) bs ->
  (ge,V293_tick_locals ptcb saved bc bs,M,ir,(enabled,si,ci),O,op) |= R ->
  exists Ms,
    V293_local_steps P (curs (scall tickfn nil),(kenil,ks))
      ((ge,caller,M),ir,(enabled,si,ci))
      (curs (scall hook nil),(kenil,
        kseq (V293_tick_post_hook ptcb rows group now running head)
          (kseq sret (kcall tickfn
            (sseq (V293_tick_body ptcb rows group saved now running head hook) sret) caller ks))))
      ((ge,V293_tick_locals ptcb saved bc bs,Ms),ir,(enabled,si,ci)) /\
    load (Tptr V293_tcb_type) Ms (bc,0%Z) = Some Vundef /\
    load Tint32 Ms (bs,0%Z) = Some (Vint32 Int.zero) /\
    (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
      V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) **
        (Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef ** R).
Proof.
  intros P ks ge caller M ir enabled si ci O op tickfn ptcb rows group saved now running head hook bc bs R
    Program Different FreshScan FreshSaved Frame.
  pose proof (V293_tick_allocate_frame _ _ _ _ _ _ _ bc (Tptr V293_tcb_type) _ FreshScan Frame) as Scan.
  pose proof (V293_tick_allocate_frame _ _ _ _ _ _ _ bs Tint32 _ FreshSaved Scan) as Both.
  destruct (V293_tick_raw_slot_update (bs,0%Z) Tint32 Vundef (Vint32 Int.zero)
    _ _ _ _ _ _ _ _ eq_refl Both) as (Ms & StoreZero & Owned).
  assert (SavedBinding : get (V293_tick_locals ptcb saved bc bs) saved = Some (bs,Tint32)).
  { unfold V293_tick_locals. apply map_get_set. }
  assert (ScanUnbound : ~ indom (emp:env) ptcb).
  { intros [v E]. rewrite map_emp_get in E. discriminate. }
  assert (SavedUnbound : ~ indom (set (emp:env) ptcb (bc,Tptr V293_tcb_type)) saved).
  { intros [v E]. rewrite map_get_set' in E by exact Different. rewrite map_emp_get in E. discriminate. }
  assert (FinalScan : load (Tptr V293_tcb_type) Ms (bc,0%Z) = Some Vundef).
  { change (load (Tptr V293_tcb_type)
      (getmem (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some Vundef).
    eapply V293_record_star_load_r; [ | exact Owned].
    eapply V293_record_star_load_l. intros st Slot.
    eapply V293_tick_raw_pointer_load; [left;reflexivity | exact Slot]. }
  assert (FinalSaved : load Tint32 Ms (bs,0%Z) = Some (Vint32 Int.zero)).
  { change (load Tint32
      (getmem (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op)) (bs,0%Z) = Some (Vint32 Int.zero)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned]. }
  exists Ms. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply snpcall_step]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step; [reflexivity | ].
      eapply sfexec_step with (d1:=dnil) (d2:=dcons ptcb (Tptr V293_tcb_type) (dcons saved Tint32 dnil));
        [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bc. repeat split; assumption || reflexivity. }
    eapply V293_local_cons.
    { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bs. repeat split; assumption || reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sallocend_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    unfold V293_tick_body.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply V293_success_assign_zero; [exact SavedBinding | exact StoreZero]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sseq_step]. }
    apply V293_local_refl.
  - split; [exact FinalScan | ]. split; [exact FinalSaved | exact Owned].
Qed.

(* Successful store construction from ownership also witnesses every original
   byte's write permission. This does not assume a free succeeds. *)
Lemma V293_tick_storebytes_writable : forall bytes M M' b i,
  storebytes M (b,i) bytes = Some M' -> V293_bytes_writable M b i (length bytes).
Proof.
  induction bytes as [ | raw bytes IH]; intros M M' b i Store k K; [cbn in K;lia | ].
  change (match get M (b,i), storebytes M (b,(i+1)%Z) bytes with
    | Some (true,_),Some tail => Some (set tail (b,i) (true,raw))
    | _,_ => None end = Some M') in Store.
  destruct (get M (b,i)) as [[permission v] | ] eqn:Cell; try discriminate.
  destruct permission; try discriminate.
  destruct (storebytes M (b,(i+1)%Z) bytes) as [tail | ] eqn:Tail; try discriminate.
  destruct k as [ | k].
  - exists v. replace (i+Z.of_nat 0)%Z with i by lia. exact Cell.
  - replace (i+Z.of_nat (S k))%Z with (i+1+Z.of_nat k)%Z by lia.
    eapply IH; [exact Tail | cbn in K;lia].
Qed.

Lemma V293_tick_raw_owned_writable : forall b tp v R ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) tp true v ** R ->
  V293_bytes_writable M b 0%Z (typelen tp).
Proof.
  intros b tp v R ge le M ir aux O op Owned.
  apply sat_split in Owned.
  destruct Owned as (part & rest & o1 & o2 & Join & OJoin & [Points Empty] & Frame).
  destruct (store_exist_join' (b,0%Z) tp v v part rest M Points Join) as [M' Store].
  unfold store in Store.
  pose proof (V293_tick_storebytes_writable _ _ _ _ _ Store) as W.
  rewrite encode_val_length in W. exact W.
Qed.

Theorem V293_tick_void_return : forall P ks ge le caller M f body next,
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists Mf,
    cstepstar P (curs sret,(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,next)) (ge,caller,Mf) /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get Mf (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get Mf (b,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next Call ND W.
  destruct (V293_sfree_construct_execution (getaddr le) P ks ge le M None ND W)
    as (Mf & Free & Frame & Removed).
  exists Mf. split.
  - eapply c_stepstarn.
    { eapply stmt_step; [reflexivity | ]. eapply sret_step; [reflexivity | exact Call | reflexivity]. }
    eapply V293_cstepstar_trans; [exact Free | ].
    eapply c_stepstarn.
    { eapply stmt_step; [reflexivity | ]. eapply sfreeend_step; [reflexivity | reflexivity | exact Call]. }
    apply c_stepstar0.
  - split; [exact Frame | exact Removed].
Qed.

(* The environment is ordered by variable names; either order enumerates
   exactly the same two allocated objects, not an assumed allocator result. *)
Lemma V293_tick_local_addresses : forall ptcb saved bc bs,
  ptcb <> saved ->
  Permutation (getaddr (V293_tick_locals ptcb saved bc bs))
    [(bc,Tptr V293_tcb_type); (bs,Tint32)].
Proof.
  intros ptcb saved bc bs Different.
  unfold V293_tick_locals.
  change (Permutation
    (getaddr (EnvMod.set (EnvMod.set EnvMod.emp ptcb (bc,Tptr V293_tcb_type)) saved (bs,Tint32)))
    [(bc,Tptr V293_tcb_type);(bs,Tint32)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  destruct (identspec.blt saved ptcb) eqn:Order.
  - apply perm_swap.
  - rewrite identspec.neq_beq_false by congruence. apply Permutation_refl.
Qed.

Theorem V293_tick_suffix_void_lifecycle :
  forall tasks P ks ge caller M ir enabled si ci O op ptcb saved rows group now running head
    bc bs bn bu bh idle bg br tick run g lo hi f body R,
  ptcb <> saved -> bc <> bs ->
  get (V293_tick_locals ptcb saved bc bs) ptcb = Some (bc,Tptr V293_tcb_type) ->
  get (V293_tick_locals ptcb saved bc bs) rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get (V293_tick_locals ptcb saved bc bs) group = None -> get ge group = Some (bg,Tint8) ->
  get (V293_tick_locals ptcb saved bc bs) now = None -> get ge now = Some (bn,Tint32) ->
  get (V293_tick_locals ptcb saved bc bs) running = None -> get ge running = Some (bu,Tint8) ->
  get (V293_tick_locals ptcb saved bc bs) head = None -> get ge head = Some (bh,Tptr V293_tcb_type) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_task_valid tasks -> run<256 -> g<256 -> lo<256 -> hi<256 ->
  (ge,V293_tick_locals ptcb saved bc bs,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_storage_owned bn tick bu run bh (V293_tick_head tasks idle)
      bc Vundef tasks idle bg br g lo hi
      (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) ** R) ->
  exists Ms Mf,
    V293_local_steps P
      (curs (sskip None),
        (kenil,kseq (V293_tick_post_hook ptcb rows group now running head)
          (kseq sret (kcall f body caller ks))))
      ((ge,V293_tick_locals ptcb saved bc bs,M),ir,(enabled,si,ci))
      (curs (sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    load Tint32 Ms (bn,0%Z) = Some (Vint32 (Int.add tick Int.one)) /\
    load (Tptr V293_tcb_type) Ms (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vundef) /\
    (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
      V293_tick_storage_owned bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
        bc (if Nat.eqb run 1 then Vptr idle else Vundef)
        (if Nat.eqb run 1 then map V293_tick_task_after tasks else tasks) idle bg br
        (fst (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi))))
        (fst (snd (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)))))
        (snd (snd (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)))))
        (V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) ** R) /\
    (forall b i, b <> bc -> b <> bs -> get Mf (b,i) = get Ms (b,i)) /\
    (forall k, k<4 -> get Mf (bc,Z.of_nat k) = None /\ get Mf (bs,Z.of_nat k) = None).
Proof.
  intros tasks P ks ge caller M ir enabled si ci O op ptcb saved rows group now running head
    bc bs bn bu bh idle bg br tick run g lo hi f body R Different Blocks
    Bc Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Run G Lo Hi Owned.
  pose proof (V293_tick_uninitialized_suffix_execution tasks P
    (kseq sret (kcall f body caller ks)) ge (V293_tick_locals ptcb saved bc bs) M
    ir enabled si ci O op ptcb rows group now running head bc bn bu bh idle bg br tick run g lo hi
    _ Bc Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Run G Lo Hi Owned) as Suffix.
  cbn zeta in Suffix. destruct Suffix as (Ms & Exec & Time & Scan & Returned).
  assert (ScanOwned : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true
      (if Nat.eqb run 1 then Vptr idle else Vundef) ** Atrue).
  { unfold V293_tick_storage_owned in Returned. clear -Returned. sep auto. }
  assert (SavedOwned : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell ((bs,0%Z),Tint32,Vint32 Int.zero) ** Atrue).
  { unfold V293_tick_storage_owned in Returned. clear -Returned. sep auto. }
  assert (SavedRaw : (ge,V293_tick_locals ptcb saved bc bs,Ms,ir,(enabled,si,ci),O,op) |=
    Amapsto (bs,0%Z) Tint32 true (Vint32 Int.zero) ** Atrue).
  { unfold V293_owned_record_cell in SavedOwned. apply astar_assoc_elim in SavedOwned.
    apply astar_l_apure_elim in SavedOwned. exact (proj2 SavedOwned). }
  pose proof (V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ ScanOwned) as Wscan.
  pose proof (V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ SavedRaw) as Wsaved.
  pose proof (V293_tick_local_addresses ptcb saved bc bs Different) as Layout.
  assert (ND : NoDup (map fst (getaddr (V293_tick_locals ptcb saved bc bs)))).
  { assert (Two : NoDup (bc :: bs :: nil)).
    { constructor.
      - cbn. intuition congruence.
      - constructor; [cbn;tauto | constructor]. }
    eapply Permutation_NoDup.
    - apply Permutation_map. apply Permutation_sym. exact Layout.
    - exact Two. }
  assert (W : forall b tp, In (b,tp) (getaddr (V293_tick_locals ptcb saved bc bs)) ->
    V293_bytes_writable Ms b 0%Z (typelen tp)).
  { intros b tp Member. apply (Permutation_in (b,tp) Layout) in Member.
    destruct Member as [E | [E | E]]; [inversion E;subst | inversion E;subst | contradiction]; assumption. }
  destruct (V293_tick_void_return P (kcall f body caller ks) ge
    (V293_tick_locals ptcb saved bc bs) caller Ms f body ks eq_refl ND W)
    as (Mf & Return & Frame & Removed).
  exists Ms. exists Mf. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity | apply sskip_step]. }
    apply V293_csteps_local. exact Return.
  - split; [exact Time | ]. split; [exact Scan | ]. split; [exact Returned | ]. split.
    + intros b i Bc' Bs'. apply Frame. intro Member.
      apply in_map_iff in Member. destruct Member as ([c tp] & E & Member). cbn in E. subst c.
      apply (Permutation_in (b,tp) Layout) in Member. cbn in Member. intuition congruence.
    + intros k K. split.
      * apply Removed with (Tptr V293_tcb_type); [ | exact K].
        eapply Permutation_in; [apply Permutation_sym;exact Layout | left;reflexivity].
      * apply Removed with Tint32; [ | exact K].
        eapply Permutation_in; [apply Permutation_sym;exact Layout | right;left;reflexivity].
Qed.

Print Assumptions V293_tick_call_to_hook.
Print Assumptions V293_tick_void_return.
Print Assumptions V293_tick_suffix_void_lifecycle.
