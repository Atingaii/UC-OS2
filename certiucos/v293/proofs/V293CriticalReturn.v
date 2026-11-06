(* Source-level boundary facts, NOT an implementation of the analysis port.
   The call-to-primitive interpretation obligation is deliberately not assumed.
   Return execution starts after the port has returned to its caller. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_saved_ie (M : mem) (bs : block) (saved : bool) : Prop :=
  load Tint32 M (bs,0%Z) =
    Some (Vint32 (if saved then Int.one else Int.zero)).

Lemma V293_saved_ie_frame : forall M M' bs saved,
  (forall i, get M' (bs,i) = get M (bs,i)) ->
  V293_saved_ie M bs saved -> V293_saved_ie M' bs saved.
Proof.
  intros M M' bs saved Frame Token. unfold V293_saved_ie in *.
  etransitivity; [apply V293_load_block_frame; exact Frame | exact Token].
Qed.

(* The most involved error entry: SELF may write oldprio and the lookup
   writes ptcb. Only these two blocks need exclusion for saved-token framing.
   This is still an entry-to-CALL result, not a call-to-excrit execution. *)
Theorem V293_reserved_entry_preserves_saved :
  forall P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br saved,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) -> get le cpu_sr = Some (bs,Tint32) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero)) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  bs <> bo -> bs <> bc -> V293_saved_ie M bs saved ->
  exists Mf,
    cstepstar P
      (curs (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id),(kenil,ks)) (ge,le,M)
      (curs (sfexec exit_id (Vptr (bs,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks)) (ge,le,Mf) /\
    V293_saved_ie Mf bs saved /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (br,Int.zero)) /\
    (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved cpu_sr exit_id
    b bo bn bc bs bcur bct base old new curprio br saved O N resolved R
    Nt Gt Bo Bn Bc Bs Nr Gr Lo Ln Empty Slot Tbo Tbc OB CB CO Self CW SO SC Token.
  destruct (V293_task_prio_reserved_entry_error_execution P ks ge le M
    table oldprio newprio ptcb current reserved cpu_sr exit_id b bo bn bc bs
    bcur bct base old new curprio br O N R Nt Gt Bo Bn Bc Bs Nr Gr
    Lo Ln Empty Slot Tbo Tbc OB CB CO Self CW)
    as (Mf & Different & Exec & Old & New & Pointer & OldSlot & NewSlot & Frame).
  exists Mf. split; [exact Exec | ]. split.
  - eapply V293_saved_ie_frame; [intro i; apply Frame; assumption | exact Token].
  - split; assumption.
Qed.

(* A genuine framework primitive step. The saved value must agree with the
   stack top; address evaluation alone does not establish this agreement.
   In particular, an initially disabled caller is restored to false. *)
Theorem V293_excrit_restores_saved : forall P ks ge le M ir active si ci bs saved,
  V293_saved_ie M bs saved ->
  loststep P (curs (sprim excrit),(kenil,ks))
    ((ge,le,M),ir,(active,si,saved::ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(saved,si,ci)) /\
  V293_saved_ie M bs saved.
Proof.
  intros. split; [apply excrit_step; reflexivity | assumption].
Qed.

(* There is no external-call execution rule in cstep/loststep. In particular,
   no primitive step may silently replace a missing port function body. *)
Theorem V293_missing_port_has_no_step : forall P exit_id args types ks m ir au,
  P exit_id = None ->
  ~ exists C' state',
    loststep P (curs (sfexec exit_id args types),(kenil,ks))
      (m,ir,au) C' state'.
Proof.
  intros P exit_id args types ks m ir au Missing [C' [state' Step]].
  inversion Step; subst; try discriminate.
  match goal with H : cstep _ _ _ _ _ |- _ =>
    inversion H; subst; try discriminate
  end.
  all: match goal with E : (curs (sfexec _ _ _),_) = (_,_) |- _ =>
    inversion E; subst; clear E end.
  - match goal with H : estep _ _ _ _ _ _ |- _ => inversion H end.
  - match goal with H : sstep _ _ _ _ _ _ _ |- _ =>
      inversion H; subst; rewrite Missing in *; discriminate end.
Qed.

(* Construct deallocation from byte ownership, rather than assuming an
   intermediate free/store/execution result. *)
Lemma V293_freeb_construct : forall n M b i,
  V293_bytes_writable M b i n ->
  exists M', freeb M b i n = Some M'.
Proof.
  induction n as [ | n IH]; intros M b i W.
  - exists M. reflexivity.
  - destruct (W 0 ltac:(lia)) as [v Read].
    replace (i + Z.of_nat 0)%Z with i in Read by lia.
    destruct (IH M b (i+1)%Z) as [M' Free].
    { intros k K. specialize (W (S k) ltac:(lia)).
      replace (i+1+Z.of_nat k)%Z with (i+Z.of_nat (S k))%Z by lia.
      exact W. }
    exists (del M' (b,i)). cbn [freeb]. rewrite Read,Free. reflexivity.
Qed.

Lemma V293_freeb_outside : forall n M M' b i other j,
  freeb M b i n = Some M' ->
  other <> b \/ (j < i)%Z \/ (i+Z.of_nat n <= j)%Z ->
  get M' (other,j) = get M (other,j).
Proof.
  induction n as [ | n IH]; intros M M' b i other j Free Outside.
  - cbn [freeb] in Free. inversion Free. reflexivity.
  - cbn [freeb] in Free.
    destruct (get M (b,i)) as [[permission v] | ]; try discriminate.
    destruct permission; try discriminate.
    destruct (freeb M b (i+1)%Z n) as [tail | ] eqn:T; try discriminate.
    inversion Free; subst M'. rewrite map_del_sem.
    destruct (map_dec_a (b,i) (other,j)) as [E|E].
    + inversion E; subst. rewrite Nat2Z.inj_succ in Outside. intuition lia.
    + eapply IH; [exact T | ]. rewrite Nat2Z.inj_succ in Outside. intuition lia.
Qed.

Lemma V293_freeb_removed : forall n M M' b i k,
  freeb M b i n = Some M' -> k < n ->
  get M' (b,(i+Z.of_nat k)%Z) = None.
Proof.
  induction n as [ | n IH]; intros M M' b i k Free K; [lia | ].
  cbn [freeb] in Free.
  destruct (get M (b,i)) as [[permission v] | ]; try discriminate.
  destruct permission; try discriminate.
  destruct (freeb M b (i+1)%Z n) as [tail | ] eqn:T; try discriminate.
  inversion Free; subst M'. rewrite map_del_sem.
  destruct k as [ | k].
  - replace (i+Z.of_nat 0)%Z with i by lia.
    destruct (map_dec_a (b,i) (b,i)); [reflexivity|contradiction].
  - destruct (map_dec_a (b,i) (b,(i+Z.of_nat (S k))%Z)) as [E|E].
    + reflexivity.
    + replace (i+Z.of_nat (S k))%Z with (i+1+Z.of_nat k)%Z by lia.
      eapply IH; [exact T|lia].
Qed.

(* NoDup blocks is a sufficient local-allocation condition, not a proof that
   OSTaskChangePrio's real function entry has allocated such an environment. *)
Lemma V293_sfree_construct_execution : forall al P ks ge le M result,
  NoDup (map fst al) ->
  (forall b t, In (b,t) al -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists M',
    cstepstar P (curs (sfree al result),(kenil,ks)) (ge,le,M)
      (curs (sfree nil result),(kenil,ks)) (ge,le,M') /\
    (forall b i, ~ In b (map fst al) -> get M' (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) al -> k < typelen t -> get M' (b,Z.of_nat k) = None).
Proof.
  induction al as [ | [b t] al IH]; intros P ks ge le M result ND W.
  - exists M. split; [apply c_stepstar0 | ]. split; intros; [reflexivity|contradiction].
  - inversion ND as [ | ? ? NotIn NDtail]; subst.
    destruct (V293_freeb_construct (typelen t) M b 0%Z (W b t (or_introl eq_refl)))
      as [Mt Free].
    assert (Frame : forall c i, c <> b -> get Mt (c,i) = get M (c,i)).
    { intros c i Different. eapply V293_freeb_outside; [exact Free|left;exact Different]. }
    destruct (IH P ks ge le Mt result NDtail) as (M' & Exec & Outside & Removed).
    { intros c tp I k K. rewrite Frame.
      - apply W with tp; [right;exact I|exact K].
      - intro E; subst c. apply NotIn. apply in_map with (f:=@fst block type) in I. exact I. }
    exists M'. split.
    + eapply c_stepstarn.
      { eapply stmt_step; [reflexivity | ]. eapply sfree_step; [reflexivity|reflexivity|exact Free]. }
      exact Exec.
    + split.
      * intros c i NotLocal. rewrite Outside.
        -- apply Frame. intro E; subst c. apply NotLocal. left; reflexivity.
        -- intro I. apply NotLocal. right;exact I.
      * intros c tp k [E|I] K.
        -- inversion E; subst c tp. rewrite Outside by exact NotIn.
           replace (Z.of_nat k) with (0+Z.of_nat k)%Z by lia.
           eapply V293_freeb_removed; eassumption.
        -- eapply Removed; eassumption.
Qed.

(* This executes the actual return, including local frees and restoration of
   the caller's environment. callcont may contain arbitrary pending kseqs;
   their statements are discarded, not evaluated. No port execution oracle. *)
Theorem V293_error_return_execution : forall P ks ge le caller M f body next error,
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists M',
    cstepstar P (curs (srete (econst32 (Int.repr error))),(kenil,ks)) (ge,le,M)
      (curs (sskip (Some (Vint32 (Int.repr error)))),(kenil,next)) (ge,caller,M') /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get M' (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get M' (b,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next error Call ND W.
  destruct (V293_sfree_construct_execution (getaddr le) P ks ge le M
    (Some (Vint32 (Int.repr error))) ND W) as (M' & Free & Frame & Removed).
  exists M'. split.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply srete_step]. }
    eapply c_stepstarn. { eapply expr_step; [reflexivity|apply ec32_step]. }
    eapply c_stepstarn.
    { eapply stmt_step; [reflexivity | ].
      eapply (sretv_step P f _ body); [reflexivity|rewrite Call;discriminate|reflexivity]. }
    eapply V293_cstepstar_trans; [exact Free | ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | ]. eapply sfreeend_step; eassumption || reflexivity. }
    apply c_stepstar0.
  - split; assumption.
Qed.

Theorem V293_error_after_port_return : forall P ks ge le caller M f body next error,
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists M',
    cstepstar P
      (curs (sskip None),(kenil,kseq (srete (econst32 (Int.repr error))) ks)) (ge,le,M)
      (curs (sskip (Some (Vint32 (Int.repr error)))),(kenil,next)) (ge,caller,M') /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get M' (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get M' (b,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next error Call ND W.
  destruct (V293_error_return_execution P ks ge le caller M f body next error Call ND W)
    as (M' & Exec & Frame & Removed).
  exists M'. split.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
    exact Exec.
  - split; assumption.
Qed.

(* Only the pending-statement position is under test: there is no assumption
   that P defines 999. The return discards that call while freeing both locals.
   This is a physical environment witness, not full API-entry reachability. *)
Definition V293_return_fixture_le : env :=
  set (set emp 601%Z (61%positive,Tint32)) 501%Z (51%positive,Tint8).
Definition V293_return_fixture_mem (saved : bool) : mem :=
  V293_fixture_put_bytes
    (V293_put_byte (V293_put_byte emp (70%positive,0%Z) 23) (51%positive,0%Z) 8)
    61%positive 0%Z (encode_val Tint32 (Vint32 (if saved then Int.one else Int.zero))).

Lemma V293_fixture_saved_ie : forall M b (saved : bool),
  V293_saved_ie
    (V293_fixture_put_bytes M b 0%Z (encode_val Tint32 (Vint32 (if saved then Int.one else Int.zero)))) b saved.
Proof.
  intros M b saved. unfold V293_saved_ie,load,loadm.
  rewrite <- (encode_val_length Tint32 (Vint32 (if saved then Int.one else Int.zero))).
  rewrite V293_loadbytes_get.
  - rewrite type_val_mach_encode_val_decode_val by reflexivity. reflexivity.
  - intros k K. exists true. apply V293_fixture_bytes_nth. exact K.
Qed.

Theorem V293_error_return_locals_witness : forall P saved,
  V293_saved_ie (V293_return_fixture_mem saved) 61%positive saved /\
  exists Mf,
    cstepstar P
      (curs (sskip None),
        (kenil,kseq (srete (econst32 (Int.repr 67)))
          (kseq (scall 999%Z nil) (kcall 700%Z sret emp kstop))))
      (emp,V293_return_fixture_le,V293_return_fixture_mem saved)
      (curs (sskip (Some (Vint32 (Int.repr 67)))) ,(kenil,kstop)) (emp,emp,Mf) /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\
    load Tint8 Mf (70%positive,0%Z) = Some (V293_byteval 23).
Proof.
  intros P saved.
  assert (Addresses : getaddr V293_return_fixture_le =
    (51%positive,Tint8)::(61%positive,Tint32)::nil) by reflexivity.
  assert (ND : NoDup (map fst (getaddr V293_return_fixture_le))).
  { rewrite Addresses. repeat constructor; cbn; intuition discriminate. }
  assert (W : forall b t, In (b,t) (getaddr V293_return_fixture_le) ->
    V293_bytes_writable (V293_return_fixture_mem saved) b 0%Z (typelen t)).
  { intros b t I. rewrite Addresses in I. destruct I as [E|[E|F]]; try contradiction; inversion E; subst b t.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_return_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      exists (Byte (Byte.repr (Z.of_nat 8))). apply V293_put_byte_get_same.
    - intros k K. unfold V293_return_fixture_mem. eexists. apply V293_fixture_bytes_nth.
      rewrite encode_val_length. exact K. }
  split.
  - unfold V293_return_fixture_mem. apply V293_fixture_saved_ie.
  - destruct (V293_error_after_port_return P
      (kseq (scall 999%Z nil) (kcall 700%Z sret emp kstop)) emp V293_return_fixture_le emp
      (V293_return_fixture_mem saved) 700%Z sret kstop 67 eq_refl ND W)
      as (Mf & Exec & Frame & Removed).
    exists Mf. split; [exact Exec | ]. split.
    + intros k K. apply Removed with Tint32; [rewrite Addresses; right;left;reflexivity|exact K].
    + split.
      * change (get Mf (51%positive,Z.of_nat 0) = None).
        apply Removed with Tint8; [rewrite Addresses;left;reflexivity|cbn;lia].
      * etransitivity.
        -- apply V293_load_block_frame. intro i. apply Frame. rewrite Addresses. cbn. intuition discriminate.
        -- unfold V293_return_fixture_mem,load,loadm. rewrite V293_loadbytes_ext with
             (M:=V293_put_byte (V293_put_byte emp (70%positive,0%Z) 23) (51%positive,0%Z) 8).
           ++ change (load Tint8 (V293_put_byte (V293_put_byte emp (70%positive,0%Z) 23)
                (51%positive,0%Z) 8) (70%positive,0%Z) = Some (V293_byteval 23)).
              rewrite V293_put_byte_other_load by discriminate. apply V293_put_byte_load. lia.
           ++ intros k K. apply V293_fixture_bytes_outside. left;discriminate.
Qed.

Definition V293_saved_error_mem (self saved : bool) : mem :=
  V293_fixture_put_bytes (V293_error_fixture_mem self 2) 61%positive 0%Z
    (encode_val Tint32 (Vint32 (if saved then Int.one else Int.zero))).

Lemma V293_saved_error_outside : forall self saved c i,
  c <> 61%positive ->
  get (V293_saved_error_mem self saved) (c,i) = get (V293_error_fixture_mem self 2) (c,i).
Proof.
  intros. unfold V293_saved_error_mem. apply V293_fixture_bytes_outside. left;assumption.
Qed.

Theorem V293_reserved_saved_witness : forall self saved P ks,
  exists Mf,
    cstepstar P
      (curs (V293_task_prio_entry_reserved 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z),(kenil,ks))
      (V293_error_fixture_ge,V293_error_fixture_le,V293_saved_error_mem self saved)
      (curs (sfexec 602%Z (Vptr (61%positive,Int.zero)::nil) (Tptr Tint32::nil)),
        (kenil,kseq (srete (econst32 (Int.repr 67))) ks))
      (V293_error_fixture_ge,V293_error_fixture_le,Mf) /\
    V293_saved_ie Mf 61%positive saved /\
    load (Tptr V293_tcb_type) Mf (40%positive,0%Z) = Some (Vptr (90%positive,Int.zero)).
Proof.
  intros self saved P ks.
  destruct (V293_error_fixture_resources self 2) as (Lo & Ln & Empty & Slot & Current & Prio & Initial & Wo & CW).
  assert (LF : forall tp c i, c <> 61%positive ->
    load tp (V293_saved_error_mem self saved) (c,i) = load tp (V293_error_fixture_mem self 2) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply V293_saved_error_outside. assumption. }
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self;reflexivity).
  destruct (V293_reserved_entry_preserves_saved P ks V293_error_fixture_ge V293_error_fixture_le
    (V293_saved_error_mem self saved) 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z 602%Z
    50%positive 51%positive 52%positive 40%positive 61%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) 6 8 90%positive saved)
    as (Mf & Exec & Token & Pointer & Frame).
  all: try discriminate;
    try (unfold V293_error_fixture_ge,V293_error_fixture_le,V293_entry_fixture_ge,V293_entry_fixture_le;
      repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];reflexivity);
    try match goal with |- (_ < _)%nat => destruct self;cbn;lia end;
    try (rewrite LF by discriminate;assumption);
    try (rewrite Resolved,LF by discriminate;exact Slot).
  - intro IsSelf. repeat split; try assumption;
      try (unfold V293_error_fixture_ge,V293_error_fixture_le,V293_entry_fixture_ge,V293_entry_fixture_le;
        repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];reflexivity);
      try (rewrite LF by discriminate;assumption);
      try (change (0<=8)%Z;lia);try (change (8+50<=4294967295)%Z;lia).
    destruct Wo as [v Read]. exists v. rewrite V293_saved_error_outside by discriminate. exact Read.
  - intros k K. rewrite V293_saved_error_outside by discriminate. apply CW;exact K.
  - unfold V293_saved_error_mem. apply V293_fixture_saved_ie.
  - exists Mf. split;[exact Exec | ]. split;assumption.
Qed.

(* Single-factor physical counterexample: change only one byte in the saved
   block. Other bytes are unchanged. This is not a reachable C alias claim. *)
Theorem V293_saved_byte_alias_counterexample :
  let M := V293_fixture_put_bytes emp 61%positive 0%Z (encode_val Tint32 (Vint32 Int.one)) in
  V293_saved_ie M 61%positive true /\
  ~ V293_saved_ie (V293_put_byte M (61%positive,0%Z) 8) 61%positive true /\
  (forall c i, (c,i) <> (61%positive,0%Z) ->
    get (V293_put_byte M (61%positive,0%Z) 8) (c,i) = get M (c,i)).
Proof.
  cbn zeta. split; [exact (V293_fixture_saved_ie emp 61%positive true) | ]. split.
  - assert (Bytes : loadbytes
      (V293_put_byte (V293_fixture_put_bytes emp 61%positive 0%Z
        (encode_val Tint32 (Vint32 Int.one))) (61%positive,0%Z) 8)
      (61%positive,0%Z) (length (encode_val Tint32 (Vint32 (Int.repr 8)))) =
      Some (encode_val Tint32 (Vint32 (Int.repr 8)))).
    { apply V293_loadbytes_get.
      intros [ | [ | [ | [ | k]]]] K; try (rewrite encode_val_length in K;cbn in K;lia);
        exists true.
      - apply V293_put_byte_get_same.
      - rewrite V293_put_byte_other by discriminate.
        exact (V293_fixture_bytes_nth (encode_val Tint32 (Vint32 Int.one)) emp 61%positive 0%Z 1 ltac:(rewrite encode_val_length;cbn;lia)).
      - rewrite V293_put_byte_other by discriminate.
        exact (V293_fixture_bytes_nth (encode_val Tint32 (Vint32 Int.one)) emp 61%positive 0%Z 2 ltac:(rewrite encode_val_length;cbn;lia)).
      - rewrite V293_put_byte_other by discriminate.
        exact (V293_fixture_bytes_nth (encode_val Tint32 (Vint32 Int.one)) emp 61%positive 0%Z 3 ltac:(rewrite encode_val_length;cbn;lia)). }
    pose proof (f_equal (fun data => match data with
      | Some bytes => Some (decode_val Tint32 bytes) | None => None end) Bytes) as Read.
    change (load Tint32 (V293_put_byte (V293_fixture_put_bytes emp 61%positive 0%Z
        (encode_val Tint32 (Vint32 Int.one))) (61%positive,0%Z) 8) (61%positive,0%Z) =
      Some (decode_val Tint32 (encode_val Tint32 (Vint32 (Int.repr 8))))) in Read.
    rewrite type_val_mach_encode_val_decode_val in Read by reflexivity.
    intro Bad. unfold V293_saved_ie in Bad.
    assert (Some (Vint32 (Int.repr 8)) = Some (Vint32 Int.one)) by (etransitivity;[symmetry;exact Read|exact Bad]).
    discriminate.
  - intros. apply V293_put_byte_other. assumption.
Qed.

(* Checked MACRO abstraction at the boundary accepted by ADR-0001. This is
   NOT an execution rule for the raw sfexec, nor a verified C frontend.
   The local CPU_SR bytes are erased here; no byte-token simulation is claimed. *)
Require Import Coq.Relations.Relation_Operators.

Fixpoint V293_port_calls (enter exit : fid) (saved : var) (s : stmts) : option stmts :=
  match s with
  | scall f args =>
    if Z.eq_dec f enter then
      match args with
      | eaddrof (evar x) :: nil => if Z.eq_dec x saved then Some (sprim encrit) else None
      | _ => None
      end
    else if Z.eq_dec f exit then
      match args with
      | eaddrof (evar x) :: nil => if Z.eq_dec x saved then Some (sprim excrit) else None
      | _ => None
      end
    else Some s
  | sseq a b =>
    match V293_port_calls enter exit saved a, V293_port_calls enter exit saved b with
    | Some a', Some b' => Some (sseq a' b') | _, _ => None end
  | sif e a b =>
    match V293_port_calls enter exit saved a, V293_port_calls enter exit saved b with
    | Some a', Some b' => Some (sif e a' b') | _, _ => None end
  | sifthen e a =>
    match V293_port_calls enter exit saved a with
    | Some a' => Some (sifthen e a') | _ => None end
  | swhile e a =>
    match V293_port_calls enter exit saved a with
    | Some a' => Some (swhile e a') | _ => None end
  | scalle _ f _ => if Z.eq_dec f enter then None else if Z.eq_dec f exit then None else Some s
  | sfexec _ _ _ | salloc _ _ | sfree _ _ => None
  | _ => Some s
  end.
Definition V293_port_normalize enter exit saved s :=
  if Z.eq_dec enter exit then None else V293_port_calls enter exit saved s.

Definition V293_primitive_error (error : Z) : stmts :=
  sseq (sprim excrit) (srete (econst32 (Int.repr error))).
Definition V293_primitive_entry (table oldprio newprio ptcb current reserved : var) : stmts :=
  sseq
    (sseq (sifthen (eunop oppsite (V293_task_prio_null_test
        (earrayelem (evar table) (evar newprio)))) (V293_primitive_error 40))
      (sseq (V293_task_prio_self_read oldprio current)
        (sseq (V293_task_prio_lookup table oldprio ptcb)
          (sifthen (V293_task_prio_null_test (evar ptcb)) (V293_primitive_error 41)))))
    (sifthen (V293_task_prio_reserved_test ptcb reserved) (V293_primitive_error 67)).
Definition V293_raw_critical_prefix table oldprio newprio ptcb current reserved cpu_sr enter exit :=
  sseq (V293_task_prio_argument_guards oldprio newprio)
    (sseq (scall enter (eaddrof (evar cpu_sr)::nil))
      (V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit)).
Definition V293_primitive_critical_prefix table oldprio newprio ptcb current reserved :=
  sseq (V293_task_prio_argument_guards oldprio newprio)
    (sseq (sprim encrit) (V293_primitive_entry table oldprio newprio ptcb current reserved)).

Theorem V293_critical_prefix_normalization :
  forall table oldprio newprio ptcb current reserved cpu_sr enter exit,
  enter <> exit ->
  V293_port_normalize enter exit cpu_sr
    (V293_raw_critical_prefix table oldprio newprio ptcb current reserved cpu_sr enter exit) =
  Some (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved).
Proof.
  intros. unfold V293_port_normalize.
  destruct (Z.eq_dec enter exit); [contradiction | ].
  unfold V293_raw_critical_prefix,V293_primitive_critical_prefix,
    V293_task_prio_argument_guards,V293_task_prio_entry_reserved,
    V293_task_prio_entry_lookup,V293_task_prio_reserved_guard,
    V293_task_prio_reserved_error,V293_task_prio_self_read,V293_task_prio_lookup,
    V293_primitive_entry,V293_primitive_error.
  cbn [V293_port_calls].
  repeat destruct (Z.eq_dec _ _); congruence || reflexivity.
Qed.

Theorem V293_port_rejects_wrong_token : forall enter exit saved other,
  enter <> exit -> other <> saved ->
  V293_port_normalize enter exit saved (scall exit (eaddrof (evar other)::nil)) = None /\
  V293_port_normalize enter exit saved (scall exit (evar saved::nil)) = None /\
  V293_port_normalize enter enter saved (scall enter (eaddrof (evar saved)::nil)) = None.
Proof.
  intros. unfold V293_port_normalize. cbn [V293_port_calls].
  repeat destruct (Z.eq_dec _ _); intuition congruence.
Qed.

(* Standard reflexive/transitive closure of the EXISTING loststep. *)
Definition V293_local_steps P C st C' st' :=
  clos_refl_trans_1n (code * taskst)
    (fun a b => loststep P (fst a) (snd a) (fst b) (snd b)) (C,st) (C',st').
Lemma V293_local_refl : forall P C st, V293_local_steps P C st C st.
Proof. intros. constructor. Qed.
Lemma V293_local_cons : forall P C st C1 st1 C2 st2,
  loststep P C st C1 st1 -> V293_local_steps P C1 st1 C2 st2 ->
  V293_local_steps P C st C2 st2.
Proof. intros P C st C1 st1 C2 st2 Step Rest.
  unfold V293_local_steps in *. eapply rt1n_trans with (y:=(C1,st1)); [exact Step|exact Rest].
Qed.
Lemma V293_local_trans : forall P C st C1 st1 C2 st2,
  V293_local_steps P C st C1 st1 -> V293_local_steps P C1 st1 C2 st2 ->
  V293_local_steps P C st C2 st2.
Proof.
  unfold V293_local_steps. intros P C st C1 st1 C2 st2 A B.
  induction A; [exact B | ]. eapply rt1n_trans; eauto.
Qed.
Lemma V293_csteps_local : forall P C m C' m' ir au,
  cstepstar P C m C' m' -> V293_local_steps P C (m,ir,au) C' (m',ir,au).
Proof.
  intros P C m C' m' ir au E. induction E.
  - apply V293_local_refl.
  - eapply V293_local_cons; [apply ostc_step;exact H | exact IHE].
Qed.

(* Same program for both initial IE states; no saved-byte precondition and no
   external-call oracle. Only the elaborated prefix receives execution credit.
   cpu_sr is a legitimate distinct local resource; its bytes are erased, not
   claimed equal to the raw method-3 token. Init/allocation linking stays open. *)
Theorem V293_occupied_critical_return :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved cpu_sr b bo bn bs old new target,
  old < 256 -> (old < 12 \/ old = 255) -> new < 12 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le cpu_sr = Some (bs,Tint32) -> bs <> b ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some (Vptr target) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved) suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 40)))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c i, ~ In c (map fst (getaddr le)) -> get Mf (c,i) = get M (c,i)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved cpu_sr b bo bn bs old new target
    O Valid N Nt Gt Bo Bn Bs Apart Lo Ln Slot Call ND W.
  destruct (V293_entry_array_eval ge le M table newprio b bn new (Vptr target)
    Nt Gt Bn Ln ltac:(lia) Slot) as [T V].
  pose proof (proj2 (V293_entry_null_eval ge le M _ (Vptr target) T V
    (or_intror (ex_intro _ target eq_refl)))) as Test.
  destruct (V293_error_return_execution P
    (kseq (sseq (V293_task_prio_self_read oldprio current)
      (sseq (V293_task_prio_lookup table oldprio ptcb)
        (sifthen (V293_task_prio_null_test (evar ptcb)) (V293_primitive_error 41))))
      (kseq (sifthen (V293_task_prio_reserved_test ptcb reserved) (V293_primitive_error 67))
        (kseq suffix ks))) ge le caller M f body next 40 ltac:(cbn [callcont];exact Call) ND W)
    as (Mf & Return & Frame & Removed).
  exists Mf. split; [ | split;assumption].
  unfold V293_primitive_critical_prefix.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local.
    eapply (V293_task_prio_argument_accepts P _ ge le M oldprio newprio bo bn old new); eauto;lia. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply encrit_step;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  unfold V293_primitive_entry.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local. apply V293_entry_if_select with (flag:=true). exact Test. }
  unfold V293_primitive_error at 1.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply excrit_step;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  apply V293_csteps_local. exact Return.
Qed.

(* Physical non-vacuity, NOT a function-entry or initialization witness.
   The erased token bytes are deliberately 23 for BOTH initial IE states. *)
Definition V293_critical_fixture_le : env :=
  set (set (set emp 501%Z (51%positive,Tint8)) 502%Z (52%positive,Tint8))
    601%Z (61%positive,Tint32).
Definition V293_critical_fixture_mem (self : bool) : mem :=
  V293_fixture_put_bytes (V293_error_fixture_mem self 0) 61%positive 0%Z
    (encode_val Tint32 (Vint32 (Int.repr 23))).

Theorem V293_occupied_critical_witness : forall P self enabled ir,
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((V293_error_fixture_ge,V293_critical_fixture_le,V293_critical_fixture_mem self),
        ir,(enabled,nil,nil))
      (curs (sskip (Some (Vint32 (Int.repr 40)))),(kenil,kstop))
      ((V293_error_fixture_ge,emp,Mf),ir,(enabled,nil,nil)) /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load (Tptr V293_tcb_type) Mf (50%positive,24%Z) = Some (Vptr (90%positive,Int.zero)).
Proof.
  intros P self enabled ir.
  destruct (V293_error_fixture_resources self 0) as (Lo & Ln & Slot & Rest).
  assert (LF : forall tp c i, c <> 61%positive ->
    load tp (V293_critical_fixture_mem self) (c,i) = load tp (V293_error_fixture_mem self 0) (c,i)).
  { intros. apply V293_load_block_frame. intro j. unfold V293_critical_fixture_mem.
    apply V293_fixture_bytes_outside. left;assumption. }
  assert (Addresses : getaddr V293_critical_fixture_le =
    (51%positive,Tint8)::(52%positive,Tint8)::(61%positive,Tint32)::nil) by reflexivity.
  assert (ND : NoDup (map fst (getaddr V293_critical_fixture_le))).
  { rewrite Addresses. repeat constructor; cbn; intuition discriminate. }
  assert (W : forall c t, In (c,t) (getaddr V293_critical_fixture_le) ->
    V293_bytes_writable (V293_critical_fixture_mem self) c 0%Z (typelen t)).
  { intros c t I. rewrite Addresses in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst c t.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_critical_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      unfold V293_error_fixture_mem. rewrite V293_put_byte_other by discriminate.
      eexists. apply V293_put_byte_get_same.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_critical_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      unfold V293_error_fixture_mem. eexists. apply V293_put_byte_get_same.
    - intros k K. unfold V293_critical_fixture_mem. eexists. apply V293_fixture_bytes_nth.
      rewrite encode_val_length. exact K. }
  assert (Bind : get V293_critical_fixture_le 500%Z = None /\
    get V293_error_fixture_ge 500%Z = Some (50%positive,Tarray (Tptr V293_tcb_type) 13) /\
    get V293_critical_fixture_le 501%Z = Some (51%positive,Tint8) /\
    get V293_critical_fixture_le 502%Z = Some (52%positive,Tint8) /\
    get V293_critical_fixture_le 601%Z = Some (61%positive,Tint32)).
  { unfold V293_critical_fixture_le,V293_error_fixture_ge,V293_entry_fixture_ge.
    repeat split; repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity. }
  destruct Bind as (Nt & Gt & Bo & Bn & Bs).
  destruct (V293_occupied_critical_return P (kcall 700%Z sret emp kstop)
    V293_error_fixture_ge V293_critical_fixture_le emp (V293_critical_fixture_mem self)
    700%Z sret kstop (scall 999%Z nil) ir enabled nil nil
    500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 601%Z
    50%positive 51%positive 52%positive 61%positive (if self then 255 else 8) 6
    (90%positive,Int.zero)) as (Mf & Exec & Frame & Removed).
  - destruct self;lia.
  - destruct self;[right|left];reflexivity || lia.
  - lia.
  - exact Nt.
  - exact Gt.
  - exact Bo.
  - exact Bn.
  - exact Bs.
  - discriminate.
  - rewrite LF by discriminate. exact Lo.
  - rewrite LF by discriminate. exact Ln.
  - rewrite LF by discriminate. exact Slot.
  - reflexivity.
  - exact ND.
  - exact W.
  - exists Mf. split; [exact Exec | ]. split.
    + intros k K. apply Removed with Tint32;[rewrite Addresses;right;right;left;reflexivity|exact K].
    + split.
      * change (get Mf (51%positive,Z.of_nat 0) = None).
        apply Removed with Tint8;[rewrite Addresses;left;reflexivity|cbn;lia].
      * split.
        -- change (get Mf (52%positive,Z.of_nat 0) = None).
           apply Removed with Tint8;[rewrite Addresses;right;left;reflexivity|cbn;lia].
        -- etransitivity.
           ++ apply V293_load_block_frame. intro i. apply Frame. rewrite Addresses. cbn. intuition discriminate.
           ++ rewrite LF by discriminate. exact Slot.
Qed.

Require Import CertiOS.framework.proof.rulesoundlib.

(* Binding membership connects the actual writes to the local-free frame. *)
Lemma V293_binding_in_getaddr : forall le x b t,
  get le x = Some (b,t) -> In (b,t) (getaddr le).
Proof.
  intros le x b t B.
  destruct (eqdomenv_conse_pre le x (b,t) B) as (a & c & d & J & E & F).
  rewrite E. apply in_or_app. right. left. reflexivity.
Qed.

(* Stores preserve the writable permission, including bytes they overwrite. *)
Lemma V293_storebytes_preserves_writable : forall bytes M M' b i,
  storebytes M (b,i) bytes = Some M' ->
  forall c j v, get M (c,j) = Some (true,v) ->
    exists w, get M' (c,j) = Some (true,w).
Proof.
  intros bytes M M' b i Store c j v W.
  destruct (Pos.eq_dec c b) as [-> | D].
  - destruct (Z_lt_dec j i) as [L | L].
    + exists v. etransitivity; [apply (V293_storebytes_outside bytes M M' b i b j Store);right;left;exact L|exact W].
    + destruct (Z_le_dec (i+Z.of_nat (length bytes)) j) as [R | R].
      * exists v. etransitivity; [apply (V293_storebytes_outside bytes M M' b i b j Store);right;right;exact R|exact W].
      * exists (nth (Z.to_nat (j-i)) bytes Undef).
        assert (K : Z.to_nat (j-i) < length bytes).
        { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        pose proof (V293_storebytes_nth bytes M M' b i (Z.to_nat (j-i)) Store K) as Read.
        replace (i+Z.of_nat (Z.to_nat (j-i)))%Z with j in Read by (rewrite Z2Nat.id by lia;lia). exact Read.
  - exists v. etransitivity; [apply (V293_storebytes_outside bytes M M' b i c j Store);left;exact D|exact W].
Qed.

(* One actual SELF+lookup prefix for NULL and non-NULL values. No preloaded
   correct ptcb, different-slot premise, or execution/store oracle is supplied. *)
Theorem V293_resolve_lookup_resources :
  forall P ge le M table oldprio ptcb current b bo bc bcur bct base old curprio value,
  old < 256 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some value ->
  (value = Vnull \/ exists p, value = Vptr p) -> b <> bo -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Ml,
    (forall tail suffix, cstepstar P
      (curs (sseq (V293_task_prio_self_read oldprio current)
        (sseq (V293_task_prio_lookup table oldprio ptcb) suffix)),(kenil,tail)) (ge,le,M)
      (curs suffix,(kenil,tail)) (ge,le,Ml)) /\
    load (Tptr V293_tcb_type) Ml (bc,0%Z) = Some value /\
    (forall c j, c <> bo -> c <> bc -> get Ml (c,j) = get M (c,j)) /\
    (forall c j v, get M (c,j) = Some (true,v) -> exists w, get Ml (c,j) = Some (true,w)).
Proof.
  intros P ge le M table oldprio ptcb current b bo bc bcur bct base old curprio value
    O resolved R Nt Gt Bo Bc Lo Slot Cases Tbo CO Self CW.
  destruct (V293_entry_byte_tests ge le M oldprio bo old O Bo Lo) as [_ SelfTest].
  set (Ms := if old =? 255 then V293_put_byte M (bo,0%Z) curprio else M).
  assert (SelfStep : forall tail,
    cstepstar P (curs (V293_task_prio_self_read oldprio current),(kenil,tail)) (ge,le,M)
      (curs (sskip None),(kenil,tail)) (ge,le,Ms)).
  { intro tail. unfold V293_task_prio_self_read,Ms. destruct (old =? 255) eqn:S.
    - destruct (Self (proj1 (Nat.eqb_eq old 255) S)) as (Nc & Gc & Pc & Base & Limit & Prio & W).
      assert (CP : curprio < 256) by (unfold resolved in R;simpl in R;lia).
      destruct (V293_entry_current_prio_eval ge le M current bcur bct base curprio Nc Gc Pc Base Limit Prio) as [T V].
      eapply V293_rekey_if_execution with (flag:=true); [exact SelfTest| |discriminate].
      intros _. eapply V293_coordinate_local_assignment; eassumption.
    - eapply V293_rekey_if_execution with (flag:=false); [exact SelfTest|discriminate|reflexivity]. }
  assert (SF : forall c j, c <> bo -> get Ms (c,j) = get M (c,j)).
  { intros. unfold Ms. destruct (old =? 255); [apply V293_put_byte_other;congruence|reflexivity]. }
  assert (SW : forall c j v, get M (c,j) = Some (true,v) -> exists w, get Ms (c,j) = Some (true,w)).
  { intros c j v W. unfold Ms. destruct (old =? 255); [ | eauto].
    destruct (addr_eq_dec (c,j) (bo,0%Z)) as [E|D].
    - inversion E;subst. eexists. apply V293_put_byte_get_same.
    - exists v. rewrite V293_put_byte_other by exact D. exact W. }
  assert (Read : load Tint8 Ms (bo,0%Z) = Some (V293_byteval resolved)).
  { unfold Ms,resolved. destruct (old =? 255); [apply V293_put_byte_load;unfold resolved in R;simpl in R;lia|exact Lo]. }
  assert (SlotS : load (Tptr V293_tcb_type) Ms (b,(4*Z.of_nat resolved)%Z) = Some value).
  { etransitivity; [apply V293_load_block_frame;intro j;apply SF;exact Tbo|exact Slot]. }
  destruct (V293_storebytes_exists (encode_val (Tptr V293_tcb_type) value) Ms bc 0%Z) as [Ml Store].
  { rewrite encode_val_length. intros k K. rewrite SF by exact CO. apply CW;exact K. }
  assert (PF : forall c j, c <> bc -> get Ml (c,j) = get Ms (c,j)).
  { intros. eapply V293_storebytes_outside; [exact Store|left;assumption]. }
  assert (Pointer : load (Tptr V293_tcb_type) Ml (bc,0%Z) = Some value).
  { eapply V293_store_readback; [destruct Cases as [->|[[p i] ->]];reflexivity|exact Store]. }
  destruct (V293_entry_array_eval ge le Ms table oldprio b bo resolved value Nt Gt Bo Read R SlotS) as [T V].
  assert (Lookup : forall tail, cstepstar P (curs (V293_task_prio_lookup table oldprio ptcb),(kenil,tail)) (ge,le,Ms)
      (curs (sskip None),(kenil,tail)) (ge,le,Ml)).
  { intro tail. unfold V293_task_prio_lookup.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z); try eassumption.
    - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  exists Ml. split.
  - intros tail suffix. eapply V293_sequence_prefix_to; [exact SelfStep| ].
    eapply V293_sequence_prefix_to; [exact Lookup|apply c_stepstar0].
  - split; [exact Pointer| ]. split.
    + intros c j A B. rewrite PF by exact B. apply SF;exact A.
    + intros c j v W. destruct (SW c j v W) as [w Readable].
      eapply V293_storebytes_preserves_writable; eassumption.
Qed.

(* Stable error interface for the SAME elaborated program. absent=true selects
   NULL/41; false selects the reserved pointer/67. The return frees resources
   obtained from the original memory, transported through both actual writes.
   Raw sfexec/port simulation and whole-function/concurrent safety stay open. *)
Theorem V293_lookup_error_critical_return :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved b bo bn bc bcur bct base old new curprio br absent,
  old < 256 -> (old < 12 \/ old = 255) -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  (absent = false -> get le reserved = None /\ get ge reserved = Some (br,Tint8)) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) =
    Some (if absent then Vnull else Vptr (br,Int.zero)) ->
  b <> bo -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved) suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr (if absent then 41 else 67))))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c j, ~ In c (map fst (getaddr le)) -> get Mf (c,j) = get M (c,j)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved b bo bn bc bcur bct base old new curprio br absent
    O Valid N resolved R Nt Gt Bo Bn Bc Reserved Lo Ln Empty Slot Tbo CO Self Call ND W.
  assert (Cases : (if absent then Vnull else Vptr (br,Int.zero)) = Vnull \/
    exists p, (if absent then Vnull else Vptr (br,Int.zero)) = Vptr p).
  { destruct absent; [left;reflexivity|right;eauto]. }
  destruct (V293_resolve_lookup_resources P ge le M table oldprio ptcb current b bo bc bcur bct base old curprio
    (if absent then Vnull else Vptr (br,Int.zero)) O R Nt Gt Bo Bc Lo Slot Cases Tbo CO Self)
    as (Ml & Lookup & Pointer & Frame & Permissions).
  { apply (W bc (Tptr V293_tcb_type)). apply V293_binding_in_getaddr with ptcb. exact Bc. }
  assert (WL : forall c t, In (c,t) (getaddr le) -> V293_bytes_writable Ml c 0%Z (typelen t)).
  { intros c t I k K. destruct (W c t I k K) as [v Read]. eapply Permissions;exact Read. }
  destruct (V293_entry_array_eval ge le M table newprio b bn new Vnull Nt Gt Bn Ln ltac:(lia) Empty) as [T V].
  pose proof (proj2 (V293_entry_null_eval ge le M _ Vnull T V (or_introl eq_refl))) as TargetTest.
  assert (NullTest : evalval (V293_task_prio_null_test (evar ptcb)) (ge,le,Ml) =
    Some (Vint32 (if absent then Int.one else Int.zero))).
  { unfold V293_task_prio_null_test. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite Bc. cbn beta iota. rewrite Pointer. destruct absent;reflexivity. }
  set (tail := if absent then
    kseq (sifthen (V293_task_prio_reserved_test ptcb reserved) (V293_primitive_error 67)) (kseq suffix ks)
    else kseq suffix ks).
  assert (Entry : cstepstar P
    (curs (V293_primitive_entry table oldprio newprio ptcb current reserved),(kenil,kseq suffix ks)) (ge,le,M)
    (curs (V293_primitive_error (if absent then 41 else 67)),(kenil,tail)) (ge,le,Ml)).
  { unfold V293_primitive_entry.
    eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_sequence_prefix_to with (M1:=M).
    - intro pending. eapply V293_rekey_if_execution with (flag:=false); [exact TargetTest|discriminate|reflexivity].
    - eapply V293_cstepstar_trans; [apply Lookup| ].
      destruct absent; unfold tail; cbn beta iota in *.
      + apply V293_entry_if_select with (flag:=true). exact NullTest.
      + eapply V293_cstepstar_trans.
        { eapply V293_rekey_if_execution with (flag:=false); [exact NullTest|discriminate|reflexivity]. }
        eapply c_stepstarn. { eapply stmt_step; [reflexivity|apply sskip_step]. }
        apply V293_entry_if_select with (flag:=true).
        destruct (Reserved eq_refl) as [Nr Gr].
        pose proof (V293_reserved_test_eval ge le Ml ptcb reserved bc br (Vptr (br,Int.zero))
          Bc Pointer (or_intror (ex_intro _ (br,Int.zero) eq_refl)) Nr Gr) as Test.
        rewrite (proj2 (V293_reserved_matches_pointer br (br,Int.zero)) eq_refl) in Test. exact Test. }
  destruct (V293_error_return_execution P tail ge le caller Ml f body next (if absent then 41 else 67)
    ltac:(unfold tail;destruct absent;cbn [callcont];exact Call) ND WL) as (Mf & Return & FreeFrame & Removed).
  exists Mf. split.
  - unfold V293_primitive_critical_prefix.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply (V293_task_prio_argument_accepts P _ ge le M oldprio newprio bo bn old new);eauto;lia. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. exact Entry. }
    unfold V293_primitive_error at 1.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    apply V293_csteps_local. exact Return.
  - split; [ | exact Removed]. intros c j Outside.
    rewrite FreeFrame by exact Outside. apply Frame; intro E; subst c;apply Outside;
      apply in_map_iff.
    + exists (bo,Tint8). split; [reflexivity|apply V293_binding_in_getaddr with oldprio;exact Bo].
    + exists (bc,Tptr V293_tcb_type). split; [reflexivity|apply V293_binding_in_getaddr with ptcb;exact Bc].
Qed.

Definition V293_lookup_critical_fixture_mem (self absent : bool) : mem :=
  V293_fixture_put_bytes (V293_error_fixture_mem self (if absent then 1 else 2)) 61%positive 0%Z
    (encode_val Tint32 (Vint32 (Int.repr 23))).

(* Absent permits old=new=8; reserved uses old=8/new=6. Both execute exactly
   the same prefix, start with ptcb=70 (neither NULL nor reserved=90), and have
   token bytes=23 independently of enabled. No initialization credit. *)
Theorem V293_lookup_error_critical_witness : forall P self absent enabled ir,
  load (Tptr V293_tcb_type) (V293_lookup_critical_fixture_mem self absent) (40%positive,0%Z) =
    Some (Vptr (70%positive,Int.zero)) /\
  load Tint32 (V293_lookup_critical_fixture_mem self absent) (61%positive,0%Z) =
    Some (Vint32 (Int.repr 23)) /\
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((V293_error_fixture_ge,V293_error_fixture_le,V293_lookup_critical_fixture_mem self absent),
        ir,(enabled,nil,nil))
      (curs (sskip (Some (Vint32 (Int.repr (if absent then 41 else 67))))),(kenil,kstop))
      ((V293_error_fixture_ge,emp,Mf),ir,(enabled,nil,nil)) /\
    (forall k, k < 4 -> get Mf (40%positive,Z.of_nat k) = None /\ get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load (Tptr V293_tcb_type) Mf (50%positive,32%Z) =
      Some (if absent then Vnull else Vptr (90%positive,Int.zero)).
Proof.
  intros P self absent enabled ir.
  destruct (V293_error_fixture_resources self (if absent then 1 else 2))
    as (Lo & Ln & NewSlot & OldSlot & Current & Prio & Initial & WO & CW).
  assert (LF : forall tp c j, c <> 61%positive ->
    load tp (V293_lookup_critical_fixture_mem self absent) (c,j) =
      load tp (V293_error_fixture_mem self (if absent then 1 else 2)) (c,j)).
  { intros. apply V293_load_block_frame. intro k. unfold V293_lookup_critical_fixture_mem.
    apply V293_fixture_bytes_outside. left;assumption. }
  assert (Addresses : getaddr V293_error_fixture_le =
    (40%positive,Tptr V293_tcb_type)::(51%positive,Tint8)::(52%positive,Tint8)::(61%positive,Tint32)::nil) by reflexivity.
  assert (ND : NoDup (map fst (getaddr V293_error_fixture_le))).
  { rewrite Addresses. repeat constructor;cbn;intuition discriminate. }
  assert (W : forall c t, In (c,t) (getaddr V293_error_fixture_le) ->
    V293_bytes_writable (V293_lookup_critical_fixture_mem self absent) c 0%Z (typelen t)).
  { intros c t I. rewrite Addresses in I.
    destruct I as [E|[E|[E|[E|F]]]];try contradiction;inversion E;subst c t.
    - intros k K. unfold V293_lookup_critical_fixture_mem.
      rewrite V293_fixture_bytes_outside by (left;discriminate). apply CW;exact K.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_lookup_critical_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      unfold V293_error_fixture_mem. rewrite V293_put_byte_other by discriminate.
      eexists. apply V293_put_byte_get_same.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_lookup_critical_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      unfold V293_error_fixture_mem. eexists. apply V293_put_byte_get_same.
    - intros k K. unfold V293_lookup_critical_fixture_mem. eexists. apply V293_fixture_bytes_nth.
      rewrite encode_val_length. exact K. }
  assert (Bind : get V293_error_fixture_le 500%Z = None /\
    get V293_error_fixture_ge 500%Z = Some (50%positive,Tarray (Tptr V293_tcb_type) 13) /\
    get V293_error_fixture_le 501%Z = Some (51%positive,Tint8) /\
    get V293_error_fixture_le 502%Z = Some (52%positive,Tint8) /\
    get V293_error_fixture_le 400%Z = Some (40%positive,Tptr V293_tcb_type) /\
    get V293_error_fixture_le 603%Z = None /\
    get V293_error_fixture_ge 603%Z = Some (90%positive,Tint8) /\
    get V293_error_fixture_le 750%Z = None /\
    get V293_error_fixture_ge 750%Z = Some (80%positive,Tptr V293_tcb_type)).
  { unfold V293_error_fixture_le,V293_error_fixture_ge,V293_entry_fixture_le,V293_entry_fixture_ge.
    repeat split;repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate];reflexivity. }
  destruct Bind as (Nt & Gt & Bo & Bn & Bc & Nr & Gr & Nc & Gc).
  split; [rewrite LF by discriminate;exact Initial| ]. split.
  { unfold V293_lookup_critical_fixture_mem. apply V293_fixture_encoded_load. reflexivity. }
  destruct (V293_lookup_error_critical_return P (kcall 700%Z sret emp kstop)
    V293_error_fixture_ge V293_error_fixture_le emp (V293_lookup_critical_fixture_mem self absent)
    700%Z sret kstop (scall 999%Z nil) ir enabled nil nil
    500%Z 501%Z 502%Z 400%Z 750%Z 603%Z
    50%positive 51%positive 52%positive 40%positive 80%positive 41%positive 8%Z
    (if self then 255 else 8) (if absent then 8 else 6) 8 90%positive absent)
    as (Mf & Exec & Frame & Removed).
  - destruct self;lia.
  - destruct self;[right|left];reflexivity || lia.
  - destruct absent;lia.
  - destruct self;cbn;lia.
  - exact Nt.
  - exact Gt.
  - exact Bo.
  - exact Bn.
  - exact Bc.
  - intros _. split;assumption.
  - rewrite LF by discriminate. exact Lo.
  - rewrite LF by discriminate. destruct absent;exact Ln.
  - rewrite LF by discriminate. destruct absent;[exact OldSlot|exact NewSlot].
  - rewrite LF by discriminate. destruct self,absent;exact OldSlot.
  - discriminate.
  - discriminate.
  - intros _. repeat split;try assumption;try (change (0<=8)%Z;lia);try (change (8+50<=4294967295)%Z;lia).
    + rewrite LF by discriminate. exact Current.
    + rewrite LF by discriminate. exact Prio.
    + unfold V293_lookup_critical_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate). exact WO.
  - reflexivity.
  - exact ND.
  - exact W.
  - exists Mf. split; [exact Exec| ]. split.
    + intros k K. split.
      * apply Removed with (Tptr V293_tcb_type); [rewrite Addresses;left;reflexivity|exact K].
      * apply Removed with Tint32; [rewrite Addresses;right;right;right;left;reflexivity|exact K].
    + split.
      * change (get Mf (51%positive,Z.of_nat 0) = None).
        apply Removed with Tint8; [rewrite Addresses;right;left;reflexivity|cbn;lia].
      * split.
        -- change (get Mf (52%positive,Z.of_nat 0) = None).
           apply Removed with Tint8; [rewrite Addresses;right;right;left;reflexivity|cbn;lia].
        -- etransitivity.
           ++ apply V293_load_block_frame. intro j. apply Frame. rewrite Addresses. cbn. intuition discriminate.
           ++ rewrite LF by discriminate. destruct absent;exact OldSlot.
Qed.

(* Complete a return whose expression has ALREADY been evaluated by a guard.
   Do not re-evaluate srete or assume that free/caller restoration succeeded. *)
Lemma V293_evaluated_return_execution : forall P ks ge le caller M f body next v,
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists M',
    cstepstar P (curs (sskip (Some v)),(kenil,kret ks)) (ge,le,M)
      (curs (sskip (Some v)),(kenil,next)) (ge,caller,M') /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get M' (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get M' (b,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next v Call ND W.
  destruct (V293_sfree_construct_execution (getaddr le) P ks ge le M (Some v) ND W)
    as (M' & Free & Frame & Removed).
  exists M'. split.
  - eapply c_stepstarn.
    { eapply stmt_step; [reflexivity| ].
      eapply (sretv_step P f _ body); [reflexivity|rewrite Call;discriminate|reflexivity]. }
    eapply V293_cstepstar_trans; [exact Free| ].
    eapply c_stepstarn.
    { eapply stmt_step; [reflexivity| ]. eapply sfreeend_step; eassumption || reflexivity. }
    apply c_stepstar0.
  - split;assumption.
Qed.

(* A stable early-return interface on the SAME prefix as 40/41/67.
   Invalid arguments return BEFORE encrit: all interrupt state is untouched.
   No table/current/reserved/cpu_sr binding or external-call body is needed. *)
Theorem V293_invalid_critical_return :
  forall P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved bo bn old new,
  old < 256 -> new < 256 ->
  ((12 <= old /\ old <> 255) \/ 12 <= new) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved) suffix),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 42)))),(kenil,next))
      ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall c i, ~ In c (map fst (getaddr le)) -> get Mf (c,i) = get M (c,i)) /\
    (forall c t k, In (c,t) (getaddr le) -> k < typelen t -> get Mf (c,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M f body next suffix ir enabled si ci
    table oldprio newprio ptcb current reserved bo bn old new O N Bad Bo Bn Lo Ln Call ND W.
  set (tail := kseq (sseq (sprim encrit)
    (V293_primitive_entry table oldprio newprio ptcb current reserved)) (kseq suffix ks)).
  assert (Rejected : exists rejected,
    cstepstar P (curs (V293_task_prio_argument_guards oldprio newprio),(kenil,tail)) (ge,le,M)
      (curs (sskip (Some (V293_byteval 42))),(kenil,kret rejected)) (ge,le,M) /\
    callcont rejected = Some (kcall f body caller next)).
  { pose proof (V293_task_prio_argument_execution P tail ge le M oldprio newprio bo bn old new
      O N Bo Bn Lo Ln) as E.
    unfold V293_argument_stop in E.
    destruct (old <? 12) eqn:Old.
    - apply Nat.ltb_lt in Old. destruct (new <? 12) eqn:New.
      + apply Nat.ltb_lt in New. destruct Bad as [[B _]|B];lia.
      + exists tail. split; [exact E|unfold tail;cbn;exact Call].
    - destruct (old =? 255) eqn:Self.
      + apply Nat.eqb_eq in Self. destruct (new <? 12) eqn:New.
        * apply Nat.ltb_lt in New. destruct Bad as [[_ B]|B];lia.
        * exists tail. split; [exact E|unfold tail;cbn;exact Call].
      + eexists. split; [exact E|unfold tail;cbn;exact Call]. }
  destruct Rejected as (rejected & Guards & ReturnCall).
  destruct (V293_evaluated_return_execution P rejected ge le caller M f body next
    (V293_byteval 42) ReturnCall ND W) as (Mf & Return & Frame & Removed).
  exists Mf. split.
  - eapply V293_local_trans.
    + apply V293_csteps_local.
      unfold V293_primitive_critical_prefix.
      eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
      exact Guards.
    + apply V293_csteps_local. exact Return.
  - split;assumption.
Qed.

(* Only local arguments/saved bytes and one nonlocal sentinel. No global
   symbol bindings: invalid guards must not inspect the shared task table. *)
Definition V293_invalid_critical_fixture_mem old new : mem :=
  V293_put_byte (V293_put_byte
    (V293_fixture_put_bytes (V293_put_byte emp (90%positive,0%Z) 23)
      61%positive 0%Z (encode_val Tint32 (Vint32 (Int.repr 23))))
    (51%positive,0%Z) old) (52%positive,0%Z) new.

Theorem V293_invalid_critical_witness : forall P old new enabled ir si ci,
  old < 256 -> new < 256 -> ((12 <= old /\ old <> 255) \/ 12 <= new) ->
  exists Mf,
    V293_local_steps P
      (curs (sseq (V293_primitive_critical_prefix 500%Z 501%Z 502%Z 400%Z 750%Z 603%Z)
        (scall 999%Z nil)),(kenil,kcall 700%Z sret emp kstop))
      ((emp,V293_critical_fixture_le,V293_invalid_critical_fixture_mem old new),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 (Int.repr 42)))),(kenil,kstop))
      ((emp,emp,Mf),ir,(enabled,si,ci)) /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    get Mf (51%positive,0%Z) = None /\ get Mf (52%positive,0%Z) = None /\
    load Tint8 Mf (90%positive,0%Z) = Some (V293_byteval 23).
Proof.
  intros P old new enabled ir si ci O N Bad.
  assert (Addresses : getaddr V293_critical_fixture_le =
    (51%positive,Tint8)::(52%positive,Tint8)::(61%positive,Tint32)::nil) by reflexivity.
  assert (ND : NoDup (map fst (getaddr V293_critical_fixture_le))).
  { rewrite Addresses. repeat constructor;cbn;intuition discriminate. }
  assert (W : forall c t, In (c,t) (getaddr V293_critical_fixture_le) ->
    V293_bytes_writable (V293_invalid_critical_fixture_mem old new) c 0%Z (typelen t)).
  { intros c t I. rewrite Addresses in I.
    destruct I as [E|[E|[E|F]]];try contradiction;inversion E;subst c t.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_invalid_critical_fixture_mem. rewrite V293_put_byte_other by discriminate.
      eexists. apply V293_put_byte_get_same.
    - intros k K. cbn in K. assert (k=0) by lia. subst k.
      unfold V293_invalid_critical_fixture_mem. eexists. apply V293_put_byte_get_same.
    - intros k K. unfold V293_invalid_critical_fixture_mem.
      repeat rewrite V293_put_byte_other by discriminate.
      eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length. exact K. }
  assert (Bo : get V293_critical_fixture_le 501%Z = Some (51%positive,Tint8)) by reflexivity.
  assert (Bn : get V293_critical_fixture_le 502%Z = Some (52%positive,Tint8)) by reflexivity.
  assert (Lo : load Tint8 (V293_invalid_critical_fixture_mem old new) (51%positive,0%Z) =
    Some (V293_byteval old)).
  { unfold V293_invalid_critical_fixture_mem.
    rewrite V293_put_byte_other_load by discriminate. apply V293_put_byte_load. exact O. }
  assert (Ln : load Tint8 (V293_invalid_critical_fixture_mem old new) (52%positive,0%Z) =
    Some (V293_byteval new)).
  { unfold V293_invalid_critical_fixture_mem. apply V293_put_byte_load. exact N. }
  destruct (V293_invalid_critical_return P (kcall 700%Z sret emp kstop)
    emp V293_critical_fixture_le emp (V293_invalid_critical_fixture_mem old new)
    700%Z sret kstop (scall 999%Z nil) ir enabled si ci
    500%Z 501%Z 502%Z 400%Z 750%Z 603%Z 51%positive 52%positive old new
    O N Bad Bo Bn Lo Ln eq_refl ND W) as (Mf & Exec & Frame & Removed).
  exists Mf. split; [exact Exec| ]. split.
  - intros k K. apply Removed with Tint32; [rewrite Addresses;right;right;left;reflexivity|exact K].
  - split.
    + change (get Mf (51%positive,Z.of_nat 0) = None).
      apply Removed with Tint8; [rewrite Addresses;left;reflexivity|cbn;lia].
    + split.
      * change (get Mf (52%positive,Z.of_nat 0) = None).
        apply Removed with Tint8; [rewrite Addresses;right;left;reflexivity|cbn;lia].
      * etransitivity.
        -- apply V293_load_block_frame. intro j. apply Frame. rewrite Addresses. cbn. intuition discriminate.
        -- unfold V293_invalid_critical_fixture_mem.
           repeat rewrite V293_put_byte_other_load by discriminate.
           etransitivity.
           ++ apply V293_load_block_frame. intro j. apply V293_fixture_bytes_outside. left;discriminate.
           ++ apply V293_put_byte_load. lia.
Qed.

(* Successful path: original-memory resources, actual stores, actual excrit. *)
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Import ListNotations.
Local Opaque HalfPermMap.set.
Theorem V293_primitive_entry_success :
  forall P ks ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct base old new curprio next br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  next <> (br,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
  resolved <> new /\
  cstepstar P (curs (V293_primitive_entry table oldprio newprio ptcb current reserved),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  V293_bytes_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct base old new curprio next br O N resolved R Nt Gt Bo Bn Bc Lo Ln Empty Slot
    Tbo Tbc Onew Cnew CO Self Nr Gr Token CW.
  assert (Different : resolved <> new).
  { intro E. rewrite E in Slot. rewrite Empty in Slot. discriminate. }
  destruct (V293_task_prio_resolve_execution P ge le M oldprio current bo bcur bct base
    old curprio O R Bo Lo Self) as (Ms & SelfStep & ResolvedRead & SF).
  assert (SL : forall tp c i, c <> bo -> load tp Ms (c,i) = load tp M (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intros j. apply SF; exact D. }
  assert (SlotS : load (Tptr V293_tcb_type) Ms (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next)).
  { rewrite SL by congruence. exact Slot. }
  assert (W : V293_bytes_writable Ms bc 0%Z 4).
  { intros k K. unfold V293_bytes_writable in CW. rewrite SF by exact CO. apply CW; exact K. }
  destruct (V293_storebytes_exists (encode_val (Tptr V293_tcb_type) (Vptr next)) Ms bc 0%Z)
    as [Mf Store].
  { rewrite encode_val_length. exact W. }
  assert (PF : forall c i, c <> bc -> get Mf (c,i) = get Ms (c,i)).
  { intros c i D. eapply V293_storebytes_outside; [exact Store|left;exact D]. }
  assert (PL : forall tp c i, c <> bc -> load tp Mf (c,i) = load tp Ms (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intro j. apply PF; exact D. }
  assert (Pointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)).
  { eapply V293_store_readback; [reflexivity|exact Store]. }
  destruct (V293_entry_array_eval ge le M table newprio b bn new Vnull Nt Gt Bn Ln ltac:(lia) Empty)
    as [NewType NewValue].
  assert (TargetTest : evalval (eunop oppsite (V293_task_prio_null_test
    (earrayelem (evar table) (evar newprio)))) (ge,le,M) = Some (Vint32 Int.zero)).
  { apply (proj2 (V293_entry_null_eval ge le M _ Vnull NewType NewValue (or_introl eq_refl))). }
  destruct (V293_entry_array_eval ge le Ms table oldprio b bo resolved (Vptr next)
    Nt Gt Bo ResolvedRead ltac:(lia) SlotS) as [OldType OldValue].
  assert (LookupStep : forall tail,
    cstepstar P (curs (V293_task_prio_lookup table oldprio ptcb),(kenil,tail)) (ge,le,Ms)
      (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_task_prio_lookup.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z);
      try eassumption.
    - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  assert (NullTest : evalval (V293_task_prio_null_test (evar ptcb)) (ge,le,Mf) = Some (Vint32 Int.zero)).
  { unfold V293_task_prio_null_test. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite Bc. cbn beta iota. rewrite Pointer. destruct next; reflexivity. }
  assert (ReservedTest : evalval (V293_task_prio_reserved_test ptcb reserved)
    (ge,le,Mf) = Some (Vint32 Int.zero)).
  { pose proof (V293_reserved_test_eval ge le Mf ptcb reserved bc br (Vptr next)
      Bc Pointer (or_intror (ex_intro _ next eq_refl)) Nr Gr) as E.
    assert (F : V293_reserved_matches br (Vptr next) = false).
    { destruct (V293_reserved_matches br (Vptr next)) eqn:Choice; [ |reflexivity].
      apply V293_reserved_matches_pointer in Choice. contradiction. }
    rewrite F in E. exact E. }
  exists Mf. split; [exact Different| ]. split.
  - unfold V293_primitive_entry.
    eapply V293_rekey_sequence_execution with (M1:=Mf).
    + intro tail. eapply V293_rekey_sequence_execution with (M1:=M).
      * intro tail'. eapply V293_rekey_if_execution with (flag:=false); [exact TargetTest|discriminate|reflexivity].
      * eapply V293_rekey_sequence_execution with (M1:=Ms); [exact SelfStep| ].
        eapply V293_rekey_sequence_execution with (M1:=Mf); [exact LookupStep| ].
        eapply V293_rekey_if_execution with (flag:=false); [exact NullTest|discriminate|reflexivity].
    + eapply V293_rekey_if_execution with (flag:=false); [exact ReservedTest|discriminate|reflexivity].
  - split; [rewrite PL by congruence; exact ResolvedRead| ].
    split; [rewrite PL,SL by congruence; exact Ln| ].
    split; [exact Pointer| ]. split; [rewrite PL by congruence; exact SlotS| ].
    split; [rewrite PL,SL by congruence; exact Empty| ]. split.
    + intros k K. exists (nth k (encode_val (Tptr V293_tcb_type) (Vptr next)) Undef).
      eapply V293_storebytes_nth; [exact Store|rewrite encode_val_length;exact K].
    + intros c i A B. rewrite PF by exact B. apply SF; exact A.
Qed.


(* Same explicit interrupt abstraction as the four errors; stop BEFORE the
   scheduler call. The public roots below derive Entry and Update from the
   original memory, rather than expose these composition premises to callers. *)
Definition V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved :=
  sseq (V293_primitive_critical_prefix table oldprio newprio ptcb current reserved)
    (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi)
      (sprim excrit)).

Lemma V293_success_segment_execution :
  forall P ks ge le M Ma Mh ir enabled si ci table oldprio newprio ptcb
    rows group yo yn xo xn byo byn pevent xi current reserved bo bn initial new,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  cstepstar P (curs (V293_primitive_entry table oldprio newprio ptcb current reserved),
    (kenil,kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi)
      (sprim excrit)) ks)) (ge,le,M) (curs (sskip None),
    (kenil,kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi)
      (sprim excrit)) ks)) (ge,le,Ma) ->
  cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,kseq (sprim excrit) ks)) (ge,le,Ma)
    (curs (sskip None),(kenil,kseq (sprim excrit) ks)) (ge,le,Mh) ->
  V293_local_steps P
    (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)).
Proof.
  intros P ks ge le M Ma Mh ir enabled si ci table oldprio newprio ptcb
    rows group yo yn xo xn byo byn pevent xi current reserved bo bn initial new
    O Valid N Bo Bn Lo Ln Entry Update.
  unfold V293_primitive_success_update,V293_primitive_critical_prefix.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local.
    eapply (V293_task_prio_argument_accepts P _ ge le M oldprio newprio bo bn initial new); eauto;lia. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply encrit_step;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_trans. { apply V293_csteps_local. exact Entry. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans. { apply V293_csteps_local. exact Update. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply excrit_step;reflexivity. }
  apply V293_local_refl.
Qed.

Theorem V293_critical_null_update_execution :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_primitive_entry_success P
    (kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) (sprim excrit)) ks)
    ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some Vnull /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_null_update_execution P (kseq (sprim excrit) ks) ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & Read & OutPointer & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - eapply V293_success_segment_execution with (Ma:=Ma) (bo:=bo) (bn:=bn) (initial:=initial) (new:=new); eassumption.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ].
    split; [exact Read | ]. split; [exact OutPointer | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + intros c i OB PC A B C D E F G J NY NI NBY NBX.
      rewrite Frame by assumption. apply EntryFrame; assumption.
Qed.


Theorem V293_critical_event_update_execution :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  V293_local_steps P (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_primitive_entry_success P
    (kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) (sprim excrit)) ks)
    ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
    V293_event_bitmap_loads Ma be ebase elo ehi (V293_ready_group elo ehi) /\
    V293_event_bitmap_writable Ma be ebase /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_event_bitmap_loads,V293_event_bitmap_writable,V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & AELoads & AEW & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_update_execution P (kseq (sprim excrit) ks) ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit AELoads AEW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & Exec & Updated & Ready & Table & OldSlot & NewSlot & EventOut & Read & OutPointer & Writable & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  - eapply V293_success_segment_execution with (Ma:=Ma) (bo:=bo) (bn:=bn) (initial:=initial) (new:=new); eassumption.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact EventOut | ].
    split; [exact Read | ]. split; [exact OutPointer | ]. split; [exact Writable | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + intros c i OB PC A B C D E F G H' J NY NI NBY NBX.
      rewrite Frame by assumption. apply EntryFrame; assumption.
Qed.


(* Physical success entries: NULL ptcb and stale coordinates, not init or reachable shared state. *)
Local Ltac entry_update_bind :=
  unfold V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,
    V293_event_fixture_le,V293_prefix_fixture_ge,V293_prefix_fixture_le,
    V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity.
Local Ltac entry_update_get :=
  unfold V293_tcb_update_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].
Local Ltac entry_update_load :=
  unfold V293_tcb_update_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; lia.

Theorem V293_critical_null_update_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks ir enabled si ci,
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_null_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_null_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  V293_local_steps P (curs (V293_primitive_success_update
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z),(kenil,ks))
    ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_null_fixture_mem self live elo ehi),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive (if live then 80 else 16) 0 1 /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some Vnull /\
  load (Tptr V293_event_type) Mh (70%positive,0%Z) = Some Vnull /\
  (forall i, get Mh (72%positive,i) = get (V293_entry_null_fixture_mem self live elo ehi) (72%positive,i)).
Proof.
  intros self live elo ehi EL EH P ks ir enabled si ci.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_null_fixture_mem self live elo ehi).
  assert (CF : forall c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some Vnull).
  { unfold M,V293_entry_null_fixture_mem. apply V293_fixture_encoded_load. reflexivity. }
  assert (HighByte : forall i, (40 <= i)%Z ->
    load Tint8 M (41%positive,i) = load Tint8 (V293_entry_update_fixture_mem self live elo ehi) (41%positive,i)).
  { intros i I. unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_entry_update_fixture_mem self live elo ehi) M).
    - reflexivity.
    - intros k K. unfold M. apply V293_entry_null_fixture_outside. right; right; lia. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads. repeat split; rewrite HighByte by lia;
    apply (eq_trans (V293_load_block_frame _ _ _ _ _ (fun i => V293_entry_update_fixture_frame self live elo ehi 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))));
    unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; entry_update_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_null_fixture_outside by (right; right; lia); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; entry_update_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8))).
  { rewrite (V293_load_block_frame _ (V293_entry_update_fixture_mem self live elo ehi) M 51%positive 0%Z (fun i => V293_entry_null_fixture_outside self live elo ehi 51%positive i ltac:(left; discriminate))). unfold V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct self; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>41%positive -> c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). unfold V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite HighByte by lia. rewrite (V293_load_block_frame _ _ _ 41%positive 58%Z
      (fun i => V293_entry_update_fixture_frame self live elo ehi 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
    unfold V293_coordinate_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate. entry_update_load. }
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_critical_null_update_execution P ks V293_entry_update_fixture_ge V293_tcb_update_fixture_le
    M ir enabled si ci 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) (if self then 255 else 8) 6 V293_prefix_fixture_entries
    600%Z 70%positive 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 80%positive 41%positive 8%Z 99%positive 8)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & Read & Pointer & InternalEvent & Untouched & Frame).
  all: try rewrite Resolved; try assumption; try discriminate; try (entry_update_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<12); lia); try (change (16<256); lia);
    try (destruct live; lia); try (destruct self; cbn; lia);
    try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear; lia)).
  - change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear; lia)).
  - intro IsSelf. repeat split; try (entry_update_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists (V293_tcb_update_memory Mg 41%positive 8%Z 6). rewrite Resolved in *.
    split; [exact Null | ]. split.
    + intros c I. rewrite LF by (clear - I; cbn in I; intuition congruence).
      apply V293_coordinate_fixture_stale. clear - I; cbn in I; intuition congruence.
    + split; [exact Exec | ]. split; [exact Updated | ].
      split; [destruct live; exact FinalLoads | ].
      split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact InternalEvent | ]. split; [exact Read | ]. intro i. apply Frame; discriminate.
Qed.


Theorem V293_critical_event_update_witness : forall self live elo ehi,
  elo < 256 -> ehi < 256 -> forall P ks ir enabled si ci,
  exists Mh,
  load (Tptr V293_tcb_type) (V293_entry_update_fixture_mem self live elo ehi)
    (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_entry_update_fixture_mem self live elo ehi) (c,0%Z) = Some (V293_byteval 255)) /\
  V293_local_steps P (curs (V293_primitive_success_update
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z
    750%Z 900%Z),(kenil,ks))
    ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,V293_entry_update_fixture_mem self live elo ehi),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mh 30%positive 31%positive (if live then 80 else 16) 0 1 /\
  V293_event_bitmap_loads Mh 72%positive 5%Z
    (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))
    (V293_ready_group (fst (V293_ready_rekey_rows elo ehi 8 6)) (snd (V293_ready_rekey_rows elo ehi 8 6))) /\
  V293_table_loads V293_tcb_type Mh 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull) (Vptr (41%positive,Int.repr 8))) /\
  load (Tptr V293_tcb_type) Mh (50%positive,32%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (50%positive,24%Z) = Some (Vptr (41%positive,Int.repr 8)) /\
  load (Tcom_ptr 411%Z) Mh (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)).
Proof.
  intros self live elo ehi EL EH P ks ir enabled si ci.
  destruct (V293_prefix_event_nonnull_entry live elo ehi EL EH)
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_update_fixture_mem self live elo ehi).
  assert (CF : forall c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem live elo ehi) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem live elo ehi) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem live elo ehi) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      unfold M. rewrite V293_entry_update_fixture_frame by discriminate. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate).
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads; repeat rewrite LF by discriminate; unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; repeat split; entry_update_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if live then 1 else 0)
    (V293_ready_group 16 (if live then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z elo ehi (V293_ready_group elo ehi)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; entry_update_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if self then 255 else 8))).
  { unfold M,V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct self; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M,V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j.
    unfold M,V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem live elo ehi) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M,V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite LF by discriminate. unfold V293_coordinate_fixture_mem.
    repeat rewrite V293_put_byte_other_load by discriminate. entry_update_load. }
  assert (Resolved : (if (if self then 255 else 8) =? 255 then 8 else (if self then 255 else 8)) = 8)
    by (destruct self; reflexivity).
  destruct (V293_critical_event_update_execution P ks V293_entry_update_fixture_ge V293_tcb_update_fixture_le
    M ir enabled si ci 500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 (if live then 1 else 0) (if self then 255 else 8) 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z elo ehi 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 80%positive 41%positive 8%Z 99%positive 8)
    as (Mg & Exec & Updated & FinalLoads & FinalView & OldSlot & NewSlot & FinalEvent & Read & Pointer & TW & InternalEvent & Untouched & Frame).
  all: try rewrite Resolved; try assumption; try discriminate; try (entry_update_bind; reflexivity);
    try (change (0 <= 8)%Z; lia); try (change (8+55 <= 4294967295)%Z; lia);
    try (change (0 <= 5)%Z; lia); try (change (5+12 <= 4294967295)%Z; lia);
    try (change (8<13); lia); try (change (6<12); lia); try (change (16<256); lia);
    try (destruct live; lia); try (destruct self; cbn; lia);
    try (change (length V293_prefix_fixture_entries = 13); reflexivity).
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear; lia)).
  - change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear; lia)).
  - intro IsSelf. repeat split; try (entry_update_bind; reflexivity); try assumption;
      try (change (0<=8)%Z; lia); try (change (8+50<=4294967295)%Z; lia).
  - exists (V293_tcb_update_memory Mg 41%positive 8%Z 6). rewrite Resolved in *.
    split; [exact Null | ]. split.
    + intros c I. rewrite LF by (clear - I; cbn in I; intuition congruence).
      apply V293_coordinate_fixture_stale. clear - I; cbn in I; intuition congruence.
    + split; [exact Exec | ]. split; [exact Updated | ].
      split; [destruct live; exact FinalLoads | ]. split; [exact FinalEvent | ].
      split; [exact FinalView | ]. split; [exact OldSlot | ]. split; [exact NewSlot | ]. exact InternalEvent.
Qed.



(* Success tail and the real scheduler call.  The unlocked branch is retained,
   but the traces below cover only non-running / ISR / scheduler-locked cases.
   This is the same explicit macro boundary, not a raw-port implementation. *)
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Local Open Scope nat_scope.

Definition V293_OSSched_success_body saved interrupt lock schednew table high target current counter :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (sprim encrit)
      (sseq (V293_OSSched_guards interrupt lock
        (sseq (V293_OSSched_unlocked_prefix schednew table high target)
          (V293_OSSched_change high current counter (sprim (switch target)))))
        (sseq (sprim excrit) sret))).
Definition V293_OSSched_success_function saved interrupt lock schednew table high target current counter : function :=
  (Tvoid,dnil,dcons saved Tint32 dnil,
    V293_OSSched_success_body saved interrupt lock schednew table high target current counter).
Definition V293_task_prio_running running :=
  ebinop oeq (ecast (evar running) Tint32) (econst32 Int.one).
Definition V293_task_prio_schedule running sched :=
  sifthen (V293_task_prio_running running) (scall sched nil).
Definition V293_task_prio_success_tail running sched :=
  sseq (V293_task_prio_schedule running sched) (srete (econst32 Int.zero)).

Lemma V293_success_allocb_outside : forall n M b i c j,
  (c <> b \/ (j < i)%Z \/ (i+Z.of_nat n <= j)%Z) ->
  get (allocb M b i n) (c,j) = get M (c,j).
Proof.
  induction n; intros M b i c j H; [reflexivity | ].
  cbn [allocb]. rewrite map_get_set' by (intro E; inversion E; subst; lia).
  apply IHn. destruct H as [H|[H|H]]; [left|right;left|right;right]; lia.
Qed.
Lemma V293_success_allocb_writable : forall n M b i,
  V293_bytes_writable (allocb M b i n) b i n.
Proof.
  induction n; intros M b i k K; [lia | ].
  destruct k as [ | k].
  - exists Undef. replace (i+Z.of_nat 0)%Z with i by lia.
    cbn [allocb]. apply map_get_set.
  - cbn [allocb]. rewrite map_get_set' by (intro E; inversion E; lia).
    replace (i+Z.of_nat (S k))%Z with (i+1+Z.of_nat k)%Z by lia.
    apply IHn. lia.
Qed.
Lemma V293_success_fresh_none : forall M b,
  fresh M b -> forall i, get M (b,i) = None.
Proof.
  intros M b Fresh i. destruct (get M (b,i)) as [v | ] eqn:E; [ | reflexivity].
  exfalso. apply (Fresh (b,i) i eq_refl). exists v; exact E.
Qed.
Lemma V293_success_load_not_fresh : forall M b c n,
  fresh M b -> load Tint8 M (c,0%Z) = Some (V293_byteval n) -> b <> c.
Proof.
  intros M b c n F L E; subst c.
  assert (Empty : get M (b,0%Z) = None) by (apply V293_success_fresh_none;exact F).
  unfold load,loadm in L. cbn [typelen loadbytes] in L.
  change (@get addr (bool * memval) mem memMap M (b,0%Z) = None) in Empty.
  rewrite Empty in L. discriminate.
Qed.

(* Actual zero initialization of the allocated CPU_SR object. *)
Lemma V293_success_assign_zero : forall P ks ge le M M' saved bs,
  get le saved = Some (bs,Tint32) ->
  store Tint32 M (bs,0%Z) (Vint32 Int.zero) = Some M' ->
  cstepstar P (curs (sassign (evar saved) (econst32 Int.zero)),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M').
Proof.
  intros P ks ge le M M' saved bs Binding Store.
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassign_step with (t1:=Tint32) (t2:=Tint32).
    - cbn [evaltype get_lenv]. rewrite Binding; reflexivity.
    - reflexivity.
    - apply eq_int; auto. }
  eapply c_stepstarn. { eapply expr_step; [reflexivity|apply ec32_step]. }
  eapply c_stepstarn. { eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_cstepstar_trans.
  { apply V293_expr_steps. apply evalval_imply_estepstar. eapply evaladdr_val_eq with (t:=Tint32).
    - cbn [evaltype get_lenv]. rewrite Binding; reflexivity.
    - cbn [evaladdr get_lenv]. rewrite Binding; reflexivity. }
  eapply c_stepstarn.
  { eapply stmt_step; [reflexivity | ]. eapply sassignend_step; try reflexivity. exact Store. }
  apply c_stepstar0.
Qed.

(* Allocate/init/free really returns the original memory, including all bytes
   at the fresh block outside the four-byte object. No allocator oracle. *)
Lemma V293_success_scheduler_storage : forall M bs,
  fresh M bs ->
  exists Ms,
    store Tint32 (allocb M bs 0%Z 4) (bs,0%Z) (Vint32 Int.zero) = Some Ms /\
    V293_bytes_writable Ms bs 0%Z 4 /\
    free Tint32 bs Ms = Some M /\
    (forall c i, c <> bs -> get Ms (c,i) = get M (c,i)).
Proof.
  intros M bs Fresh.
  destruct (V293_storebytes_exists (encode_val Tint32 (Vint32 Int.zero))
    (allocb M bs 0%Z 4) bs 0%Z) as [Ms Store].
  { rewrite encode_val_length. apply V293_success_allocb_writable. }
  assert (W : V293_bytes_writable Ms bs 0%Z 4).
  { intros k K. exists (nth k (encode_val Tint32 (Vint32 Int.zero)) Undef).
    eapply V293_storebytes_nth; [exact Store | ]. rewrite encode_val_length; exact K. }
  destruct (V293_freeb_construct 4 Ms bs 0%Z W) as [Mf Free].
  assert (Frame : forall c i,
    (c <> bs \/ (i < 0)%Z \/ (4 <= i)%Z) -> get Ms (c,i) = get M (c,i)).
  { intros c i H. rewrite (V293_storebytes_outside _ _ _ _ _ _ _ Store).
    - apply V293_success_allocb_outside. exact H.
    - rewrite encode_val_length. exact H. }
  assert (Back : Mf = M).
  { apply HalfPermMap.extensionality. intros [c i]. change (get Mf (c,i) = get M (c,i)).
    destruct (Pos.eq_dec c bs) as [E|E].
    - subst c. destruct (Z_lt_ge_dec i 0), (Z_lt_ge_dec i 4).
      + rewrite (V293_freeb_outside _ _ _ _ _ _ _ Free) by (right;left;lia).
        apply Frame; right;left;lia.
      + lia.
      + rewrite (V293_success_fresh_none M bs Fresh i).
        replace i with (0+Z.of_nat (Z.to_nat i))%Z by (rewrite Z2Nat.id;lia).
        eapply V293_freeb_removed; [exact Free|lia].
      + rewrite (V293_freeb_outside _ _ _ _ _ _ _ Free) by (right;right;lia).
        apply Frame; right;right;lia.
    - rewrite (V293_freeb_outside _ _ _ _ _ _ _ Free) by (left;exact E).
      apply Frame;left;exact E. }
  subst Mf. exists Ms. repeat split; try assumption.
  intros c i H. apply Frame;left;exact H.
Qed.

Lemma V293_success_global_byte_eq : forall ge le M x b n k,
  n < 256 -> k < 256 -> get le x = None -> get ge x = Some (b,Tint8) ->
  load Tint8 M (b,0%Z) = Some (V293_byteval n) ->
  evalval (ebinop oeq (ecast (evar x) Tint32) (econst32 (Int.repr (Z.of_nat k)))) (ge,le,M) =
    Some (Vint32 (if Nat.eqb n k then Int.one else Int.zero)).
Proof.
  intros ge le M x b n k N K NL G L.
  cbn [evalval evaltype get_lenv get_genv]. rewrite !NL,!G.
  cbn -[load]. rewrite L. unfold V293_byteval. cbn [cast_eval bop_eval val_eq].
  assert (Eq : Int.eq (Int.repr (Z.of_nat n)) (Int.repr (Z.of_nat k)) = Nat.eqb n k).
  { destruct (Nat.eqb n k) eqn:E.
    - apply Nat.eqb_eq in E. subst k. apply Int.eq_true.
    - apply Nat.eqb_neq in E. apply Int.eq_false. intro Same.
      apply (f_equal Int.unsigned) in Same.
      rewrite !Int.unsigned_repr in Same by
        (unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia).
      apply E. lia. }
  rewrite Eq. destruct (Nat.eqb n k);reflexivity.
Qed.

Definition V293_success_sched_blocked ge M interrupt lock : Prop :=
  exists bi ni,
    get ge interrupt = Some (bi,Tint8) /\
    load Tint8 M (bi,0%Z) = Some (V293_byteval ni) /\ ni < 256 /\
    (ni <> 0 \/ exists bl nl,
      get ge lock = Some (bl,Tint8) /\
      load Tint8 M (bl,0%Z) = Some (V293_byteval nl) /\ nl < 256 /\ nl <> 0).

Lemma V293_success_sched_guard_skip : forall P ks ge le M interrupt lock body,
  get le interrupt = None -> get le lock = None ->
  V293_success_sched_blocked ge M interrupt lock ->
  cstepstar P (curs (V293_OSSched_guards interrupt lock body),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,M).
Proof.
  intros P ks ge le M interrupt lock body NI NL (bi & ni & GI & LI & R & Blocked).
  unfold V293_OSSched_guards,V293_OSSched_zero.
  destruct (Nat.eq_dec ni 0) as [Zero|Nonzero].
  - subst ni. destruct Blocked as [Impossible | (bl & nl & GL & LL & LRange & LNonzero)]; [contradiction | ].
    eapply V293_rekey_if_execution with (flag:=true).
    + apply (V293_success_global_byte_eq ge le M interrupt bi 0 0); auto;lia.
    + intros _. eapply V293_rekey_if_execution with (flag:=false).
      * pose proof (V293_success_global_byte_eq ge le M lock bl nl 0 LRange ltac:(lia) NL GL LL) as E.
        assert (Z : Nat.eqb nl 0 = false) by (apply Nat.eqb_neq;exact LNonzero).
        rewrite Z in E. exact E.
      * discriminate.
      * reflexivity.
    + discriminate.
  - eapply V293_rekey_if_execution with (flag:=false).
    + pose proof (V293_success_global_byte_eq ge le M interrupt bi ni 0 R ltac:(lia) NI GI LI) as E.
      assert (Z : Nat.eqb ni 0 = false) by (apply Nat.eqb_neq;exact Nonzero).
      rewrite Z in E. exact E.
    + discriminate.
    + reflexivity.
Qed.

Theorem V293_success_sched_call_execution :
  forall P ks ge caller M ir enabled si ci sched saved interrupt lock schednew table high target current counter,
  P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) ->
  saved <> interrupt -> saved <> lock ->
  V293_success_sched_blocked ge M interrupt lock ->
  V293_local_steps P (curs (scall sched nil),(kenil,ks))
    ((ge,caller,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci)).
Proof.
  intros P ks ge caller M ir enabled si ci sched saved interrupt lock schednew table high target current counter
    Program SI SL Blocked.
  destruct (memory_has_fresh_block M) as [bs Fresh].
  destruct (V293_success_scheduler_storage M bs Fresh) as (Ms & Init & W & Free & Frame).
  set (callee := set (emp:env) saved (bs,Tint32)).
  set (body := V293_OSSched_success_body saved interrupt lock schednew table high target current counter).
  assert (Binding : get callee saved = Some (bs,Tint32)) by (unfold callee;apply map_get_set).
  assert (NI : get callee interrupt = None).
  { unfold callee. rewrite map_get_set' by exact SI. apply map_emp_get. }
  assert (NL : get callee lock = None).
  { unfold callee. rewrite map_get_set' by exact SL. apply map_emp_get. }
  assert (Blocked' : V293_success_sched_blocked ge Ms interrupt lock).
  { destruct Blocked as (bi & ni & GI & LI & R & B).
    assert (BI : bs <> bi) by (eapply V293_success_load_not_fresh;eassumption).
    exists bi. exists ni. split; [exact GI | ]. split.
    - etransitivity; [apply V293_load_block_frame;intro i;apply Frame;congruence | exact LI].
    - split; [exact R | ]. destruct B as [N| (bl & nl & GL & LL & LR & LN)].
      + left;exact N.
      + right. assert (BL : bs <> bl) by (eapply V293_success_load_not_fresh;eassumption).
        exists bl. exists nl. split; [exact GL | ]. split.
        * etransitivity; [apply V293_load_block_frame;intro i;apply Frame;congruence | exact LL].
        * split;assumption. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply snpcall_step]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply sfexec_step with (d1:=dnil) (d2:=dcons saved Tint32 dnil).
    - reflexivity.
    - reflexivity.
    - exact Program.
    - exact I.
    - reflexivity. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply salloclv_step.
    - reflexivity.
    - reflexivity.
    - exists bs. split; [exact Fresh | ]. split; [reflexivity | ]. split.
      + intros [v V]. rewrite map_emp_get in V. discriminate.
      + reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sallocend_step]. }
  unfold V293_OSSched_success_body.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local. eapply V293_success_assign_zero; [exact Binding|exact Init]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply encrit_step;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans.
  { apply V293_csteps_local. apply V293_success_sched_guard_skip;assumption. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_cons. { apply excrit_step;reflexivity. }
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply sret_step with (al:=[(bs,Tint32)]).
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply sfree_step; [reflexivity|reflexivity|exact Free]. }
  eapply V293_local_cons.
  { apply ostc_step. eapply stmt_step; [reflexivity | ]. eapply sfreeend_step; reflexivity. }
  apply V293_local_refl.
Qed.

Lemma V293_success_local_if : forall P ks ge le M ir enabled si ci cond body (flag : bool),
  evalval cond (ge,le,M) = Some (Vint32 (if flag then Int.one else Int.zero)) ->
  (flag = true -> V293_local_steps P (curs body,(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))) ->
  V293_local_steps P (curs (sifthen cond body),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)).
Proof.
  intros P ks ge le M ir enabled si ci cond body flag Eval Yes.
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|constructor]. }
  eapply V293_local_trans.
  { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Eval. }
  destruct flag.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply svift_step;reflexivity]. }
    apply Yes;reflexivity.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sviff_step;reflexivity]. }
    apply V293_local_refl.
Qed.

(* Non-running needs no scheduler definition or scheduler guard resources.
   For running=1, the callee creates its own locals and releases them. *)
Theorem V293_success_schedule_execution :
  forall P ks ge le M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter,
  run < 256 -> get le running = None -> get ge running = Some (rb,Tint8) ->
  load Tint8 M (rb,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_local_steps P (curs (V293_task_prio_schedule running sched),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)).
Proof.
  intros P ks ge le M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter
    Range NL G L WhenRunning.
  unfold V293_task_prio_schedule,V293_task_prio_running.
  change Int.one with (Int.repr (Z.of_nat 1)).
  eapply V293_success_local_if with (flag:=Nat.eqb run 1).
  - apply V293_success_global_byte_eq with (b:=rb);auto;lia.
  - intro Yes. apply Nat.eqb_eq in Yes. destruct (WhenRunning Yes) as (Program & SI & SL & Blocked).
    eapply V293_success_sched_call_execution;eassumption.
Qed.

(* This public tail starts AFTER critical updates/excrit. It is not yet a
   whole-function root: writable caller locals are resources at this boundary. *)
Theorem V293_success_tail_return_execution :
  forall P ks ge le caller M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter
    f body next,
  run < 256 -> get le running = None -> get ge running = Some (rb,Tint8) ->
  load Tint8 M (rb,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall b t, In (b,t) (getaddr le) -> V293_bytes_writable M b 0%Z (typelen t)) ->
  exists Mf,
    V293_local_steps P (curs (V293_task_prio_success_tail running sched),(kenil,ks)) ((ge,le,M),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 Int.zero))),(kenil,next)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (forall b i, ~ In b (map fst (getaddr le)) -> get Mf (b,i) = get M (b,i)) /\
    (forall b t k, In (b,t) (getaddr le) -> k < typelen t -> get Mf (b,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M ir enabled si ci running rb run sched saved interrupt lock schednew table high target current counter
    f body next Range NL G L Running Call ND W.
  destruct (V293_error_return_execution P ks ge le caller M f body next 0%Z Call ND W)
    as (Mf & Return & Frame & Removed).
  exists Mf. split.
  - unfold V293_task_prio_success_tail.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans.
    { eapply V293_success_schedule_execution;eassumption. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    apply V293_csteps_local. exact Return.
  - split;assumption.
Qed.

Definition V293_success_globals_away (ge : env) (names : list var) (written : list block) :=
  forall x b, In x names -> get ge x = Some (b,Tint8) -> ~ In b written.

Lemma V293_success_sched_blocked_frame : forall ge M M' interrupt lock written,
  V293_success_globals_away ge [interrupt;lock] written ->
  (forall b i, ~ In b written -> get M' (b,i) = get M (b,i)) ->
  V293_success_sched_blocked ge M interrupt lock ->
  V293_success_sched_blocked ge M' interrupt lock.
Proof.
  intros ge M M' interrupt lock written Away Frame (bi & ni & GI & LI & R & Blocked).
  exists bi. exists ni. split; [exact GI | ]. split.
  - etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=interrupt);simpl; eauto | exact LI].
  - split; [exact R | ]. destruct Blocked as [N | (bl & nl & GL & LL & LR & LN)].
    + left;exact N.
    + right. exists bl. exists nl. split; [exact GL | ]. split.
      * etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=lock);simpl;eauto | exact LL].
      * split;assumption.
Qed.

(* Original-memory update resources now reach the REAL guarded scheduler call.
   The final API return/free is a separate tail root, not claimed here. *)
Theorem V293_critical_null_schedule_execution :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved) (V293_task_prio_schedule running sched)),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away.
  pose proof (V293_critical_null_update_execution P (kseq (V293_task_prio_schedule running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [Exec Rest].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & Read & Pointer & Internal & Tail).
    destruct Tail as [Untouched Frame]. apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  exists Mg. split; [ | exact Rest].
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans; [exact Exec | ].
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_success_schedule_execution;eassumption.
Qed.

(* Original-memory update resources now reach the REAL guarded scheduler call.
   The final API return/free is a separate tail root, not claimed here. *)
Theorem V293_critical_event_schedule_execution :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
  V293_local_steps P (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved) (V293_task_prio_schedule running sched)),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away.
  pose proof (V293_critical_event_update_execution P (kseq (V293_task_prio_schedule running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [Exec Rest].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventLoads & Read & Pointer & Writable & Internal & Untouched & Frame). apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  exists Mg. split; [ | exact Rest].
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
  eapply V293_local_trans; [exact Exec | ].
  eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
  eapply V293_success_schedule_execution;eassumption.
Qed.

Definition V293_success_tail_fixture_ge : env :=
  set (set (set emp 1001%Z (100%positive,Tint8)) 1002%Z (101%positive,Tint8)) 1003%Z (102%positive,Tint8).
Definition V293_success_tail_fixture_mem (saved : bool) run nesting locked :=
  V293_put_byte (V293_put_byte (V293_put_byte (V293_return_fixture_mem saved)
    (100%positive,0%Z) run) (101%positive,0%Z) nesting) (102%positive,0%Z) locked.
Definition V293_success_tail_fixture_program (f : fid) : option function :=
  if Z.eq_dec f 999%Z then
    Some (V293_OSSched_success_function 1004%Z 1002%Z 1003%Z 1005%Z 500%Z 1006%Z 1007%Z 1008%Z 1009%Z)
  else None.

(* Physical simultaneous tail resources, not initialization/reachability.
   All IE/stack values are allowed. Covers non-running, ISR and lock branches. *)
Theorem V293_success_tail_return_witness : forall saved run nesting locked enabled si ci ir,
  run < 256 -> nesting < 256 -> locked < 256 ->
  (run = 1 -> nesting <> 0 \/ locked <> 0) ->
  exists Mf,
    V293_local_steps V293_success_tail_fixture_program
      (curs (V293_task_prio_success_tail 1001%Z 999%Z),(kenil,kcall 700%Z sret emp kstop))
      ((V293_success_tail_fixture_ge,V293_return_fixture_le,V293_success_tail_fixture_mem saved run nesting locked),ir,(enabled,si,ci))
      (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
      ((V293_success_tail_fixture_ge,emp,Mf),ir,(enabled,si,ci)) /\
    get Mf (51%positive,0%Z) = None /\
    (forall k, k < 4 -> get Mf (61%positive,Z.of_nat k) = None) /\
    load Tint8 Mf (100%positive,0%Z) = Some (V293_byteval run) /\
    load Tint8 Mf (101%positive,0%Z) = Some (V293_byteval nesting) /\
    load Tint8 Mf (102%positive,0%Z) = Some (V293_byteval locked).
Proof.
  intros saved run nesting locked enabled si ci ir RunRange NestRange LockRange Blocked.
  set (M := V293_success_tail_fixture_mem saved run nesting locked).
  assert (Addresses : getaddr V293_return_fixture_le = [(51%positive,Tint8);(61%positive,Tint32)]) by reflexivity.
  assert (ND : NoDup (map fst (getaddr V293_return_fixture_le))).
  { rewrite Addresses. repeat constructor;cbn;intuition discriminate. }
  assert (W : forall b t, In (b,t) (getaddr V293_return_fixture_le) -> V293_bytes_writable M b 0%Z (typelen t)).
  { intros b t I. rewrite Addresses in I. destruct I as [E | [E | F]]; try contradiction; inversion E;subst b t.
    - intros k K. cbn in K. assert (k=0) by lia. subst k. unfold M,V293_success_tail_fixture_mem.
      repeat rewrite V293_put_byte_other by discriminate.
      unfold V293_return_fixture_mem. rewrite V293_fixture_bytes_outside by (left;discriminate).
      eexists. apply V293_put_byte_get_same.
    - intros k K. unfold M,V293_success_tail_fixture_mem. repeat rewrite V293_put_byte_other by discriminate.
      unfold V293_return_fixture_mem. eexists. apply V293_fixture_bytes_nth.
      rewrite encode_val_length. exact K. }
  assert (LR : load Tint8 M (100%positive,0%Z) = Some (V293_byteval run)).
  { unfold M,V293_success_tail_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate. apply V293_put_byte_load;exact RunRange. }
  assert (LI : load Tint8 M (101%positive,0%Z) = Some (V293_byteval nesting)).
  { unfold M,V293_success_tail_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate. apply V293_put_byte_load;exact NestRange. }
  assert (LL : load Tint8 M (102%positive,0%Z) = Some (V293_byteval locked)).
  { unfold M,V293_success_tail_fixture_mem. apply V293_put_byte_load;exact LockRange. }
  assert (Run : run = 1 ->
    V293_success_tail_fixture_program 999%Z = Some (V293_OSSched_success_function 1004%Z 1002%Z 1003%Z 1005%Z 500%Z 1006%Z 1007%Z 1008%Z 1009%Z) /\
    1004%Z <> 1002%Z /\ 1004%Z <> 1003%Z /\ V293_success_sched_blocked V293_success_tail_fixture_ge M 1002%Z 1003%Z).
  { intro One. split; [reflexivity | ]. split; [discriminate | ]. split; [discriminate | ].
    exists 101%positive. exists nesting. split.
    - unfold V293_success_tail_fixture_ge. rewrite map_get_set' by discriminate. apply map_get_set.
    - split; [exact LI | ]. split; [exact NestRange | ]. destruct (Blocked One) as [N|N]; [left;exact N | right].
      exists 102%positive. exists locked. split; [apply map_get_set | ]. split; [exact LL | ]. split;assumption. }
  destruct (V293_success_tail_return_execution V293_success_tail_fixture_program
    (kcall 700%Z sret emp kstop) V293_success_tail_fixture_ge V293_return_fixture_le emp M ir enabled si ci
    1001%Z 100%positive run 999%Z 1004%Z 1002%Z 1003%Z 1005%Z 500%Z 1006%Z 1007%Z 1008%Z 1009%Z
    700%Z sret kstop RunRange) as (Mf & Exec & Frame & Removed).
  - unfold V293_return_fixture_le. repeat rewrite map_get_set' by discriminate. apply map_emp_get.
  - unfold V293_success_tail_fixture_ge. repeat rewrite map_get_set' by discriminate. apply map_get_set.
  - exact LR.
  - exact Run.
  - reflexivity.
  - exact ND.
  - exact W.
  - exists Mf. split; [exact Exec | ]. split.
    + change (get Mf (51%positive,Z.of_nat 0) = None). apply Removed with Tint8; [rewrite Addresses;left;reflexivity|cbn;lia].
    + split.
      * intros k K. apply Removed with Tint32; [rewrite Addresses;right;left;reflexivity|exact K].
      * repeat split; etransitivity; try (apply V293_load_block_frame;intro i;apply Frame;rewrite Addresses;cbn;intuition discriminate);assumption.
Qed.


(* Full-permission refinement of the frozen update proofs.  Only actual stores
   and pure byte updates preserve permission; NOT arbitrary cstepstar traces. *)
Definition V293_preserves_writable (M M' : mem) : Prop :=
  forall b i v, get M (b,i) = Some (true,v) ->
    exists w, get M' (b,i) = Some (true,w).

Lemma V293_writable_refl : forall M, V293_preserves_writable M M.
Proof. intros M b i v W. exists v;exact W. Qed.
Lemma V293_writable_trans : forall M1 M2 M3,
  V293_preserves_writable M1 M2 -> V293_preserves_writable M2 M3 ->
  V293_preserves_writable M1 M3.
Proof. intros M1 M2 M3 A B b i v W. destruct (A b i v W) as [w R]. eapply B;exact R. Qed.
Lemma V293_put_byte_writable : forall M a n,
  V293_preserves_writable M (V293_put_byte M a n).
Proof.
  intros M [b i] n c j v W. destruct (addr_eq_dec (c,j) (b,i)) as [E|E].
  - inversion E;subst. eexists. unfold V293_put_byte. apply map_get_set.
  - exists v. rewrite V293_put_byte_other by exact E. exact W.
Qed.
Lemma V293_store_writable : forall t M M' b i v,
  store t M (b,i) v = Some M' -> V293_preserves_writable M M'.
Proof. intros t M M' b i v S. unfold V293_preserves_writable. intros c j w W. eapply V293_storebytes_preserves_writable; [exact S|exact W]. Qed.

(* This tactic traverses only the finite, explicit memory transformers below. *)
Ltac V293_writable_pure :=
  unfold V293_coordinate_memory,V293_tcb_read_memory,V293_tcb_update_memory,
    V293_ready_branch_memory,V293_rekey_ready_memory,V293_event_rekey_memory;
  cbn zeta;
  let rec go := lazymatch goal with
  | |- V293_preserves_writable ?M ?M => apply V293_writable_refl
  | |- V293_preserves_writable ?M (V293_put_byte ?N ?a ?n) =>
      eapply V293_writable_trans with (M2:=N); [go | apply V293_put_byte_writable]
  | |- context [if ?test then _ else _] => destruct test; go
  end in go.


Lemma V293_task_prio_resolve_execution_writable :
  forall P ge le M oldprio current bo bcur bct base old curprio,
  old < 256 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le oldprio = Some (bo,Tint8) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  exists Ms,
    V293_preserves_writable M Ms /\
    (forall tail, cstepstar P (curs (V293_task_prio_self_read oldprio current),(kenil,tail)) (ge,le,M)
      (curs (sskip None),(kenil,tail)) (ge,le,Ms)) /\
    load Tint8 Ms (bo,0%Z) = Some (V293_byteval resolved) /\
    (forall c i, c <> bo -> get Ms (c,i) = get M (c,i)).
Proof.
  intros P ge le M oldprio current bo bcur bct base old curprio O resolved R Bo Lo Self.
  destruct (V293_entry_byte_tests ge le M oldprio bo old O Bo Lo) as [_ Test].
  exists (if old =? 255 then V293_put_byte M (bo,0%Z) curprio else M).
  split. { destruct (old =? 255); [apply V293_put_byte_writable|apply V293_writable_refl]. }
  split.
  - intro tail. unfold V293_task_prio_self_read. destruct (old =? 255) eqn:S.
    + destruct (Self (proj1 (Nat.eqb_eq old 255) S)) as (Nc & Gc & Pc & Base & Limit & Prio & W).
      assert (CP : curprio < 256) by (unfold resolved in R; simpl in R; lia).
      destruct (V293_entry_current_prio_eval ge le M current bcur bct base curprio Nc Gc Pc Base Limit Prio) as [T V].
      eapply V293_rekey_if_execution with (flag:=true); [exact Test| |discriminate].
      intros _. eapply V293_coordinate_local_assignment; eassumption.
    + eapply V293_rekey_if_execution with (flag:=false); [exact Test|discriminate|reflexivity].
  - split.
    + unfold resolved. destruct (old =? 255) eqn:S; [apply V293_put_byte_load; unfold resolved in R; simpl in R; lia|exact Lo].
    + intros c i D. destruct (old =? 255); [apply V293_put_byte_other; congruence|reflexivity].
Qed.


Theorem V293_primitive_entry_success_writable :
  forall P ks ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct base old new curprio next br,
  old < 256 -> new < 12 ->
  let resolved := if old =? 255 then curprio else old in
  resolved < 13 ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->
  b <> bo -> b <> bc -> bo <> bn -> bc <> bn -> bc <> bo ->
  (old = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr base)) /\
    (0 <= base)%Z /\ (base+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(base+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (br,Tint8) ->
  next <> (br,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  exists Mf,
  V293_preserves_writable M Mf /\
  resolved <> new /\
  cstepstar P (curs (V293_primitive_entry table oldprio newprio ptcb current reserved),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  load Tint8 Mf (bo,0%Z) = Some (V293_byteval resolved) /\
  load Tint8 Mf (bn,0%Z) = Some (V293_byteval new) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) /\
  load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some Vnull /\
  V293_bytes_writable Mf bc 0%Z 4 /\
  (forall c i, c <> bo -> c <> bc -> get Mf (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct base old new curprio next br O N resolved R Nt Gt Bo Bn Bc Lo Ln Empty Slot
    Tbo Tbc Onew Cnew CO Self Nr Gr Token CW.
  assert (Different : resolved <> new).
  { intro E. rewrite E in Slot. rewrite Empty in Slot. discriminate. }
  destruct (V293_task_prio_resolve_execution_writable P ge le M oldprio current bo bcur bct base
    old curprio O R Bo Lo Self) as (Ms & SelfWritable & SelfStep & ResolvedRead & SF).
  assert (SL : forall tp c i, c <> bo -> load tp Ms (c,i) = load tp M (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intros j. apply SF; exact D. }
  assert (SlotS : load (Tptr V293_tcb_type) Ms (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next)).
  { rewrite SL by congruence. exact Slot. }
  assert (W : V293_bytes_writable Ms bc 0%Z 4).
  { intros k K. unfold V293_bytes_writable in CW. rewrite SF by exact CO. apply CW; exact K. }
  destruct (V293_storebytes_exists (encode_val (Tptr V293_tcb_type) (Vptr next)) Ms bc 0%Z)
    as [Mf Store].
  { rewrite encode_val_length. exact W. }
  assert (PF : forall c i, c <> bc -> get Mf (c,i) = get Ms (c,i)).
  { intros c i D. eapply V293_storebytes_outside; [exact Store|left;exact D]. }
  assert (PL : forall tp c i, c <> bc -> load tp Mf (c,i) = load tp Ms (c,i)).
  { intros tp c i D. apply V293_load_block_frame. intro j. apply PF; exact D. }
  assert (Pointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)).
  { eapply V293_store_readback; [reflexivity|exact Store]. }
  destruct (V293_entry_array_eval ge le M table newprio b bn new Vnull Nt Gt Bn Ln ltac:(lia) Empty)
    as [NewType NewValue].
  assert (TargetTest : evalval (eunop oppsite (V293_task_prio_null_test
    (earrayelem (evar table) (evar newprio)))) (ge,le,M) = Some (Vint32 Int.zero)).
  { apply (proj2 (V293_entry_null_eval ge le M _ Vnull NewType NewValue (or_introl eq_refl))). }
  destruct (V293_entry_array_eval ge le Ms table oldprio b bo resolved (Vptr next)
    Nt Gt Bo ResolvedRead ltac:(lia) SlotS) as [OldType OldValue].
  assert (LookupStep : forall tail,
    cstepstar P (curs (V293_task_prio_lookup table oldprio ptcb),(kenil,tail)) (ge,le,Ms)
      (curs (sskip None),(kenil,tail)) (ge,le,Mf)).
  { intro tail. unfold V293_task_prio_lookup.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z);
      try eassumption.
    - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  assert (NullTest : evalval (V293_task_prio_null_test (evar ptcb)) (ge,le,Mf) = Some (Vint32 Int.zero)).
  { unfold V293_task_prio_null_test. cbn [evalval evaltype get_lenv get_genv get_mem].
    rewrite Bc. cbn beta iota. rewrite Pointer. destruct next; reflexivity. }
  assert (ReservedTest : evalval (V293_task_prio_reserved_test ptcb reserved)
    (ge,le,Mf) = Some (Vint32 Int.zero)).
  { pose proof (V293_reserved_test_eval ge le Mf ptcb reserved bc br (Vptr next)
      Bc Pointer (or_intror (ex_intro _ next eq_refl)) Nr Gr) as E.
    assert (F : V293_reserved_matches br (Vptr next) = false).
    { destruct (V293_reserved_matches br (Vptr next)) eqn:Choice; [ |reflexivity].
      apply V293_reserved_matches_pointer in Choice. contradiction. }
    rewrite F in E. exact E. }
  exists Mf. split.
  { eapply V293_writable_trans; [exact SelfWritable| ]. unfold V293_preserves_writable. intros c j v W0. eapply V293_storebytes_preserves_writable; [exact Store|exact W0]. }
  split; [exact Different| ]. split.
  - unfold V293_primitive_entry.
    eapply V293_rekey_sequence_execution with (M1:=Mf).
    + intro tail. eapply V293_rekey_sequence_execution with (M1:=M).
      * intro tail'. eapply V293_rekey_if_execution with (flag:=false); [exact TargetTest|discriminate|reflexivity].
      * eapply V293_rekey_sequence_execution with (M1:=Ms); [exact SelfStep| ].
        eapply V293_rekey_sequence_execution with (M1:=Mf); [exact LookupStep| ].
        eapply V293_rekey_if_execution with (flag:=false); [exact NullTest|discriminate|reflexivity].
    + eapply V293_rekey_if_execution with (flag:=false); [exact ReservedTest|discriminate|reflexivity].
  - split; [rewrite PL by congruence; exact ResolvedRead| ].
    split; [rewrite PL,SL by congruence; exact Ln| ].
    split; [exact Pointer| ]. split; [rewrite PL by congruence; exact SlotS| ].
    split; [rewrite PL,SL by congruence; exact Empty| ]. split.
    + intros k K. exists (nth k (encode_val (Tptr V293_tcb_type) (Vptr next)) Undef).
      eapply V293_storebytes_nth; [exact Store|rewrite encode_val_length;exact K].
    + intros c i A B. rewrite PF by exact B. apply SF; exact A.
Qed.


Theorem V293_task_prio_prefix_null_update_execution_writable :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Me,
  let Mh := V293_tcb_update_memory Me bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_null_execution P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg)
    as (M1 & M2 & Me & S1 & S2 & Store & Read & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  assert (Prefix : forall tail, cstepstar P
    (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,Me)).
  { intro tail. destruct (V293_task_prio_prefix_event_null_execution P tail ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg)
      as (A & B & C & SA & SB & SC & _ & E & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B.
    change (store (Tptr V293_event_type) Mf (bp,0%Z) Vnull = Some C) in SC.
    rewrite Store in SC. inversion SC; subst C. exact E. }
  assert (TC : forall i, get Me (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PC : forall i, get Me (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (ExtraFrame : forall c, c = bn \/ c = bi ->
    forall tp i, load tp Me (c,i) = load tp M (c,i)).
  { intros c I tp i. destruct (ExtraApart c I) as (A & B & C & D & E & F & G & J).
    apply V293_load_block_frame. intro j. apply Frame; assumption. }
  assert (EF : forall tp c i, c <> bp -> load tp Me (c,i) = load tp Mf (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j.
    eapply V293_storebytes_outside; [exact Store | left; exact A]. }
  assert (Hptr : load (Tptr V293_tcb_type) Me (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { rewrite (V293_load_block_frame _ M Me bc 0%Z PC). exact Lp. }
  assert (WG : V293_tcb_update_writable Me bt base).
  { intros d D. rewrite TC. exact (TW d D). }
  assert (NewValues : forall x v, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    exists c, get le x = Some (c,Tint8) /\ c <> bt /\ c <> bt /\ load Tint8 Me (c,0%Z) = Some v).
  { intros x v I. destruct (FinalLoc x v ltac:(clear -I; unfold V293_rekey_new_bindings in I;
      unfold V293_rekey_ready_bindings; simpl in *; tauto)) as (c & Bind & A & B & Load).
    destruct (NewTcbApart x v c I Bind) as [C D].
    exists c. repeat split; try assumption. rewrite EF by exact C. exact Load. }
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ BY].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [_ BX].
  assert (Operands : V293_rekey_locals ge le Me bt bt (V293_tcb_update_bindings newprio yn xi byn xn new)).
  { intros x v I. cbn [V293_tcb_update_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|F]]]]]; try contradiction; inversion E; subst x v.
    - exists bn. destruct (ExtraApart bn ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Ln.
    - apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - exists bi. destruct (ExtraApart bi ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Li.
    - rewrite BY. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - rewrite BX. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto. }
  destruct (V293_task_prio_tcb_update_execution P ks ge le Me ptcb newprio yn xi byn xn bc bt base new
    N Base Limit Bc CT Hptr Operands WG)
    as (Suffix & Updated & Pointer & FinalOperands & Writable & TF).
  set (Mh := V293_tcb_update_memory Me bt base new) in *.
  assert (RF : forall tp c i, c <> bt -> load tp Mh (c,i) = load tp Me (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply TF. left. exact A. }
  assert (Untouched : forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)).
  { intros i I. rewrite TF by (right; exact I). apply TC. }
  assert (FinalEvent : load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ M Mh).
    - exact Event.
    - intros k K. cbn [typelen] in K. apply Untouched. left. lia. }
  exists Me. cbn zeta. fold Mh. split.
  { eapply V293_writable_trans with (M2:=M1).
    - eapply V293_store_writable;exact S1.
    - eapply V293_writable_trans with (M2:=M2).
      + eapply V293_store_writable;exact S2.
      + eapply V293_writable_trans with (M2:=Mr).
        * unfold Mr. V293_writable_pure.
        * eapply V293_writable_trans with (M2:=Mf).
          -- unfold Mf. V293_writable_pure.
          -- eapply V293_writable_trans with (M2:=Me).
             ++ eapply V293_store_writable;exact Store.
             ++ unfold Mh. V293_writable_pure. }
  split.
  - unfold V293_task_prio_prefix_event_update. eapply V293_rekey_sequence_execution; eassumption.
  - split; [exact Updated | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split; [intros p R; rewrite RF by congruence; exact (FinalView p R) | ].
      split; [rewrite RF by congruence; exact OldSlot | ].
      split; [rewrite RF by congruence; exact NewSlot | ].
      split; [rewrite RF by congruence; exact Read | ].
      split; [exact Pointer | ]. split; [exact FinalEvent | ].
      split; [exact Untouched | ].
      intros c i A B C D E F G J. rewrite TF by auto. apply Frame; assumption.
Qed.


Theorem V293_task_prio_coordinates_null_update_execution_writable :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW.
  assert (SourceApart : forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx -> c <> bn).
  { intros c I. destruct (CoordApart c I) as (_ & _ & A & _). exact A. }
  destruct (V293_task_prio_coordinates_execution P ks ge le M newprio yn xi byn xn bn ny bi nby nbx new
    N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW)
    as (Coordinates & NewY & NewI & NewBY & NewBX & NewSource & CoordFrame).
  set (Mc := V293_coordinate_memory M ny bi nby nbx new) in *.
  assert (Safe : forall c, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    c <> ny /\ c <> bi /\ c <> nby /\ c <> nbx).
  { intros c I.
    pose proof (CoordApart ny ltac:(auto)) as A.
    pose proof (CoordApart bi ltac:(auto)) as B.
    pose proof (CoordApart nby ltac:(auto)) as C.
    pose proof (CoordApart nbx ltac:(auto)) as D.
    cbn in I. intuition congruence. }
  assert (CF : forall c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    get Mc (c,i) = get M (c,i)).
  { intros c i I. destruct (Safe c I) as (A & B & C & D).
    apply CoordFrame; congruence. }
  assert (LF : forall tp c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp] ->
    load tp Mc (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF. exact I. }
  assert (NewLoc : V293_rekey_locals ge le Mc br bg (V293_rekey_new_bindings yn xn byn new)).
  { destruct (V293_prio_coordinates new N) as [Y X].
    destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ MY].
    destruct (V293_mask_byte_value (V293_prio_bit new) X) as [_ MX].
    intros x v I. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
    - exists ny. destruct (CoordApart ny ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; assumption.
    - exists nbx. destruct (CoordApart nbx ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MX. exact NewBX.
    - exists nby. destruct (CoordApart nby ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MY. exact NewBY. }
  assert (Resources :
    load Tint8 Mc (bo,0%Z) = Some (V293_byteval old) /\
    load (Tptr V293_tcb_type) Mc (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
    V293_bytes_writable Mc b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Mc b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Mc b entries /\
    V293_tcb_old_loads Mc bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Mc (dy,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dby,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Mc br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Mc br bg /\
    V293_bytes_writable Mc bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Mc (bt,(base+28)%Z) = Some Vnull /\
    V293_tcb_update_writable Mc bt base).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; tauto).
    repeat rewrite CF by (simpl; tauto).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; tauto). apply Wo. exact K.
    - intros k K. rewrite CF by (simpl; tauto). apply Wn. exact K.
    - intros p R. rewrite LF by (simpl; tauto). apply View. exact R.
    - intros k K. rewrite CF by (simpl; tauto). apply We. exact K.
    - intros d D. rewrite CF by (simpl; tauto). apply TW. exact D. }
  destruct Resources as (Clo & Clp & Cwo & Cwn & Cview & Cfields & Cwy & Cwby & Cwx & Cloads & Cw & Cwe & Cevent & Ctw).
  destruct (V293_task_prio_prefix_null_update_execution_writable P ks ge le Mc table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Clo NewSource Clp Cwo Cwn Len Cview By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Cfields
    Cwy Cwby Cwx Cloads Cw NewLoc NewApart Be Cwe Cevent Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi NewI ExtraApart NewTcbApart Ctw)
    as (Mg & PrefixWritable & Exec & Updated & Ready & Table & OldSlot & NewSlot & Read & Pointer & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  { eapply V293_writable_trans with (M2:=Mc); [unfold Mc;V293_writable_pure|exact PrefixWritable]. }
  split.
  - unfold V293_task_prio_coordinates_update.
    eapply V293_rekey_sequence_execution; [ | exact Exec].
    intro tail. destruct (V293_task_prio_coordinates_execution P tail ge le M newprio yn xi byn xn bn ny bi nby nbx new
      N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW) as [E _]. exact E.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ].
    split; [exact Read | ]. split; [exact Pointer | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF. simpl; tauto.
    + intros c i A B C D E F G J NY NI NBY NBX.
      rewrite Frame by assumption. apply CoordFrame; congruence.
Qed.


Theorem V293_critical_null_update_execution_writable :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
V293_preserves_writable M Mh /\
    V293_local_steps P (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_primitive_entry_success_writable P
    (kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) (sprim excrit)) ks)
    ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & EntryWritable & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some Vnull /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_null_update_execution_writable P (kseq (sprim excrit) ks) ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg
    CT CP TP Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & UpdateWritable & Exec & Updated & Ready & Table & OldSlot & NewSlot & Read & OutPointer & Internal & Untouched & Frame).
  exists Mg. cbn zeta in *. split.
  { eapply V293_writable_trans; [exact EntryWritable|exact UpdateWritable]. }
  split.
  - eapply V293_success_segment_execution with (Ma:=Ma) (bo:=bo) (bn:=bn) (initial:=initial) (new:=new); eassumption.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ].
    split; [exact Read | ]. split; [exact OutPointer | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + intros c i OB PC A B C D E F G J NY NI NBY NBX.
      rewrite Frame by assumption. apply EntryFrame; assumption.
Qed.


Theorem V293_event_type_field_layout :
  ftype 1%Z V293_event_fields = Some Tint8 /\
  field_offset 1%Z V293_event_fields = Some Int.zero.
Proof. split; reflexivity. Qed.

Definition V293_event_kind_code (data : edata) : nat :=
  match data with
  | abssem _ => 3
  | absmbox _ => 1
  | absmsgq _ _ => 2
  | absmutexsem _ _ => 4
  end.

Definition V293_event_type_matches (M : mem) (be : block) (base : Z)
    (data : edata) : Prop :=
  load Tint8 M (be,base) = Some (V293_byteval (V293_event_kind_code data)).

Lemma V293_event_type_matches_frame : forall M M' be base data,
  get M' (be,base) = get M (be,base) ->
  V293_event_type_matches M be base data ->
  V293_event_type_matches M' be base data.
Proof.
  intros M M' be base data Frame Kind.
  unfold V293_event_type_matches in *.
  unfold load,loadm in *.
  rewrite (V293_loadbytes_ext _ M M'); [exact Kind | ].
  intros k K. cbn [typelen] in K. assert (k = 0) by lia. subst k.
  replace (base+Z.of_nat 0)%Z with base by lia. exact Frame.
Qed.

Lemma V293_event_rekey_byte_frame : forall M be base lo hi old new c i,
  old < 13 -> new < 13 ->
  c <> be \/ (i < base+10)%Z \/ (base+12 < i)%Z ->
  get (V293_event_rekey_memory M be base lo hi old new) (c,i) = get M (c,i).
Proof.
  intros M be base lo hi old new c i O N Outside.
  assert (RO : V293_prio_row old < 2) by (unfold V293_prio_row; destruct (_ <? 8); lia).
  assert (RN : V293_prio_row new < 2) by (unfold V293_prio_row; destruct (_ <? 8); lia).
  unfold V293_event_rekey_memory.
  repeat rewrite V293_put_byte_other by
    (intro E; inversion E; subst; destruct Outside as [D|[D|D]]; try contradiction; lia).
  destruct (_ =? 0);
    repeat rewrite V293_put_byte_other by
      (intro E; inversion E; subst; destruct Outside as [D|[D|D]]; try contradiction; lia);
    reflexivity.
Qed.

Theorem V293_task_prio_prefix_event_update_preserves_writable_event_frame :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    get Mh (c,i) = get M (c,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mh (be,i) = get M (be,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_nonnull_execution P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
    as (M1 & M2 & Me & S1 & S2 & Store & Exec & Test & FinalLoads & FinalView & OldSlot & NewSlot & FinalW & FinalLoc & FinalEvent & FinalEW & Read & Frame).
  set (Mr := V293_tcb_read_memory M2 dy dby dx (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old)) in *.
  set (Mf := V293_ready_branch_memory Mr br bg lo hi old new) in *.
  set (Mg := V293_event_rekey_memory Me be ebase elo ehi old new) in *.
  assert (Prefix : forall tail, cstepstar P
    (curs (V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,Mg)).
  { intro tail. destruct (V293_task_prio_prefix_event_nonnull_execution P tail ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart)
      as (A & B & C & SA & SB & SC & E & _).
    rewrite S1 in SA. inversion SA; subst A. rewrite S2 in SB. inversion SB; subst B.
    change (store (Tptr V293_event_type) Mf (bp,0%Z) (Vptr (be,Int.repr ebase)) = Some C) in SC.
    rewrite Store in SC. inversion SC; subst C. exact E. }
  assert (TC : forall i, get Mg (bt,i) = get M (bt,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [_ [A _]];
      destruct (Apart dby ltac:(auto)) as [_ [A' _]];
      destruct (Apart dx ltac:(auto)) as [_ [A'' _]]; congruence. }
  assert (PC : forall i, get Mg (bc,i) = get M (bc,i)).
  { intro i. apply Frame; try congruence;
      destruct (Apart dy ltac:(auto)) as [A _];
      destruct (Apart dby ltac:(auto)) as [A' _];
      destruct (Apart dx ltac:(auto)) as [A'' _]; congruence. }
  assert (ExtraFrame : forall c, c = bn \/ c = bi ->
    forall tp i, load tp Mg (c,i) = load tp M (c,i)).
  { intros c I tp i. destruct (ExtraApart c I) as (A & B & C & D & E & F & G & H' & J).
    apply V293_load_block_frame. intro j. apply Frame; assumption. }
  assert (Hptr : load (Tptr V293_tcb_type) Mg (bc,0%Z) = Some (Vptr (bt,Int.repr base))).
  { rewrite (V293_load_block_frame _ M Mg bc 0%Z PC). exact Lp. }
  assert (WG : V293_tcb_update_writable Mg bt base).
  { intros d D. rewrite TC. exact (TW d D). }
  assert (NewValues : forall x v, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    exists c, get le x = Some (c,Tint8) /\ c <> bt /\ c <> bt /\ load Tint8 Mg (c,0%Z) = Some v).
  { intros x v I. destruct (FinalLoc x v ltac:(clear -I; unfold V293_rekey_new_bindings in I;
      unfold V293_rekey_ready_bindings; simpl in *; tauto)) as (c & Bind & A & B & Load).
    exists c. repeat split; try assumption; eapply NewTcbApart; eassumption. }
  destruct (V293_prio_coordinates new N) as [Yn Xn].
  destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ BY].
  destruct (V293_mask_byte_value (V293_prio_bit new) Xn) as [_ BX].
  assert (Operands : V293_rekey_locals ge le Mg bt bt (V293_tcb_update_bindings newprio yn xi byn xn new)).
  { intros x v I. cbn [V293_tcb_update_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|F]]]]]; try contradiction; inversion E; subst x v.
    - exists bn. destruct (ExtraApart bn ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption.
      rewrite ExtraFrame by auto. exact Ln.
    - apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - exists bi. destruct (ExtraApart bi ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A).
      repeat split; try assumption. rewrite ExtraFrame by auto. exact Li.
    - rewrite BY. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto.
    - rewrite BX. apply NewValues. unfold V293_rekey_new_bindings; simpl; tauto. }
  destruct (V293_task_prio_tcb_update_execution P ks ge le Mg ptcb newprio yn xi byn xn bc bt base new
    N Base Limit Bc CT Hptr Operands WG)
    as (Suffix & Updated & Pointer & FinalOperands & Writable & TF).
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (RF : forall tp c i, c <> bt -> load tp Mh (c,i) = load tp Mg (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j. apply TF. left. exact A. }
  assert (Untouched : forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)).
  { intros i I. rewrite TF by (right; exact I). apply TC. }
  assert (FinalInternalEvent : load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ M Mh).
    - exact Event.
    - intros k K. cbn [typelen] in K. apply Untouched. left. lia. }
  assert (EventBefore : forall i, get Mf (be,i) = get M (be,i)).
  { intro i. unfold Mf,V293_ready_branch_memory.
    destruct (V293_ready_test_flag lo hi old);
      try (unfold V293_rekey_ready_memory;
        repeat rewrite V293_put_byte_other by congruence;
        destruct (_ =? 0); repeat rewrite V293_put_byte_other by congruence);
      unfold Mr,V293_tcb_read_memory;
      repeat rewrite V293_put_byte_other by congruence;
      rewrite (V293_storebytes_outside _ _ _ _ _ _ _ S2) by (left; congruence);
      rewrite (V293_storebytes_outside _ _ _ _ _ _ _ S1) by (left; congruence);
      reflexivity. }
  assert (EventHeader : forall i, (i < ebase+10 \/ ebase+12 < i)%Z ->
    get Mh (be,i) = get M (be,i)).
  { intros i I. rewrite TF by (left; congruence).
    unfold Mg. rewrite V293_event_rekey_byte_frame by (try assumption; right; exact I).
    rewrite (V293_storebytes_outside _ _ _ _ _ _ _ Store) by (left; congruence).
    apply EventBefore. }
  exists Mg. cbn zeta. fold Mh. split.
  { eapply V293_writable_trans with (M2:=M1).
    - eapply V293_store_writable;exact S1.
    - eapply V293_writable_trans with (M2:=M2).
      + eapply V293_store_writable;exact S2.
      + eapply V293_writable_trans with (M2:=Mr).
        * unfold Mr. V293_writable_pure.
        * eapply V293_writable_trans with (M2:=Mf).
          -- unfold Mf. V293_writable_pure.
          -- eapply V293_writable_trans with (M2:=Me).
             ++ eapply V293_store_writable;exact Store.
             ++ eapply V293_writable_trans with (M2:=Mg); [unfold Mg;V293_writable_pure|unfold Mh;V293_writable_pure]. }
  split.
  - unfold V293_task_prio_prefix_event_update. eapply V293_rekey_sequence_execution; eassumption.
  - split; [exact Updated | ]. split.
    + unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalLoads.
    + split; [intros p R; rewrite RF by congruence; exact (FinalView p R) | ].
      split; [rewrite RF by congruence; exact OldSlot | ].
      split; [rewrite RF by congruence; exact NewSlot | ]. split.
      * unfold V293_event_bitmap_loads in *. repeat rewrite RF by congruence. exact FinalEvent.
      * split; [rewrite RF by congruence; exact Read | ].
        split; [exact Pointer | ]. split; [exact Writable | ].
        split; [exact FinalInternalEvent | ]. split; [exact Untouched | ].
        split; [ | exact EventHeader ].
        intros c i A B C D E F G H' J. rewrite TF by auto. apply Frame; assumption.
Qed.

(* Compatibility: the original public contract is an exact projection. *)
Theorem V293_task_prio_prefix_event_update_preserves_writable :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  V293_rekey_locals ge le M br bg (V293_rekey_new_bindings yn xn byn new) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  load Tint8 M (bi,0%Z) = Some (V293_byteval (V293_prio_bit new)) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi Li ExtraApart NewTcbApart TW.
  destruct (V293_task_prio_prefix_event_update_preserves_writable_event_frame P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewLoc NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi Li ExtraApart NewTcbApart TW) as [Mg Result].
  exists Mg. cbn zeta in *. tauto.
Qed.


Theorem V293_task_prio_coordinates_update_execution_writable_event_frame :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mh (be,i) = get M (be,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW.
  assert (SourceApart : forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx -> c <> bn).
  { intros c I. destruct (CoordApart c I) as (_ & _ & A & _). exact A. }
  destruct (V293_task_prio_coordinates_execution P ks ge le M newprio yn xi byn xn bn ny bi nby nbx new
    N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW)
    as (Coordinates & NewY & NewI & NewBY & NewBX & NewSource & CoordFrame).
  set (Mc := V293_coordinate_memory M ny bi nby nbx new) in *.
  assert (Safe : forall c, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    c <> ny /\ c <> bi /\ c <> nby /\ c <> nbx).
  { intros c I.
    pose proof (CoordApart ny ltac:(auto)) as A.
    pose proof (CoordApart bi ltac:(auto)) as B.
    pose proof (CoordApart nby ltac:(auto)) as C.
    pose proof (CoordApart nbx ltac:(auto)) as D.
    cbn in I. intuition congruence. }
  assert (CF : forall c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    get Mc (c,i) = get M (c,i)).
  { intros c i I. destruct (Safe c I) as (A & B & C & D).
    apply CoordFrame; congruence. }
  assert (LF : forall tp c i, In c [b;bo;bn;bc;bt;dy;dby;dx;br;bg;bp;be] ->
    load tp Mc (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF. exact I. }
  assert (NewLoc : V293_rekey_locals ge le Mc br bg (V293_rekey_new_bindings yn xn byn new)).
  { destruct (V293_prio_coordinates new N) as [Y X].
    destruct (V293_mask_byte_value (V293_prio_row new) ltac:(lia)) as [_ MY].
    destruct (V293_mask_byte_value (V293_prio_bit new) X) as [_ MX].
    intros x v I. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v.
    - exists ny. destruct (CoordApart ny ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; assumption.
    - exists nbx. destruct (CoordApart nbx ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MX. exact NewBX.
    - exists nby. destruct (CoordApart nby ltac:(auto)) as (_ & _ & _ & _ & _ & _ & _ & _ & A & B & _).
      repeat split; try assumption. rewrite <- MY. exact NewBY. }
  assert (Resources :
    load Tint8 Mc (bo,0%Z) = Some (V293_byteval old) /\
    load (Tptr V293_tcb_type) Mc (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
    V293_bytes_writable Mc b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Mc b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Mc b entries /\
    V293_tcb_old_loads Mc bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Mc (dy,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dby,0%Z) = Some (true,v)) /\
    (exists v, get Mc (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Mc br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Mc br bg /\
    V293_bytes_writable Mc bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Mc (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
    V293_event_bitmap_loads Mc be ebase elo ehi (V293_ready_group elo ehi) /\
    V293_event_bitmap_writable Mc be ebase /\
    V293_tcb_update_writable Mc bt base).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_event_bitmap_loads,V293_event_bitmap_writable,V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; tauto).
    repeat rewrite CF by (simpl; tauto).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; tauto). apply Wo. exact K.
    - intros k K. rewrite CF by (simpl; tauto). apply Wn. exact K.
    - intros p R. rewrite LF by (simpl; tauto). apply View. exact R.
    - intros k K. rewrite CF by (simpl; tauto). apply We. exact K.
    - intros d D. rewrite CF by (simpl; tauto). apply TW. exact D. }
  destruct Resources as (Clo & Clp & Cwo & Cwn & Cview & Cfields & Cwy & Cwby & Cwx & Cloads & Cw & Cwe & Cevent & Celoads & Cew & Ctw).
  destruct (V293_task_prio_prefix_event_update_preserves_writable_event_frame P ks ge le Mc table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Clo NewSource Clp Cwo Cwn Len Cview By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Cfields
    Cwy Cwby Cwx Cloads Cw NewLoc NewApart Be Cwe Cevent Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit Celoads Cew LocalApart CT CP CE TP TE Bi NewI ExtraApart NewTcbApart Ctw)
    as (Mg & PrefixWritable & Exec & Updated & Ready & Table & OldSlot & NewSlot & EventOut & Read & Pointer & Writable & Internal & Untouched & Frame & EventHeader).
  exists Mg. cbn zeta in *. split.
  { eapply V293_writable_trans with (M2:=Mc); [unfold Mc;V293_writable_pure|exact PrefixWritable]. }
  split.
  - unfold V293_task_prio_coordinates_update.
    eapply V293_rekey_sequence_execution; [ | exact Exec].
    intro tail. destruct (V293_task_prio_coordinates_execution P tail ge le M newprio yn xi byn xn bn ny bi nby nbx new
      N Bn NBy Bi NBby NBx Ln SourceApart NYI NYBY NYBX NIBY NIBX NBYBX CoordW) as [E _]. exact E.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact EventOut | ].
    split; [exact Read | ]. split; [exact Pointer | ]. split; [exact Writable | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF. simpl; tauto.
    + split.
      * intros c i A B C D E F G H' J NY NI NBY NBX.
        rewrite Frame by assumption. apply CoordFrame; congruence.
      * intros i I. rewrite EventHeader by exact I. apply CF. simpl; auto 20.
Qed.

(* Compatibility: the original public contract is an exact projection. *)
Theorem V293_task_prio_coordinates_update_execution_writable :
  forall P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr base)) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    cstepstar P (curs (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi),
    (kenil,ks)) (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mh) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW.
  destruct (V293_task_prio_coordinates_update_execution_writable_event_frame P ks ge le M table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx O N ON L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Lp Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW) as [Mg Result].
  exists Mg. cbn zeta in *. tauto.
Qed.


Theorem V293_critical_event_update_execution_writable_event_frame :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    V293_local_steps P (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mh (be,i) = get M (be,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_primitive_entry_success_writable P
    (kseq (sseq (V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi) (sprim excrit)) ks)
    ge le M table oldprio newprio ptcb current reserved
    b bo bn bc bcur bct curbase initial new curprio (bt,Int.repr base) rb
    Input N O Nt Gt Bo Bn Bc Lo Ln Empty Slot Tbo Tbc Onew Cnew CO Self Nreserved Greserved Token CW)
    as (Ma & EntryWritable & Different & Entry & Aold & Anew & Pointer & ASlot & AEmpty & ACW & EntryFrame).
  assert (CF : forall c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    get Ma (c,i) = get M (c,i)).
  { intros c i I. destruct (EntryApart c I) as [A B]. apply EntryFrame; assumption. }
  assert (LF : forall tp c i, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    load tp Ma (c,i) = load tp M (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j. apply CF; exact I. }
  assert (Resources :
    V293_bytes_writable Ma b (4*Z.of_nat old)%Z 4 /\
    V293_bytes_writable Ma b (4*Z.of_nat new)%Z 4 /\
    V293_table_loads V293_tcb_type Ma b entries /\
    V293_tcb_old_loads Ma bt base (V293_prio_row old) (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) /\
    (exists v, get Ma (dy,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dby,0%Z) = Some (true,v)) /\
    (exists v, get Ma (dx,0%Z) = Some (true,v)) /\
    V293_rekey_bitmap_loads Ma br bg lo hi (V293_ready_group lo hi) /\
    V293_rekey_bitmap_writable Ma br bg /\
    V293_bytes_writable Ma bp 0%Z 4 /\
    load (Tcom_ptr 411%Z) Ma (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
    V293_event_bitmap_loads Ma be ebase elo ehi (V293_ready_group elo ehi) /\
    V293_event_bitmap_writable Ma be ebase /\
    V293_tcb_update_writable Ma bt base /\
    (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
      exists v, get Ma (c,0%Z) = Some (true,v))).
  { unfold V293_bytes_writable,V293_table_loads,V293_tcb_old_loads,
      V293_rekey_bitmap_loads,V293_rekey_bitmap_writable,
      V293_event_bitmap_loads,V293_event_bitmap_writable,V293_tcb_update_writable in *.
    repeat rewrite LF by (simpl; auto 20).
    repeat rewrite CF by (simpl; auto 20).
    repeat split; try tauto.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wo; exact K.
    - intros k K. rewrite CF by (simpl; auto 20). apply Wn; exact K.
    - intros p R. rewrite LF by (simpl; auto 20). apply View; exact R.
    - intros k K. rewrite CF by (simpl; auto 20). apply We; exact K.
    - intros d D. rewrite CF by (simpl; auto 20). apply TW; exact D.
    - intros c I. destruct I as [-> | [-> | [-> | ->]]]; rewrite CF by (simpl; auto 20); apply CoordW; auto. }
  destruct Resources as (AWo & AWn & AView & AFields & AWy & AWby & AWx & ALoads & AW & AWe & AEvent & AELoads & AEW & ATW & ACoordW).
  destruct (V293_task_prio_coordinates_update_execution_writable_event_frame P (kseq (sprim excrit) ks) ge le Ma table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi old new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    O ltac:(clear -N; lia) Different L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Aold Anew Pointer AWo AWn Len AView By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart AFields
    AWy AWby AWx ALoads AW NewApart Be AWe AEvent Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit AELoads AEW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart ATW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart ACoordW)
    as (Mg & UpdateWritable & Exec & Updated & Ready & Table & OldSlot & NewSlot & EventOut & Read & OutPointer & Writable & Internal & Untouched & Frame & EventHeader).
  exists Mg. cbn zeta in *. split.
  { eapply V293_writable_trans; [exact EntryWritable|exact UpdateWritable]. }
  split.
  - eapply V293_success_segment_execution with (Ma:=Ma) (bo:=bo) (bn:=bn) (initial:=initial) (new:=new); eassumption.
  - split; [exact Updated | ]. split; [exact Ready | ]. split; [exact Table | ].
    split; [exact OldSlot | ]. split; [exact NewSlot | ]. split; [exact EventOut | ].
    split; [exact Read | ]. split; [exact OutPointer | ]. split; [exact Writable | ].
    split; [exact Internal | ]. split.
    + intros i I. rewrite Untouched by exact I. apply CF; simpl; auto 20.
    + split.
      * intros c i OB PC A B C D E F G H' J NY NI NBY NBX.
        rewrite Frame by assumption. apply EntryFrame; assumption.
      * intros i I. rewrite EventHeader by exact I. apply CF. simpl; auto 20.
Qed.

(* Compatibility: the original public contract is an exact projection. *)
Theorem V293_critical_event_update_execution_writable :
  forall P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  exists Mg,
  let Mh := V293_tcb_update_memory Mg bt base new in
  let fr := V293_ready_branch_rows lo hi old new in
  let er := V293_ready_rekey_rows elo ehi old new in
V293_preserves_writable M Mh /\
    V293_local_steps P (curs (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi
    current reserved),
    (kenil,ks)) ((ge,le,M),ir,(enabled,si,ci)) (curs (sskip None),(kenil,ks)) ((ge,le,Mh),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mh bt base new /\
  V293_rekey_bitmap_loads Mh br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mh b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat new)%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_event_bitmap_loads Mh be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er)) /\
  load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (be,Int.repr ebase)) /\
  load (Tptr V293_tcb_type) Mh (bc,0%Z) = Some (Vptr (bt,Int.repr base)) /\
  V293_tcb_update_writable Mh bt base /\
  load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall i, (i < base+50)%Z \/ (base+54 < i)%Z -> get Mh (bt,i) = get M (bt,i)) /\
  (forall c i, c <> bo -> c <> bc -> c <> b -> c <> dy -> c <> dby -> c <> dx -> c <> br -> c <> bg -> c <> bp -> c <> be -> c <> bt ->
    c <> ny -> c <> bi -> c <> nby -> c <> nbx ->
    get Mh (c,i) = get M (c,i)).
Proof.
  intros P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg
    Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields
    Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg
    EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW
    NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW
    Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart.
  destruct (V293_critical_event_update_execution_writable_event_frame P ks ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as [Mg Result].
  exists Mg. cbn zeta in *. tauto.
Qed.


(* Original memory to real guarded call, return zero, and free ALL locals. *)
Theorem V293_critical_null_success_return_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some Vnull /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  pose proof (V293_critical_null_update_execution_writable P (kseq (V293_task_prio_success_tail running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [UpdateWritable [Exec Rest]].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & Read & Pointer & Internal & Tail).
    destruct Tail as [Untouched Frame]. apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  assert (FinalWritable : forall c t, In (c,t) (getaddr le) ->
    V293_bytes_writable Mh c 0%Z (typelen t)).
  { intros c t I k K. destruct (InitialWritable c t I k K) as [v W0].
    eapply UpdateWritable;exact W0. }
  destruct (V293_success_tail_return_execution P ks ge le caller Mh ir enabled si ci
    running runblock run sched saved interrupt lock schednew table high target schedcurrent counter
    f body next RunRange NoRun GlobalRun RunLoad Running Call ND FinalWritable)
    as (Mf & Return & FreeFrame & Removed).
  assert (FinalLoad : forall tp c i, In c [b;bt;br;bg] ->
    load tp Mf (c,i) = load tp Mh (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j.
    apply FreeFrame. apply HeapApart;exact I. }
  exists Mf. cbn zeta. fold old. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact Return.
  - destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & Read & Pointer & Internal & Untouched & UFrame).
    split. { unfold V293_tcb_updated_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Updated. }
    split. { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    split. { intros p R. rewrite FinalLoad by (simpl;tauto). exact (Table p R). }
    split. { rewrite FinalLoad by (simpl;tauto). exact Internal. }
    split; [ |exact Removed].
    intros c i NotLocal NotWritten. rewrite FreeFrame by exact NotLocal.
    apply UFrame; clear -NotWritten; simpl in NotWritten;intuition congruence.
Qed.

(* Original memory to real guarded call, return zero, and free ALL locals. *)
Theorem V293_critical_event_success_return_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  pose proof (V293_critical_event_update_execution_writable P (kseq (V293_task_prio_success_tail running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [UpdateWritable [Exec Rest]].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventLoads & Read & Pointer & Writable & Internal & Untouched & Frame). apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  assert (FinalWritable : forall c t, In (c,t) (getaddr le) ->
    V293_bytes_writable Mh c 0%Z (typelen t)).
  { intros c t I k K. destruct (InitialWritable c t I k K) as [v W0].
    eapply UpdateWritable;exact W0. }
  destruct (V293_success_tail_return_execution P ks ge le caller Mh ir enabled si ci
    running runblock run sched saved interrupt lock schednew table high target schedcurrent counter
    f body next RunRange NoRun GlobalRun RunLoad Running Call ND FinalWritable)
    as (Mf & Return & FreeFrame & Removed).
  assert (FinalLoad : forall tp c i, In c [b;bt;br;bg;be] ->
    load tp Mf (c,i) = load tp Mh (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j.
    apply FreeFrame. apply HeapApart;exact I. }
  exists Mf. cbn zeta. fold old. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact Return.
  - destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventReady & Read & Pointer & FinalEW & Internal & Untouched & UFrame).
    split. { unfold V293_tcb_updated_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Updated. }
    split. { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    split. { intros p R. rewrite FinalLoad by (simpl;tauto). exact (Table p R). }
    split. { unfold V293_event_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact EventReady. }
    split. { rewrite FinalLoad by (simpl;tauto). exact Internal. }
    split; [ |exact Removed].
    intros c i NotLocal NotWritten. rewrite FreeFrame by exact NotLocal.
    apply UFrame; clear -NotWritten; simpl in NotWritten;intuition congruence.
Qed.

(* Single-factor counterexample to deriving free permission from a load:
   identical byte and address, change ONLY the permission bit. *)
Theorem V293_success_load_free_permission_ablation : forall (writable : bool),
  let M : mem := set emp (111%positive,0%Z)
    (writable,Byte (Byte.repr (Int.unsigned (Int.repr 7)))) in
  load Tint8 M (111%positive,0%Z) = Some (V293_byteval 7) /\
  free Tint8 111%positive M =
    if writable then Some (del M (111%positive,0%Z)) else None.
Proof.
  intros writable M. split.
  - apply V293_encoded_byte_load with (permission:=writable); [lia| ].
    unfold M. apply map_get_set.
  - unfold free. cbn [typelen freeb].
    unfold M. rewrite map_get_set. destruct writable;reflexivity.
Qed.

(* Concrete simultaneous entries for the complete success-return roots.
   Each branch has one original memory; this does not prove initialization,
   reachability, unlocked dispatch, or a whole-kernel invariant. *)
Definition V293_complete_fixture_ge : env :=
  set (set (set V293_entry_update_fixture_ge 1001%Z (100%positive,Tint8))
    1002%Z (101%positive,Tint8)) 1003%Z (102%positive,Tint8).
Definition V293_complete_fixture_mem (event : bool) : mem :=
  V293_put_byte (V293_put_byte (V293_put_byte
    (if event then V293_entry_update_fixture_mem true true 0 1
     else V293_entry_null_fixture_mem true true 0 1)
    (100%positive,0%Z) 1) (101%positive,0%Z) 1) (102%positive,0%Z) 0.


Lemma V293_complete_fixture_get_frame : forall event c i,
  c<>100%positive -> c<>101%positive -> c<>102%positive ->
  get (V293_complete_fixture_mem event) (c,i) =
  get (if event then V293_entry_update_fixture_mem true true 0 1
       else V293_entry_null_fixture_mem true true 0 1) (c,i).
Proof.
  intros event c i A B C. unfold V293_complete_fixture_mem.
  repeat rewrite V293_put_byte_other by (intro E;inversion E;congruence). reflexivity.
Qed.
Lemma V293_complete_fixture_load_frame : forall event tp c i,
  c<>100%positive -> c<>101%positive -> c<>102%positive ->
  load tp (V293_complete_fixture_mem event) (c,i) =
  load tp (if event then V293_entry_update_fixture_mem true true 0 1
       else V293_entry_null_fixture_mem true true 0 1) (c,i).
Proof.
  intros event tp c i A B C. apply V293_load_block_frame. intro j.
  apply V293_complete_fixture_get_frame;assumption.
Qed.
Local Ltac complete_entry_bind :=
  unfold V293_complete_fixture_ge,V293_entry_update_fixture_ge,V293_tcb_update_fixture_le,
    V293_event_fixture_le,V293_prefix_fixture_ge,V293_prefix_fixture_le,
    V293_read_ready_fixture_le,V293_ready_fragment_fixture_le;
  repeat first [rewrite map_get_set | rewrite map_get_set' by discriminate]; reflexivity.
Local Ltac complete_entry_get :=
  unfold V293_tcb_update_fixture_mem;
  repeat first [rewrite V293_put_byte_other by discriminate | rewrite V293_put_byte_get_same].
Local Ltac complete_entry_load :=
  unfold V293_tcb_update_fixture_mem;
  repeat rewrite V293_put_byte_other_load by discriminate;
  apply V293_put_byte_load; lia.


(* Joint physical entries for the complete roots: not initialization/reachability. *)
Theorem V293_critical_null_success_return_witness : forall ir enabled si ci,
  exists Mf,
  V293_local_steps V293_success_tail_fixture_program
    (curs (sseq (V293_primitive_success_update
      500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z 750%Z 900%Z)
      (V293_task_prio_success_tail 1001%Z 999%Z)),(kenil,kcall 700%Z sret emp kstop))
    ((V293_complete_fixture_ge,V293_tcb_update_fixture_le,V293_complete_fixture_mem false),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
    ((V293_complete_fixture_ge,emp,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 80 0 1 /\
  V293_table_loads V293_tcb_type Mf 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull)
      (Vptr (41%positive,Int.repr 8))) /\
  load (Tcom_ptr 411%Z) Mf (41%positive,36%Z) = Some Vnull /\
  (forall c ty k, In (c,ty) (getaddr V293_tcb_update_fixture_le) -> k < typelen ty ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall c i, In c [100%positive;101%positive;102%positive] ->
    get Mf (c,i) = get (V293_complete_fixture_mem false) (c,i)) /\
  load (Tptr V293_tcb_type) (V293_complete_fixture_mem false) (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_complete_fixture_mem false) (c,0%Z) = Some (V293_byteval 255)).
Proof.
  intros ir enabled si ci.
  destruct (V293_prefix_event_nonnull_entry true 0 1 ltac:(lia) ltac:(lia))
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_null_fixture_mem true true 0 1).
  assert (CF : forall c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem true 0 1) (c,i)).
  { intros. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>41%positive -> c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem true 0 1) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem true 0 1) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some Vnull).
  { unfold M,V293_entry_null_fixture_mem. apply V293_fixture_encoded_load. reflexivity. }
  assert (HighByte : forall i, (40 <= i)%Z ->
    load Tint8 M (41%positive,i) = load Tint8 (V293_entry_update_fixture_mem true true 0 1) (41%positive,i)).
  { intros i I. unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_entry_update_fixture_mem true true 0 1) M).
    - reflexivity.
    - intros k K. unfold M. apply V293_entry_null_fixture_outside. right; right; lia. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads. repeat split; rewrite HighByte by lia;
    apply (eq_trans (V293_load_block_frame _ _ _ _ _ (fun i => V293_entry_update_fixture_frame true true 0 1 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))));
    unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; complete_entry_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if true then 1 else 0)
    (V293_ready_group 16 (if true then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_null_fixture_outside by (left; discriminate); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_null_fixture_outside by (right; right; lia); repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; complete_entry_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if true then 255 else 8))).
  { rewrite (V293_load_block_frame _ (V293_entry_update_fixture_mem true true 0 1) M 51%positive 0%Z (fun i => V293_entry_null_fixture_outside true true 0 1 51%positive i ltac:(left; discriminate))). unfold V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct true; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>41%positive -> c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem true 0 1) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A B. apply V293_load_block_frame. intro j.
    unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; assumption). unfold V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem true 0 1) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M. repeat rewrite V293_entry_null_fixture_outside by (left; discriminate). unfold V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite HighByte by lia. rewrite (V293_load_block_frame _ _ _ 41%positive 58%Z
      (fun i => V293_entry_update_fixture_frame true true 0 1 41%positive i ltac:(discriminate) ltac:(discriminate) ltac:(discriminate))).
    unfold V293_coordinate_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate. complete_entry_load. }
  assert (Addresses : getaddr V293_tcb_update_fixture_le =
    [(32%positive,Tint8);(33%positive,Tint8);(34%positive,Tint8);(35%positive,Tint8);
     (36%positive,Tint8);(37%positive,Tint8);(40%positive,Tptr V293_tcb_type);
     (51%positive,Tint8);(52%positive,Tint8);(70%positive,Tptr V293_event_type);(73%positive,Tint8)]) by reflexivity.
  assert (CoordsW : forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    exists v, get M (c,0%Z) = Some (true,v)).
  { intros c Cases. destruct Cases as [E | [E | [E | [E | F]]]];try contradiction;subst c;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;eexists;apply V293_put_byte_get_same. }
  assert (NewW : exists v,get M (52%positive,0%Z)=Some(true,v)).
  { unfold M. rewrite V293_entry_null_fixture_outside by (left;discriminate).
    rewrite V293_entry_update_fixture_frame by discriminate.
    rewrite V293_coordinate_fixture_delta by (intro E;inversion E;discriminate).
    rewrite V293_tcb_update_fixture_outside by (try discriminate;left;discriminate).
    rewrite V293_prefix_event_nonnull_outside by discriminate.
    rewrite V293_event_fixture_outside by (try discriminate;left;discriminate).
    unfold V293_prefix_fixture_mem. eexists;apply V293_put_byte_get_same. }
  assert (AllWritable : forall c ty, In (c,ty) (getaddr V293_tcb_update_fixture_le) ->
    V293_bytes_writable (V293_complete_fixture_mem false) c 0%Z (typelen ty)).
  { intros c ty I. rewrite Addresses in I.
    repeat destruct I as [E|I];try contradiction;inversion E;subst c ty.
    all: intros k K;rewrite V293_complete_fixture_get_frame by discriminate.
    all: try solve [exact(CW k K)|exact(HWe k K)].
    all: cbn [typelen] in K;assert(k=0) by lia;subst k;cbn [Z.of_nat Z.add];
      first [assumption | apply CoordsW;cbn;tauto]. }
  destruct (V293_critical_null_success_return_execution V293_success_tail_fixture_program
    (kcall 700%Z sret emp kstop) V293_complete_fixture_ge V293_tcb_update_fixture_le emp
    (V293_complete_fixture_mem false) ir enabled si ci
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 1 255 6 V293_prefix_fixture_entries
    600%Z 70%positive 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 80%positive 41%positive 8%Z 99%positive 8
    1001%Z 100%positive 1 999%Z 1004%Z 1002%Z 1003%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z
    700%Z sret kstop)
    as (Mf & Exec & Updated & Ready & Table & Internal & Frame & Removed).

  all: try solve [reflexivity]; try solve [discriminate];
    try solve [change (0<=8)%Z;lia]; try solve [change (8+55<=4294967295)%Z;lia];
    try solve [change (255<256);lia]; try solve [change (8<13);lia];
    try solve [change (6<12);lia]; try solve [change (16<256);lia]; try solve [change (1<256);lia].
  all: try solve [right;reflexivity].
  all: try solve [repeat rewrite V293_complete_fixture_load_frame by discriminate;assumption].
  all: try solve [intros k K; rewrite V293_complete_fixture_get_frame by discriminate;
    first [exact (HWo k K)|exact(HWn k K)|exact(HWe k K)|exact(CW k K)]].
  all: try solve [intros p R;rewrite V293_complete_fixture_load_frame by discriminate;exact(HView p R)].
  all: try solve [unfold V293_tcb_old_loads in *;repeat rewrite V293_complete_fixture_load_frame by discriminate;exact HFields].
  all: try solve [rewrite V293_complete_fixture_get_frame by discriminate;assumption].
  all: try solve [unfold V293_rekey_bitmap_loads in *;repeat rewrite V293_complete_fixture_load_frame by discriminate;exact HLoads].
  all: try solve [unfold V293_rekey_bitmap_writable in *;repeat rewrite V293_complete_fixture_get_frame by discriminate;exact HW].
  all: try solve [intros d D;rewrite V293_complete_fixture_get_frame by discriminate;exact(HTW d D)].
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; split; discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite V293_complete_fixture_get_frame by discriminate;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - rewrite V293_complete_fixture_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear;lia)).
  - rewrite V293_complete_fixture_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear;lia)).
  - intro IsSelf. repeat split; try solve [complete_entry_bind];
      try solve [rewrite V293_complete_fixture_load_frame by discriminate;assumption];
      try solve [rewrite V293_complete_fixture_get_frame by discriminate;assumption];
      try solve [change (0<=8)%Z;lia];try solve [change (8+50<=4294967295)%Z;lia].
  - intros c Cases. cbn in Cases. intuition congruence.
  - unfold V293_complete_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load;lia.
  - intro One. split; [reflexivity | ]. split; [discriminate | ]. split; [discriminate | ].
    exists 101%positive. exists 1. split; [complete_entry_bind | ]. split.
    + unfold V293_complete_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
      apply V293_put_byte_load;lia.
    + split; [lia | left;discriminate].
  - intros x c I Bind. cbn in I. destruct I as [E | [E | [E | F]]];try contradiction;subst x;
      unfold V293_complete_fixture_ge in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind;subst c;cbn;intuition discriminate.
  - rewrite Addresses. repeat constructor;cbn;intuition discriminate.
  - intros c I. rewrite Addresses. cbn in I. destruct I as [E | [E | [E | [E | F]]]];try contradiction;subst c;
      cbn;intuition discriminate.
  - exists Mf. split; [exact Exec | ]. split; [exact Updated | ].
    split; [exact Ready | ]. split; [exact Table | ]. split; [exact Internal | ].
    split; [exact Removed | ]. split.
    + intros c i I. apply Frame; rewrite ?Addresses;clear -I;cbn in *;intuition congruence.
    + split.
      * rewrite V293_complete_fixture_load_frame by discriminate. exact Null.
      * intros c I. rewrite V293_complete_fixture_load_frame by (clear -I;cbn in I;intuition congruence).
        rewrite LF by (clear -I;cbn in I;intuition congruence).
        apply V293_coordinate_fixture_stale;clear -I;cbn in I;intuition congruence.
Qed.

Theorem V293_critical_event_success_return_witness : forall ir enabled si ci,
  exists Mf,
  V293_local_steps V293_success_tail_fixture_program
    (curs (sseq (V293_primitive_success_update
      500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z 750%Z 900%Z)
      (V293_task_prio_success_tail 1001%Z 999%Z)),(kenil,kcall 700%Z sret emp kstop))
    ((V293_complete_fixture_ge,V293_tcb_update_fixture_le,V293_complete_fixture_mem true),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
    ((V293_complete_fixture_ge,emp,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 80 0 1 /\
  V293_table_loads V293_tcb_type Mf 50%positive
    (update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull)
      (Vptr (41%positive,Int.repr 8))) /\
  load (Tcom_ptr 411%Z) Mf (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5)) /\
  V293_event_bitmap_loads Mf 72%positive 5%Z 64 0 1 /\
  (forall c ty k, In (c,ty) (getaddr V293_tcb_update_fixture_le) -> k < typelen ty ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall c i, In c [100%positive;101%positive;102%positive] ->
    get Mf (c,i) = get (V293_complete_fixture_mem true) (c,i)) /\
  load (Tptr V293_tcb_type) (V293_complete_fixture_mem true) (40%positive,0%Z) = Some Vnull /\
  (forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    load Tint8 (V293_complete_fixture_mem true) (c,0%Z) = Some (V293_byteval 255)).
Proof.
  intros ir enabled si ci.
  destruct (V293_prefix_event_nonnull_entry true 0 1 ltac:(lia) ltac:(lia))
    as (Lp & Event & We & Fields & View & Wo & Wn & Wy & Wby & Wx & Loads & W & NewLoc & Lo & Ln & Initial & ELoads & EW).
  set (M := V293_entry_update_fixture_mem true true 0 1).
  assert (CF : forall c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    get M (c,i) = get (V293_coordinate_fixture_mem true 0 1) (c,i)).
  { intros. apply V293_entry_update_fixture_frame; assumption. }
  assert (LF : forall tp c i, c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_coordinate_fixture_mem true 0 1) (c,i)).
  { intros. apply V293_load_block_frame. intro j. apply CF; assumption. }
  assert (RF : forall tp c i, c <> 41%positive -> c <> 73%positive -> c <> 33%positive -> c <> 37%positive -> c <> 35%positive ->
    c<>51%positive -> c<>40%positive -> c<>80%positive ->
    load tp M (c,i) = load tp (V293_prefix_event_nonnull_mem true 0 1) (c,i)).
  { intros. rewrite LF by assumption. apply V293_load_block_frame. intro j.
    rewrite V293_coordinate_fixture_delta by (intro E; inversion E; congruence).
    apply V293_tcb_update_fixture_outside; [assumption | left; assumption]. }
  assert (HEvent : load (Tcom_ptr 411%Z) M (41%positive,36%Z) = Some (Vptr (72%positive,Int.repr 5))).
  { unfold load,loadm. rewrite (V293_loadbytes_ext _ (V293_prefix_event_nonnull_mem true 0 1) M).
    - exact Event.
    - intros k K. cbn [typelen] in K.
      unfold M. rewrite V293_entry_update_fixture_frame by discriminate. rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate).
      apply V293_tcb_update_fixture_outside; [discriminate | right; left; lia]. }
  assert (HFields : V293_tcb_old_loads M 41%positive 8%Z 1 2 1).
  { unfold V293_tcb_old_loads; repeat rewrite LF by discriminate; unfold V293_coordinate_fixture_mem; repeat rewrite V293_put_byte_other_load by discriminate; repeat split; complete_entry_load. }
  assert (HView : V293_table_loads V293_tcb_type M 50%positive V293_prefix_fixture_entries).
  { intros p R. rewrite RF by discriminate. exact (View p R). }
  assert (HWo : V293_bytes_writable M 50%positive 32%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wo k K). }
  assert (HWn : V293_bytes_writable M 50%positive 24%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (Wn k K). }
  assert (HWe : V293_bytes_writable M 70%positive 0%Z 4).
  { intros k K. unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact (We k K). }
  assert (HWy : exists v, get M (32%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wy. }
  assert (HWby : exists v, get M (36%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wby. }
  assert (HWx : exists v, get M (34%positive,0%Z) = Some (true,v)).
  { unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact Wx. }
  assert (HLoads : V293_rekey_bitmap_loads M 30%positive 31%positive 16 (if true then 1 else 0)
    (V293_ready_group 16 (if true then 1 else 0))).
  { unfold V293_rekey_bitmap_loads in *. repeat rewrite RF by discriminate. exact Loads. }
  assert (HW : V293_rekey_bitmap_writable M 30%positive 31%positive).
  { unfold V293_rekey_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact W. }
  assert (HELoads : V293_event_bitmap_loads M 72%positive 5%Z 0 1 (V293_ready_group 0 1)).
  { unfold V293_event_bitmap_loads in *. repeat rewrite RF by discriminate. exact ELoads. }
  assert (HEW : V293_event_bitmap_writable M 72%positive 5%Z).
  { unfold V293_event_bitmap_writable in *.
    unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate); repeat rewrite V293_tcb_update_fixture_outside by (try discriminate; left; discriminate). exact EW. }
  assert (HLn : load Tint8 M (52%positive,0%Z) = Some (V293_byteval 6)).
  { rewrite RF by discriminate. exact Ln. }
  assert (HTW : V293_tcb_update_writable M 41%positive 8%Z).
  { intros d D. assert (d=50 \/ d=51 \/ d=52 \/ d=53 \/ d=54)%Z by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; unfold M; repeat rewrite V293_entry_update_fixture_frame by discriminate; repeat rewrite V293_coordinate_fixture_delta by (intro Eq; inversion Eq; discriminate);
      eexists; complete_entry_get; reflexivity. }
  assert (HLo : load Tint8 M (51%positive,0%Z) = Some (V293_byteval (if true then 255 else 8))).
  { unfold M,V293_entry_update_fixture_mem. apply V293_put_byte_load. destruct true; lia. }
  assert (SelectorW : exists v, get M (51%positive,0%Z) = Some (true,v)).
  { unfold M,V293_entry_update_fixture_mem. eexists. apply V293_put_byte_get_same. }
  assert (OuterLF : forall tp c i, c<>51%positive ->
    load tp M (c,i) = load tp
      (V293_fixture_put_bytes
        (V293_fixture_put_bytes (V293_coordinate_fixture_mem true 0 1) 40%positive 0%Z
          (encode_val (Tptr V293_tcb_type) Vnull))
        80%positive 0%Z (encode_val (Tptr V293_tcb_type) (Vptr (41%positive,Int.repr 8)))) (c,i)).
  { intros tp c i A. apply V293_load_block_frame. intro j.
    unfold M,V293_entry_update_fixture_mem.
    apply V293_put_byte_other. intro E; inversion E; congruence. }
  assert (Current : load (Tptr V293_tcb_type) M (80%positive,0%Z) = Some (Vptr (41%positive,Int.repr 8))).
  { rewrite OuterLF by discriminate. apply V293_fixture_pointer_load. reflexivity. }
  assert (Null : load (Tptr V293_tcb_type) M (40%positive,0%Z) = Some Vnull).
  { rewrite OuterLF by discriminate. unfold load,loadm. rewrite V293_loadbytes_ext with
      (M:=V293_fixture_put_bytes (V293_coordinate_fixture_mem true 0 1) 40%positive 0%Z
        (encode_val (Tptr V293_tcb_type) Vnull)).
    - apply V293_fixture_pointer_load. reflexivity.
    - intros k K. apply V293_fixture_bytes_outside. left; discriminate. }
  assert (CW : V293_bytes_writable M 40%positive 0%Z 4).
  { intros k K. unfold M,V293_entry_update_fixture_mem.
    rewrite V293_put_byte_other by discriminate.
    rewrite V293_fixture_bytes_outside by (left; discriminate).
    eexists. apply V293_fixture_bytes_nth. rewrite encode_val_length; exact K. }
  assert (Prio : load Tint8 M (41%positive,58%Z) = Some (V293_byteval 8)).
  { rewrite LF by discriminate. unfold V293_coordinate_fixture_mem.
    repeat rewrite V293_put_byte_other_load by discriminate. complete_entry_load. }
  assert (Addresses : getaddr V293_tcb_update_fixture_le =
    [(32%positive,Tint8);(33%positive,Tint8);(34%positive,Tint8);(35%positive,Tint8);
     (36%positive,Tint8);(37%positive,Tint8);(40%positive,Tptr V293_tcb_type);
     (51%positive,Tint8);(52%positive,Tint8);(70%positive,Tptr V293_event_type);(73%positive,Tint8)]) by reflexivity.
  assert (CoordsW : forall c, In c [33%positive;73%positive;37%positive;35%positive] ->
    exists v, get M (c,0%Z) = Some (true,v)).
  { intros c Cases. destruct Cases as [E | [E | [E | [E | F]]]];try contradiction;subst c;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;eexists;apply V293_put_byte_get_same. }
  assert (NewW : exists v,get M (52%positive,0%Z)=Some(true,v)).
  { unfold M.
    rewrite V293_entry_update_fixture_frame by discriminate.
    rewrite V293_coordinate_fixture_delta by (intro E;inversion E;discriminate).
    rewrite V293_tcb_update_fixture_outside by (try discriminate;left;discriminate).
    rewrite V293_prefix_event_nonnull_outside by discriminate.
    rewrite V293_event_fixture_outside by (try discriminate;left;discriminate).
    unfold V293_prefix_fixture_mem. eexists;apply V293_put_byte_get_same. }
  assert (AllWritable : forall c ty, In (c,ty) (getaddr V293_tcb_update_fixture_le) ->
    V293_bytes_writable (V293_complete_fixture_mem true) c 0%Z (typelen ty)).
  { intros c ty I. rewrite Addresses in I.
    repeat destruct I as [E|I];try contradiction;inversion E;subst c ty.
    all: intros k K;rewrite V293_complete_fixture_get_frame by discriminate.
    all: try solve [exact(CW k K)|exact(HWe k K)].
    all: cbn [typelen] in K;assert(k=0) by lia;subst k;cbn [Z.of_nat Z.add];
      first [assumption | apply CoordsW;cbn;tauto]. }
  destruct (V293_critical_event_success_return_execution V293_success_tail_fixture_program
    (kcall 700%Z sret emp kstop) V293_complete_fixture_ge V293_tcb_update_fixture_le emp
    (V293_complete_fixture_mem true) ir enabled si ci
    500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z
    50%positive 51%positive 52%positive 40%positive 41%positive 32%positive 36%positive 34%positive
    8%Z 30%positive 31%positive 16 1 255 6 V293_prefix_fixture_entries
    600%Z 70%positive 72%positive 5%Z 0 1 601%Z 73%positive 33%positive 37%positive 35%positive
    750%Z 900%Z 80%positive 41%positive 8%Z 99%positive 8
    1001%Z 100%positive 1 999%Z 1004%Z 1002%Z 1003%Z 1005%Z 1006%Z 1007%Z 1008%Z 1009%Z
    700%Z sret kstop)
    as (Mf & Exec & Updated & Ready & Table & EventReady & Internal & Frame & Removed).

  all: try solve [reflexivity]; try solve [discriminate];
    try solve [change (0<=8)%Z;lia]; try solve [change (8+55<=4294967295)%Z;lia];
    try solve [change (255<256);lia]; try solve [change (8<13);lia];
    try solve [change (6<12);lia]; try solve [change (16<256);lia]; try solve [change (1<256);lia].
  all: try solve [right;reflexivity].
  all: try solve [repeat rewrite V293_complete_fixture_load_frame by discriminate;assumption].
  all: try solve [intros k K; rewrite V293_complete_fixture_get_frame by discriminate;
    first [exact (HWo k K)|exact(HWn k K)|exact(HWe k K)|exact(CW k K)]].
  all: try solve [intros p R;rewrite V293_complete_fixture_load_frame by discriminate;exact(HView p R)].
  all: try solve [unfold V293_tcb_old_loads in *;repeat rewrite V293_complete_fixture_load_frame by discriminate;exact HFields].
  all: try solve [rewrite V293_complete_fixture_get_frame by discriminate;assumption].
  all: try solve [unfold V293_rekey_bitmap_loads in *;repeat rewrite V293_complete_fixture_load_frame by discriminate;exact HLoads].
  all: try solve [unfold V293_rekey_bitmap_writable in *;repeat rewrite V293_complete_fixture_get_frame by discriminate;exact HW].
  all: try solve [intros d D;rewrite V293_complete_fixture_get_frame by discriminate;exact(HTW d D)].
  all: try solve [change (0<=5)%Z;lia];try solve [change (5+12<=4294967295)%Z;lia];try solve [change (0<256);lia].
  all: try solve [unfold V293_event_bitmap_loads in *;repeat rewrite V293_complete_fixture_load_frame by discriminate;exact HELoads].
  all: try solve [unfold V293_event_bitmap_writable in *;repeat rewrite V293_complete_fixture_get_frame by discriminate;exact HEW].
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; repeat split; discriminate.
  - intros x v c I Bind. cbn [V293_rekey_ready_bindings In] in I.
    destruct I as [E|[E|[E|[E|[E|[E|F]]]]]];try contradiction;inversion E;subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind|rewrite map_get_set' in Bind by discriminate];
      inversion Bind;subst c;split;discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros x v c I Bind. cbn [V293_rekey_new_bindings In] in I.
    destruct I as [E|[E|[E|F]]]; try contradiction; inversion E; subst x v;
      unfold V293_tcb_update_fixture_le,V293_event_fixture_le,V293_prefix_fixture_le,V293_read_ready_fixture_le,V293_ready_fragment_fixture_le in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind; subst c; discriminate.
  - intros c Cases. cbn in Cases. intuition congruence.
  - intros c Cases. destruct Cases as [-> | [-> | [-> | ->]]];
      rewrite V293_complete_fixture_get_frame by discriminate;
      rewrite CF by discriminate; unfold V293_coordinate_fixture_mem;
      repeat rewrite V293_put_byte_other by discriminate;
      eexists; apply V293_put_byte_get_same.
  - rewrite V293_complete_fixture_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,24%Z) = Some (nth 6 V293_prefix_fixture_entries Vnull)).
    exact (HView 6 ltac:(clear;lia)).
  - rewrite V293_complete_fixture_load_frame by discriminate.
    change (load (Tptr V293_tcb_type) M (50%positive,32%Z) = Some (nth 8 V293_prefix_fixture_entries Vnull)).
    exact (HView 8 ltac:(clear;lia)).
  - intro IsSelf. repeat split; try solve [complete_entry_bind];
      try solve [rewrite V293_complete_fixture_load_frame by discriminate;assumption];
      try solve [rewrite V293_complete_fixture_get_frame by discriminate;assumption];
      try solve [change (0<=8)%Z;lia];try solve [change (8+50<=4294967295)%Z;lia].
  - intros c Cases. cbn in Cases. intuition congruence.
  - unfold V293_complete_fixture_mem. repeat rewrite V293_put_byte_other_load by discriminate.
    apply V293_put_byte_load;lia.
  - intro One. split; [reflexivity | ]. split; [discriminate | ]. split; [discriminate | ].
    exists 101%positive. exists 1. split; [complete_entry_bind | ]. split.
    + unfold V293_complete_fixture_mem. rewrite V293_put_byte_other_load by discriminate.
      apply V293_put_byte_load;lia.
    + split; [lia | left;discriminate].
  - intros x c I Bind. cbn in I. destruct I as [E | [E | [E | F]]];try contradiction;subst x;
      unfold V293_complete_fixture_ge in Bind;
      repeat first [rewrite map_get_set in Bind | rewrite map_get_set' in Bind by discriminate];
      inversion Bind;subst c;cbn;intuition discriminate.
  - rewrite Addresses. repeat constructor;cbn;intuition discriminate.
  - intros c I. rewrite Addresses. cbn in I. destruct I as [E | [E | [E | [E | [E | F]]]]];try contradiction;subst c;
      cbn;intuition discriminate.
  - exists Mf. split; [exact Exec | ]. split; [exact Updated | ].
    split; [exact Ready | ]. split; [exact Table | ]. split; [exact Internal | ].
    split; [exact EventReady | ].
    split; [exact Removed | ]. split.
    + intros c i I. apply Frame; rewrite ?Addresses;clear -I;cbn in *;intuition congruence.
    + split.
      * rewrite V293_complete_fixture_load_frame by discriminate. exact Null.
      * intros c I. rewrite V293_complete_fixture_load_frame by (clear -I;cbn in I;intuition congruence).
        rewrite LF by (clear -I;cbn in I;intuition congruence).
        apply V293_coordinate_fixture_stale;clear -I;cbn in I;intuition congruence.
Qed.


Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.

(* A ready-only abstract primitive, not the complete API specification.  Its
   frame rule is the framework spec_prim_step, not an assumed execution. *)
Definition V293_ready_prio_step (next : tid) (old new : nat) : osabstep :=
  fun args O result =>
    args = nil /\ old < 13 /\ new < 12 /\
    exists tasks message,
      get O abstcblsid = Some (abstcblist tasks) /\
      get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) /\
      (forall t status msg, get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)) /\
      result = (Some (Vint32 Int.zero),
        set O abstcblsid (abstcblist
          (set tasks next (Int.repr (Z.of_nat new),rdy,message)))).

Lemma V293_ready_prio_eqdom : forall O tasks next old new message,
  get O abstcblsid = Some (abstcblist tasks) ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  eqdomO O (set O abstcblsid
    (abstcblist (set tasks next (Int.repr (Z.of_nat new),rdy,message)))).
Proof.
  intros O tasks next old new message Table Task. split.
  - intro id. unfold indom.
    destruct (OSAbstMod.eq_dec id abstcblsid) as [-> | Ne].
    + rewrite map_get_set. split; intros; eauto.
    + split; intros [v V]; exists v.
      * rewrite map_get_set' by congruence. exact V.
      * rewrite map_get_set' in V by congruence. exact V.
  - intros ts T. rewrite Table in T. inversion T; subst ts.
    exists (set tasks next (Int.repr (Z.of_nat new),rdy,message)).
    split; [apply map_get_set | ]. unfold eqdomtls. intro t. unfold indom.
    change ((exists v, get tasks t = Some v) <->
      (exists v, get (set tasks next (Int.repr (Z.of_nat new),rdy,message)) t = Some v)).
    destruct (TcbMod.eq_dec t next) as [-> | Ne].
    + split; intros; [eexists; apply map_get_set | eexists; exact Task].
    + split; intros [v V]; exists v.
      * rewrite map_get_set' by congruence. exact V.
      * rewrite map_get_set' in V by congruence. exact V.
Qed.

Lemma V293_ready_prio_shared_fields : forall current tasks events now next new message
    ge le M ir aux O op R,
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** R ->
  (ge,le,M,ir,aux,
    set O abstcblsid (abstcblist (set tasks next (Int.repr (Z.of_nat new),rdy,message))),op)
    |= V293_shared_fields current
      (set tasks next (Int.repr (Z.of_nat new),rdy,message)) events now ** R.
Proof.
  intros current tasks events now next new message ge le M ir aux O op R Hs.
  unfold V293_shared_fields in *.
  assert (Hhead : (ge,le,M,ir,aux,O,op) |=
    Aabsdata abstcblsid (abstcblist tasks) **
    (Aabsdata curtid (oscurt current) **
    ((Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now)) ** R)))
    by (sep auto).
  apply (V293_shared_replace_slot abstcblsid (abstcblist tasks)
    (abstcblist (set tasks next (Int.repr (Z.of_nat new),rdy,message)))) in Hhead.
  clear Hs. sep auto.
Qed.

Theorem V293_ready_prio_owned_step : forall sc current tasks events now next old new message
    ge le M ir aux O op R Of OO,
  old < 13 -> new < 12 ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  (forall t status msg, get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)) ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** R ->
  join O Of OO ->
  exists O' OO',
    O' = set O abstcblsid (abstcblist
      (set tasks next (Int.repr (Z.of_nat new),rdy,message))) /\
    join O' Of OO' /\
    spec_step sc (spec_prim nil (V293_ready_prio_step next old new)) OO
      (spec_done (Some (Vint32 Int.zero))) OO' /\
    (ge,le,M,ir,aux,O',op) |= V293_shared_fields current
      (set tasks next (Int.repr (Z.of_nat new),rdy,message)) events now ** R.
Proof.
  intros sc current tasks events now next old new message ge le M ir aux O op R Of OO
    Old New Task Fresh Owned Frame.
  assert (Table : get O abstcblsid = Some (abstcblist tasks)).
  { change (get (getabst (ge,le,M,ir,aux,O,op)) abstcblsid = Some (abstcblist tasks)).
    eapply V293_star_abst_get_l; [ | exact Owned].
    intros st H. exact (proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))). }
  set (O' := set O abstcblsid (abstcblist
    (set tasks next (Int.repr (Z.of_nat new),rdy,message)))).
  set (OO' := set OO abstcblsid (abstcblist
    (set tasks next (Int.repr (Z.of_nat new),rdy,message)))).
  assert (Frame' : join O' Of OO').
  { unfold O',OO'. eapply OSAbstMod.join_set_l; [exact Frame | ].
    exists (abstcblist tasks). exact Table. }
  exists O'. exists OO'. split; [reflexivity | ]. split; [exact Frame' | ]. split.
  - eapply spec_prim_step with (O:=O) (O':=O') (Of:=Of).
    + unfold V293_ready_prio_step. repeat split; try assumption; try reflexivity.
      exists tasks. exists message. auto.
    + eapply V293_ready_prio_eqdom; eassumption.
    + unfold tidsame,O'. rewrite map_get_set' by discriminate. reflexivity.
    + exact Frame.
    + exact Frame'.
  - apply V293_ready_prio_shared_fields. exact Owned.
Qed.

Lemma V293_ready_test_from_task : forall lo hi tasks next old message,
  old < 13 -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  V293_ready_test_flag lo hi old = true.
Proof.
  intros lo hi tasks next old message Old Bitmap Task.
  assert (Bit : V293_bitmap_ready lo hi old).
  { apply (proj2 (Bitmap old Old)). exists next. exists message. exact Task. }
  unfold V293_ready_test_flag,V293_ready_row,V293_prio_row,V293_prio_bit.
  unfold V293_bitmap_ready in Bit.
  destruct (old <? 8) eqn:E; apply Nat.ltb_lt in E || apply Nat.ltb_ge in E;
    cbn; destruct Bit as [[L B] | [L [U B]]]; try lia; exact B.
Qed.

(* The branch is derived from entry ownership, not a post-state oracle. *)
Theorem V293_ready_prio_branch_relations : forall lo hi entries tasks next old new message,
  old < 13 -> new < 12 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  nth new entries Vnull = Vnull ->
  let rows := V293_ready_branch_rows lo hi old new in
  V293_bitmap_tasks (fst rows) (snd rows)
    (set tasks next (Int.repr (Z.of_nat new),rdy,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next))
    (set tasks next (Int.repr (Z.of_nat new),rdy,message)).
Proof.
  intros lo hi entries tasks next old new message Old New Table Bitmap Task Empty rows.
  unfold rows,V293_ready_branch_rows.
  rewrite (V293_ready_test_from_task _ _ _ _ _ _ Old Bitmap Task).
  split.
  - eapply V293_rekey_ready_tasks_preserved; eauto; lia.
  - eapply V293_rekey_task_table_preserved; eauto; lia.
Qed.

Lemma V293_shared_fields_rebase : forall current tasks events now
    ge le M ir aux O op ge' le' ir' aux' op',
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ->
  (ge',le',M,ir',aux',O,op') |= V293_shared_fields current tasks events now.
Proof.
  intros. unfold V293_shared_fields in *. simpl in *. exact H.
Qed.

Lemma V293_shared_fields_heap_lift : forall current tasks events now
    ge le M ir aux O op Of OO,
  (ge,le,emp,ir,aux,O,op) |= V293_shared_fields current tasks events now ->
  join O Of OO ->
  (ge,le,M,ir,aux,OO,op) |= V293_shared_fields current tasks events now ** Atrue.
Proof.
  intros current tasks events now ge le M ir aux O op Of OO Owned Frame.
  apply sat_split'. exists (emp:mem). exists M. exists O. exists Of.
  split; [apply map_join_comm; apply map_join_emp | ]. split; [exact Frame | ].
  split; [exact Owned | exact I].
Qed.

(* One concrete NULL-event success trace is paired with a genuine owned
   abstract primitive on the SAME entry task map.  This is not a forward
   simulation, full API Hoare triple, ready_inv closure, or reachable state. *)
Theorem V293_critical_ready_owned_success : forall sc events now O Of OO op ir enabled si ci,
  (V293_complete_fixture_ge,V293_tcb_update_fixture_le,emp,ir,(enabled,si,ci),O,op) |=
    V293_shared_fields (41%positive,Int.repr 8) (V293_prefix_fixture_tasks true) events now ->
  join O Of OO ->
  let tasks' := set (V293_prefix_fixture_tasks true) (41%positive,Int.repr 8)
    (Int.repr 6,rdy,Vnull) in
  let entries' := update_nth_val 6 (update_nth_val 8 V293_prefix_fixture_entries Vnull)
    (Vptr (41%positive,Int.repr 8)) in
  exists Mf O' OO',
  join O' Of OO' /\
  spec_step sc (spec_prim nil (V293_ready_prio_step (41%positive,Int.repr 8) 8 6)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps V293_success_tail_fixture_program
    (curs (sseq (V293_primitive_success_update
      500%Z 501%Z 502%Z 400%Z 300%Z 301%Z 302%Z 303%Z 304%Z 305%Z 306%Z 307%Z 600%Z 601%Z 750%Z 900%Z)
      (V293_task_prio_success_tail 1001%Z 999%Z)),(kenil,kcall 700%Z sret emp kstop))
    ((V293_complete_fixture_ge,V293_tcb_update_fixture_le,V293_complete_fixture_mem false),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,kstop))
    ((V293_complete_fixture_ge,emp,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf 41%positive 8%Z 6 /\
  V293_rekey_bitmap_loads Mf 30%positive 31%positive 80 0 1 /\
  V293_table_loads V293_tcb_type Mf 50%positive entries' /\
  load (Tcom_ptr 411%Z) Mf (41%positive,36%Z) = Some Vnull /\
  (forall c ty k, In (c,ty) (getaddr V293_tcb_update_fixture_le) -> k < typelen ty ->
    get Mf (c,Z.of_nat k) = None) /\
  get O' abstcblsid = Some (abstcblist tasks') /\
  (V293_complete_fixture_ge,emp,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields (41%positive,Int.repr 8) tasks' events now ** Atrue /\
  V293_bitmap_tasks 80 0 tasks' /\
  V293_priority_table entries' tasks' /\
  V293_highest_ready tasks' (60%positive,Int.zero).
Proof.
  intros sc events now O Of OO op ir enabled si ci Owned Frame tasks' entries'.
  destruct (V293_prefix_fixture_relations true) as (Table & Bitmap & Task & Empty).
  assert (OwnedEmp : (V293_complete_fixture_ge,V293_tcb_update_fixture_le,emp,ir,
      (enabled,si,ci),O,op) |=
      V293_shared_fields (41%positive,Int.repr 8) (V293_prefix_fixture_tasks true) events now ** Aemp)
    by (apply astar_r_aemp_intro; exact Owned).
  assert (Fresh : forall t status msg,
      get (V293_prefix_fixture_tasks true) t <> Some (Int.repr (Z.of_nat 6),status,msg)).
  { intros t status msg T. pose proof
      (V293_rekey_task_entry V293_prefix_fixture_entries (V293_prefix_fixture_tasks true) t 6 status msg Table ltac:(lia) T) as Entry.
    rewrite Empty in Entry. discriminate. }
  destruct (V293_ready_prio_owned_step sc (41%positive,Int.repr 8)
    (V293_prefix_fixture_tasks true) events now (41%positive,Int.repr 8) 8 6 Vnull
    V293_complete_fixture_ge V293_tcb_update_fixture_le emp ir (enabled,si,ci) O op Aemp Of OO
    ltac:(lia) ltac:(lia) Task Fresh OwnedEmp Frame)
    as (O' & OO' & EqO & Frame' & Abstract & UpdatedOwned).
  apply astar_r_aemp_elim in UpdatedOwned.
  destruct (V293_ready_prio_branch_relations 16 1 V293_prefix_fixture_entries
    (V293_prefix_fixture_tasks true) (41%positive,Int.repr 8) 8 6 Vnull
    ltac:(lia) ltac:(lia) Table Bitmap Task Empty) as [FinalBitmap FinalTable].
  change (V293_bitmap_tasks 80 0 tasks') in FinalBitmap.
  change (V293_priority_table entries' tasks') in FinalTable.
  destruct (V293_critical_null_success_return_witness ir enabled si ci)
    as (Mf & Execute & TCB & Ready & PhysicalTable & NullEvent & Freed & Guards & Initial & Stale).
  assert (Highest : V293_highest_ready tasks' (60%positive,Int.zero)).
  { destruct (V293_ready_selection_task 80 0 entries' tasks' ltac:(lia) ltac:(lia)
      ltac:(exists 4; left; split; [lia | reflexivity]) FinalBitmap FinalTable)
      as (selected & msg & Selected & Pointer & High).
    change (Vptr (60%positive,Int.zero) = Vptr selected) in Pointer.
    inversion Pointer; subst selected. exact High. }
  exists Mf. exists O'. exists OO'.
  split; [exact Frame' | ]. split; [exact Abstract | ]. split; [exact Execute | ].
  split; [exact TCB | ]. split; [exact Ready | ]. split; [exact PhysicalTable | ].
  split; [exact NullEvent | ]. split; [exact Freed | ]. split.
  - rewrite EqO. apply map_get_set.
  - split.
    + eapply V293_shared_fields_heap_lift; [ | exact Frame'].
      eapply V293_shared_fields_rebase; exact UpdatedOwned.
    + split; [exact FinalBitmap | ]. split; [exact FinalTable | exact Highest].
Qed.

(* Semantic, single-factor counterexamples: not failed scripts. *)
Theorem V293_ready_prio_stale_bitmap_rejected :
  ~ V293_bitmap_tasks 80 0 (V293_prefix_fixture_tasks true).
Proof.
  intro Stale. destruct (V293_prefix_fixture_relations true) as (_ & _ & Task & _).
  assert (Bit : V293_bitmap_ready 80 0 8).
  { apply (proj2 (Stale 8 ltac:(lia))). exists (41%positive,Int.repr 8).
    exists Vnull. exact Task. }
  destruct Bit as [[N _] | [_ [_ B]]]; [lia | discriminate].
Qed.

Theorem V293_ready_prio_moving_not_highest :
  ~ V293_highest_ready
    (set (V293_prefix_fixture_tasks true) (41%positive,Int.repr 8) (Int.repr 6,rdy,Vnull))
    (41%positive,Int.repr 8).
Proof.
  intros (p & m & Moving & Minimal).
  rewrite map_get_set in Moving. inversion Moving; subst p m.
  assert (Other : get
    (set (V293_prefix_fixture_tasks true) (41%positive,Int.repr 8) (Int.repr 6,rdy,Vnull))
    (60%positive,Int.zero) = Some (Int.repr 4,rdy,Vnull)).
  { rewrite map_get_set' by discriminate. unfold V293_prefix_fixture_tasks.
    rewrite map_get_set' by discriminate. apply map_get_sig. }
  specialize (Minimal _ _ _ Other). change (6 <= 4)%Z in Minimal. lia.
Qed.


(* Only abstract ownership is transported.  No arbitrary physical R is
   retained across writes or deallocation. *)
Lemma V293_shared_fields_empty_heap : forall current tasks events now
    ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now -> M = emp.
Proof.
  intros current tasks events now ge le M ir aux O op Hs.
  unfold V293_shared_fields in Hs.
  apply sat_split in Hs. destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & H1 & H2).
  destruct H1 as [_ E1]. change (m1 = emp) in E1. subst m1.
  apply sat_split in H2. destruct H2 as (m3 & m4 & o3 & o4 & JM2 & JO2 & H3 & H4).
  destruct H3 as [_ E3]. change (m3 = emp) in E3. subst m3.
  apply sat_split in H4. destruct H4 as (m5 & m6 & o5 & o6 & JM3 & JO3 & H5 & H6).
  destruct H5 as [_ E5]. change (m5 = emp) in E5. subst m5.
  destruct H6 as [_ E6]. change (m6 = emp) in E6. subst m6.
  apply map_join_comm in JM3. apply map_join_emp' in JM3. subst m4.
  apply map_join_comm in JM2. apply map_join_emp' in JM2. subst m2.
  apply map_join_comm in JM. apply map_join_emp' in JM. symmetry. exact JM.
Qed.

Lemma V293_shared_fields_owned_transport : forall current tasks events now
    ge le M ir aux O op R Of OO ge' le' Mf ir' aux' op',
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** R ->
  join O Of OO ->
  (ge',le',Mf,ir',aux',OO,op') |= V293_shared_fields current tasks events now ** Atrue.
Proof.
  intros current tasks events now ge le M ir aux O op R Of OO ge' le' Mf ir' aux' op'
    Owned Frame.
  apply sat_split in Owned.
  destruct Owned as (m1 & m2 & o1 & o2 & JM & JO & Fields & Rest).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as Empty.
  subst m1.
  destruct (map_join_assoc JO Frame) as (other & FinalJoin & RestJoin).
  eapply V293_shared_fields_heap_lift; [ | exact FinalJoin].
  eapply V293_shared_fields_rebase. exact Fields.
Qed.

(* General original entry, not a fixed concrete fixture or execution premise. *)
Theorem V293_critical_ready_null_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bc <> bt -> bc <> bp -> bt <> bp ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),rdy,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  Os' = set Os abstcblsid (abstcblist
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_ready_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some Vnull /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message)) events now ** Atrue /\
  V293_bitmap_tasks (fst fr) (snd fr)
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message)) /\
  exists selected,
    V293_highest_ready
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message)) selected /\
    load (Tptr V293_tcb_type) Mf
      (b,(4*Z.of_nat (V293_ready_select (fst fr) (snd fr)
        (V293_ready_group (fst fr) (snd fr))))%Z) = Some (Vptr selected).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap Task Owned Frame.
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_ready_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new message ge le M ir (enabled,si,ci) Os op R Of OO
    O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  destruct (V293_ready_prio_branch_relations lo hi entries tasks
    (bt,Int.repr base) old new message O N TaskTable Bitmap Task EmptyEntry)
    as [FinalBitmap FinalTable].
  destruct (V293_critical_null_success_return_execution
    P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg CT CP TP Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Execute & TCB & Ready & PhysicalTable & NullEvent & PhysicalFrame & Freed).
  set (fr := V293_ready_branch_rows lo hi old new) in *.
  assert (FinalBounds : fst fr < 256 /\ snd fr < 256).
  { unfold fr,V293_ready_branch_rows.
    rewrite (V293_ready_test_from_task _ _ _ _ _ _ O Bitmap Task).
    apply V293_ready_rekey_bounds; try assumption; clear -N; lia. }
  assert (FinalNonempty : exists p, V293_bitmap_ready (fst fr) (snd fr) p).
  { exists new. apply (proj2 (FinalBitmap new ltac:(clear -N; lia))).
    exists (bt,Int.repr base). exists message. apply map_get_set. }
  destruct (V293_ready_selection_task (fst fr) (snd fr)
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base)))
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),rdy,message))
    (proj1 FinalBounds) (proj2 FinalBounds) FinalNonempty FinalBitmap FinalTable)
    as (selected & selected_message & Selected & SelectedPointer & Highest).
  assert (SelectedRange : V293_ready_select (fst fr) (snd fr)
      (V293_ready_group (fst fr) (snd fr)) < 13).
  { eapply V293_ready_selection_range; [exact (proj1 FinalBounds) |
      exact (proj2 FinalBounds) | reflexivity | exact FinalNonempty]. }
  exists Mf. exists Os'. exists OO'.
  cbn zeta. fold old. fold fr.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Execute | ]. split; [exact TCB | ]. split; [exact Ready | ].
  split; [exact PhysicalTable | ]. split; [exact NullEvent | ].
  split; [exact PhysicalFrame | ]. split; [exact Freed | ]. split.
  - eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame'].
  - split; [exact FinalBitmap | ]. split; [exact FinalTable | ].
    exists selected. split; [exact Highest | ].
    rewrite (PhysicalTable _ SelectedRange).
    exact (f_equal (@Some val) SelectedPointer).
Qed.


(* Waiting-task primitive: changing priority preserves the complete wait
   reason, timeout and message.  It is not the complete API specification. *)
Definition V293_wait_prio_step (next : tid) (old new : nat) : osabstep :=
  fun args O result =>
    args = nil /\ old < 13 /\ new < 12 /\
    exists tasks reason delay message,
      get O abstcblsid = Some (abstcblist tasks) /\
      get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) /\
      (forall t status msg, get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)) /\
      result = (Some (Vint32 Int.zero),
        set O abstcblsid (abstcblist
          (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)))).

Lemma V293_wait_prio_eqdom : forall O tasks next old new reason delay message,
  get O abstcblsid = Some (abstcblist tasks) ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  eqdomO O (set O abstcblsid
    (abstcblist (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)))).
Proof.
  intros O tasks next old new reason delay message Table Task. split.
  - intro id. unfold indom.
    destruct (OSAbstMod.eq_dec id abstcblsid) as [-> | Ne].
    + rewrite map_get_set. split; intros; eauto.
    + split; intros [v V]; exists v.
      * rewrite map_get_set' by congruence. exact V.
      * rewrite map_get_set' in V by congruence. exact V.
  - intros ts T. rewrite Table in T. inversion T; subst ts.
    exists (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)).
    split; [apply map_get_set | ]. unfold eqdomtls. intro t. unfold indom.
    change ((exists v, get tasks t = Some v) <->
      (exists v, get (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) t = Some v)).
    destruct (TcbMod.eq_dec t next) as [-> | Ne].
    + split; intros; [eexists; apply map_get_set | eexists; exact Task].
    + split; intros [v V]; exists v.
      * rewrite map_get_set' by congruence. exact V.
      * rewrite map_get_set' in V by congruence. exact V.
Qed.

Lemma V293_wait_prio_shared_fields : forall current tasks events now next new reason delay message
    ge le M ir aux O op R,
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** R ->
  (ge,le,M,ir,aux,
    set O abstcblsid (abstcblist (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message))),op)
    |= V293_shared_fields current
      (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** R.
Proof.
  intros current tasks events now next new reason delay message ge le M ir aux O op R Hs.
  unfold V293_shared_fields in *.
  assert (Hhead : (ge,le,M,ir,aux,O,op) |=
    Aabsdata abstcblsid (abstcblist tasks) **
    (Aabsdata curtid (oscurt current) **
    ((Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now)) ** R)))
    by (sep auto).
  apply (V293_shared_replace_slot abstcblsid (abstcblist tasks)
    (abstcblist (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)))) in Hhead.
  clear Hs. sep auto.
Qed.

Theorem V293_wait_prio_owned_step : forall sc current tasks events now next old new reason delay message
    ge le M ir aux O op R Of OO,
  old < 13 -> new < 12 ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (forall t status msg, get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)) ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** R ->
  join O Of OO ->
  exists O' OO',
    O' = set O abstcblsid (abstcblist
      (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message))) /\
    join O' Of OO' /\
    spec_step sc (spec_prim nil (V293_wait_prio_step next old new)) OO
      (spec_done (Some (Vint32 Int.zero))) OO' /\
    (ge,le,M,ir,aux,O',op) |= V293_shared_fields current
      (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** R.
Proof.
  intros sc current tasks events now next old new reason delay message ge le M ir aux O op R Of OO
    Old New Task Fresh Owned Frame.
  assert (Table : get O abstcblsid = Some (abstcblist tasks)).
  { change (get (getabst (ge,le,M,ir,aux,O,op)) abstcblsid = Some (abstcblist tasks)).
    eapply V293_star_abst_get_l; [ | exact Owned].
    intros st H. exact (proj1 (proj2 (V293_shared_fields_get _ _ _ _ st H))). }
  set (O' := set O abstcblsid (abstcblist
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)))).
  set (OO' := set OO abstcblsid (abstcblist
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)))).
  assert (Frame' : join O' Of OO').
  { unfold O',OO'. eapply OSAbstMod.join_set_l; [exact Frame | ].
    exists (abstcblist tasks). exact Table. }
  exists O'. exists OO'. split; [reflexivity | ]. split; [exact Frame' | ]. split.
  - eapply spec_prim_step with (O:=O) (O':=O') (Of:=Of).
    + unfold V293_wait_prio_step. repeat split; try assumption; try reflexivity.
      exists tasks. exists reason. exists delay. exists message. auto.
    + eapply V293_wait_prio_eqdom; eassumption.
    + unfold tidsame,O'. rewrite map_get_set' by discriminate. reflexivity.
    + exact Frame.
    + exact Frame'.
  - apply V293_wait_prio_shared_fields. exact Owned.
Qed.

Lemma V293_wait_test_from_task : forall lo hi entries tasks next old reason delay message,
  old < 13 -> V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  V293_ready_test_flag lo hi old = false.
Proof.
  intros lo hi entries tasks next old reason delay message Old Table Bitmap Task.
  assert (NotReady : ~ V293_bitmap_ready lo hi old).
  { intro Bit. destruct (proj1 (Bitmap old Old) Bit) as (t & m & Ready).
    pose proof (V293_rekey_priority_unique entries tasks t next old rdy m
      (wait reason delay) message Table Old Ready Task) as E.
    subst t. rewrite Task in Ready. discriminate. }
  assert (BitFalse : forall row bit, ~ Nat.testbit row bit = true -> Nat.testbit row bit = false).
  { intros row bit H. destruct (Nat.testbit row bit); [contradiction | reflexivity]. }
  unfold V293_ready_test_flag,V293_ready_row,V293_prio_row,V293_prio_bit.
  unfold V293_bitmap_ready in NotReady.
  destruct (old <? 8) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; cbn.
  - apply BitFalse. intro Bit. apply NotReady. left. auto.
  - apply BitFalse. intro Bit. apply NotReady. right. auto.
Qed.

Lemma V293_wait_ready_tasks_preserved : forall lo hi tasks next old new reason delay message,
  V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  V293_bitmap_tasks lo hi
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)).
Proof.
  intros lo hi tasks next old new reason delay message Bitmap Task p P. split.
  - intro Bit. destruct (proj1 (Bitmap p P) Bit) as (t & m & Ready).
    assert (Other : t <> next) by (intro E; subst t; rewrite Task in Ready; discriminate).
    exists t. exists m. rewrite map_get_set' by congruence. exact Ready.
  - intros (t & m & Ready). destruct (TcbMod.eq_dec t next) as [-> | Other].
    + rewrite map_get_set in Ready. discriminate.
    + rewrite map_get_set' in Ready by congruence.
      apply (proj2 (Bitmap p P)). exists t. exists m. exact Ready.
Qed.

(* This relates one event wait-kind's priority bitmap to task-map membership.
   It does not assert the abstract ECB's waiter list or all TCB fields. *)
Definition V293_event_wait_tasks lo hi (tasks : TcbMod.map) (reason : tcbstats) : Prop :=
  forall p, p < 13 ->
    (V293_bitmap_ready lo hi p <->
      exists t delay message,
        get tasks t = Some (Int.repr (Z.of_nat p),wait reason delay,message)).

Theorem V293_event_wait_tasks_rekey : forall elo ehi entries tasks next old new reason delay message,
  old < 13 -> new < 13 ->
  V293_priority_table entries tasks -> V293_event_wait_tasks elo ehi tasks reason ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  V293_event_wait_tasks (fst (V293_ready_rekey_rows elo ehi old new))
    (snd (V293_ready_rekey_rows elo ehi old new))
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) reason.
Proof.
  intros elo ehi entries tasks next old new reason delay message O N Table Bitmap Task p P.
  rewrite V293_ready_rekey_membership by assumption. split.
  - intros [E | [Bit Ne]].
    + subst p. exists next. exists delay. exists message. apply map_get_set.
    + destruct (proj1 (Bitmap p P) Bit) as (t & d & m & T).
      assert (Nt : t <> next).
      { intro E; subst t. rewrite Task in T.
        assert (Eq : Int.repr (Z.of_nat old) = Int.repr (Z.of_nat p)) by congruence.
        pose proof (V293_priority_repr_injective old p O P Eq). congruence. }
      exists t. exists d. exists m. rewrite map_get_set' by congruence. exact T.
  - intros (t & d & m & T). destruct (TcbMod.eq_dec t next) as [E | Ne].
    + subst t. rewrite map_get_set in T. left.
      assert (Eq : Int.repr (Z.of_nat p) = Int.repr (Z.of_nat new)) by congruence.
      eapply V293_priority_repr_injective; eassumption.
    + rewrite map_get_set' in T by congruence. right. split.
      * apply (proj2 (Bitmap p P)). exists t. exists d. exists m. exact T.
      * intro E; subst p.
        pose proof (V293_rekey_priority_unique entries tasks t next old
          (wait reason d) m (wait reason delay) message Table O T Task). contradiction.
Qed.

Theorem V293_wait_prio_branch_relations : forall lo hi elo ehi entries tasks next old new reason delay message,
  old < 13 -> new < 12 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  nth new entries Vnull = Vnull ->
  V293_ready_branch_rows lo hi old new = (lo,hi) /\
  V293_bitmap_tasks lo hi (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next))
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_event_wait_tasks (fst (V293_ready_rekey_rows elo ehi old new))
    (snd (V293_ready_rekey_rows elo ehi old new))
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message)) reason.
Proof.
  intros lo hi elo ehi entries tasks next old new reason delay message O N Table Bitmap Event Task Empty.
  split.
  - unfold V293_ready_branch_rows.
    rewrite (V293_wait_test_from_task _ _ _ _ _ _ _ _ _ O Table Bitmap Task). reflexivity.
  - split.
    + eapply V293_wait_ready_tasks_preserved; eassumption.
    + split.
      * eapply V293_rekey_task_table_preserved; eauto; lia.
      * eapply V293_event_wait_tasks_rekey; eauto; lia.
Qed.

Theorem V293_critical_wait_event_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame.
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_wait_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new reason delay message ge le M ir (enabled,si,ci) Os op R Of OO
    O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  destruct (V293_wait_prio_branch_relations lo hi elo ehi entries tasks
    (bt,Int.repr base) old new reason delay message O N TaskTable Bitmap EventBitmap Task EmptyEntry)
    as (Branch & FinalBitmap & FinalTable & FinalEvent).
  destruct (V293_critical_event_success_return_execution P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Execute & TCB & Ready & PhysicalTable & PhysicalEvent & Internal & PhysicalFrame & Freed).
  fold old in Ready. rewrite Branch in Ready. cbn [fst snd] in Ready.
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Execute | ]. split; [exact TCB | ]. split; [exact Ready | ].
  split; [exact PhysicalTable | ]. split; [exact PhysicalEvent | ]. split; [exact Internal | ].
  split; [exact PhysicalFrame | ]. split; [exact Freed | ]. split.
  - eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame'].
  - split; [exact FinalBitmap | ]. split; [exact FinalTable | ]. split; [exact FinalEvent | ].
    split; [apply map_get_set | ]. intros p msg. rewrite map_get_set. discriminate.
Qed.

(* Same concrete event return, with the target TCB byte frame retained.
   Historical interfaces above stay unchanged. *)
Theorem V293_critical_event_return_tcb_frame_event_frame :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  pose proof (V293_critical_event_update_execution_writable_event_frame P (kseq (V293_task_prio_success_tail running sched) ks) ge le M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart) as Original.
  destruct Original as [Mg Result]. cbn zeta in Result |- *.
  destruct Result as [UpdateWritable [Exec Rest]].
  set (Mh := V293_tcb_update_memory Mg bt base new) in *.
  assert (Frame : forall c i, ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] -> get Mh (c,i) = get M (c,i)).
  { intros c i NotWritten. destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventLoads & Read & Pointer & Writable & Internal & Untouched & Frame & EventHeader). apply Frame; clear - NotWritten; simpl in NotWritten;intuition congruence. }
  assert (RunLoad : load Tint8 Mh (runblock,0%Z) = Some (V293_byteval run)).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;eapply Away with (x:=running);simpl;eauto | exact LoadRun]. }
  assert (Running : run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge Mh interrupt lock).
  { intro One. destruct (WhenRunning One) as (Program & SI & SL & Blocked).
    split; [exact Program | ]. split; [exact SI | ]. split; [exact SL | ].
    eapply V293_success_sched_blocked_frame; [ | exact Frame | exact Blocked].
    intros x c X G. eapply Away with (x:=x); [simpl in X |- *;tauto | exact G]. }
  assert (FinalWritable : forall c t, In (c,t) (getaddr le) ->
    V293_bytes_writable Mh c 0%Z (typelen t)).
  { intros c t I k K. destruct (InitialWritable c t I k K) as [v W0].
    eapply UpdateWritable;exact W0. }
  destruct (V293_success_tail_return_execution P ks ge le caller Mh ir enabled si ci
    running runblock run sched saved interrupt lock schednew table high target schedcurrent counter
    f body next RunRange NoRun GlobalRun RunLoad Running Call ND FinalWritable)
    as (Mf & Return & FreeFrame & Removed).
  assert (FinalLoad : forall tp c i, In c [b;bt;br;bg;be] ->
    load tp Mf (c,i) = load tp Mh (c,i)).
  { intros tp c i I. apply V293_load_block_frame. intro j.
    apply FreeFrame. apply HeapApart;exact I. }
  exists Mf. cbn zeta. fold old. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans; [exact Exec | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact Return.
  - destruct Rest as (Updated & Ready & Table & OldSlot & NewSlot & EventReady & Read & Pointer & FinalEW & Internal & Untouched & UFrame & EventHeader).
    split. { unfold V293_tcb_updated_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Updated. }
    split. { unfold V293_rekey_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact Ready. }
    split. { intros p R. rewrite FinalLoad by (simpl;tauto). exact (Table p R). }
    split. { unfold V293_event_bitmap_loads in *. repeat rewrite FinalLoad by (simpl;tauto). exact EventReady. }
    split. { rewrite FinalLoad by (simpl;tauto). exact Internal. }
    split.
    + intros c i NotLocal NotWritten. rewrite FreeFrame by exact NotLocal.
      apply UFrame; clear -NotWritten; simpl in NotWritten;intuition congruence.
    + split; [exact Removed | ]. split.
      * intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
        apply Untouched. exact Outside.
      * intros i Outside. rewrite FreeFrame by (apply HeapApart; simpl;tauto).
        apply EventHeader. exact Outside.
Qed.

(* Compatibility: the original public contract is an exact projection. *)
Theorem V293_critical_event_return_tcb_frame :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  exists Mf,
  let old := if initial =? 255 then curprio else initial in
  let fr := V293_ready_branch_rows lo hi old new in
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get Mf (bt,i) = get M (bt,i)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart.
  destruct (V293_critical_event_return_tcb_frame_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart) as [Mg Result].
  exists Mg. cbn zeta in *. tauto.
Qed.


(* Physical payload binding, specialized to unsuspended single-event waits.
   Source: repaired fixed Source/ucos_ii.h (status bits at 105--110;
   fields at 590,600--603). Pend is an explicit unchanged byte, not an
   assertion that timeout/abort processing has completed. *)
Theorem V293_wait_payload_field_layout :
  ftype 10%Z V293_tcb_fields = Some (Tptr Tvoid) /\
  ftype 13%Z V293_tcb_fields = Some Tint32 /\
  ftype 14%Z V293_tcb_fields = Some Tint8 /\
  ftype 15%Z V293_tcb_fields = Some Tint8 /\
  field_offset 10%Z V293_tcb_fields = Some (Int.repr 32) /\
  field_offset 13%Z V293_tcb_fields = Some (Int.repr 44) /\
  field_offset 14%Z V293_tcb_fields = Some (Int.repr 48) /\
  field_offset 15%Z V293_tcb_fields = Some (Int.repr 49).
Proof. repeat split; reflexivity. Qed.

Definition V293_wait_payload (M : mem) (bt : block) (base : Z)
    (reason : tcbstats) (delay : int32) (message : val) (pend : nat) : Prop :=
  (match reason with
   | os_stat_sem _ => load Tint8 M (bt,(base+48)%Z) = Some (V293_byteval 1)
   | os_stat_mbox _ => load Tint8 M (bt,(base+48)%Z) = Some (V293_byteval 2)
   | os_stat_q _ => load Tint8 M (bt,(base+48)%Z) = Some (V293_byteval 4)
   | os_stat_mutexsem _ => load Tint8 M (bt,(base+48)%Z) = Some (V293_byteval 16)
   | _ => False
   end) /\
  load Tint32 M (bt,(base+44)%Z) = Some (Vint32 delay) /\
  load (Tptr Tvoid) M (bt,(base+32)%Z) = Some message /\
  pend < 256 /\ load Tint8 M (bt,(base+49)%Z) = Some (V293_byteval pend).

Lemma V293_tcb_payload_load_frame : forall tp M M' bt base delta,
  (delta + Z.of_nat (typelen tp) <= 50)%Z ->
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get M' (bt,i) = get M (bt,i)) ->
  load tp M' (bt,(base+delta)%Z) = load tp M (bt,(base+delta)%Z).
Proof.
  intros tp M M' bt base delta Range Frame. unfold load,loadm.
  rewrite (V293_loadbytes_ext _ M M'); [reflexivity | ].
  intros k K. apply Frame. left. lia.
Qed.

Lemma V293_wait_payload_frame : forall M M' bt base reason delay message pend,
  (forall i, (i < base+50 \/ base+54 < i)%Z -> get M' (bt,i) = get M (bt,i)) ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_wait_payload M' bt base reason delay message pend.
Proof.
  intros M M' bt base reason delay message pend Frame Payload.
  unfold V293_wait_payload in *.
  assert (Loads : forall tp delta, (delta+Z.of_nat (typelen tp)<=50)%Z ->
    load tp M' (bt,(base+delta)%Z) = load tp M (bt,(base+delta)%Z)).
  { intros. eapply V293_tcb_payload_load_frame; eauto. }
  destruct reason; cbn -[load loadm loadbytes] in *; try tauto;
    repeat rewrite Loads by (cbn [typelen];lia); exact Payload.
Qed.

Theorem V293_critical_wait_payload_execution_event_frame :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload.
  assert (EmptyEntry : nth new entries Vnull = Vnull).
  { pose proof (View new ltac:(clear -N; lia)) as Loaded.
    rewrite Empty in Loaded. inversion Loaded. reflexivity. }
  assert (Fresh : forall t status msg,
      get tasks t <> Some (Int.repr (Z.of_nat new),status,msg)).
  { intros t status msg Member. pose proof
      (V293_rekey_task_entry entries tasks t new status msg TaskTable ltac:(clear -N; lia) Member) as Entry.
    rewrite EmptyEntry in Entry. discriminate. }
  destruct (V293_wait_prio_owned_step sc abstract_current tasks events now
    (bt,Int.repr base) old new reason delay message ge le M ir (enabled,si,ci) Os op R Of OO
    O N Task Fresh Owned Frame)
    as (Os' & OO' & Identity & Frame' & Abstract & UpdatedOwned).
  destruct (V293_wait_prio_branch_relations lo hi elo ehi entries tasks
    (bt,Int.repr base) old new reason delay message O N TaskTable Bitmap EventBitmap Task EmptyEntry)
    as (Branch & FinalBitmap & FinalTable & FinalEvent).
  destruct (V293_critical_event_return_tcb_frame_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart)
    as (Mf & Execute & TCB & Ready & PhysicalTable & PhysicalEvent & Internal & PhysicalFrame & Freed & TcbFrame & EventHeader).
  fold old in Ready. rewrite Branch in Ready. cbn [fst snd] in Ready.
  exists Mf. exists Os'. exists OO'. cbn zeta. fold old.
  split; [exact Identity | ]. split; [exact Frame' | ]. split; [exact Abstract | ].
  split; [exact Execute | ]. split; [exact TCB | ]. split; [exact Ready | ].
  split; [exact PhysicalTable | ]. split; [exact PhysicalEvent | ]. split; [exact Internal | ].
  split; [exact PhysicalFrame | ]. split; [exact Freed | ]. split.
  - eapply V293_shared_fields_owned_transport; [exact UpdatedOwned | exact Frame'].
  - split; [exact FinalBitmap | ]. split; [exact FinalTable | ]. split; [exact FinalEvent | ].
    split; [apply map_get_set | ]. split.
    + eapply V293_wait_payload_frame; [exact TcbFrame | exact Payload].
    + split; [ | exact EventHeader ]. intros p msg. rewrite map_get_set. discriminate.
Qed.

(* Original interface retained without any extra entry condition. *)
Theorem V293_critical_wait_payload_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload.
  destruct (V293_critical_wait_payload_execution_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload) as (Mf & Os' & OO' & Result).
  exists Mf. exists Os'. exists OO'. cbn zeta in *. tauto.
Qed.

(* One actual abstract ECB, not an unrelated wait-kind bitmap.
   Queue order/multiplicity are preserved by retaining the same events map;
   neither NoDup nor concrete event header/data loads are asserted here. *)
Definition V293_event_wait_queue (events : EcbMod.map) (tasks : TcbMod.map)
    (eid : tid) (reason : tcbstats) (data : edata) (waiters : waitset) : Prop :=
  get events eid = Some (data,waiters) /\
  (match reason,data with
   | os_stat_sem e,abssem _ => e = eid
   | os_stat_mbox e,absmbox _ => e = eid
   | os_stat_q e,absmsgq _ _ => e = eid
   | os_stat_mutexsem e,absmutexsem _ _ => e = eid
   | _,_ => False
   end) /\
  (forall t, In t waiters <->
    exists p delay message, get tasks t = Some (p,wait reason delay,message)).

Theorem V293_event_wait_queue_rekey : forall events tasks eid reason data waiters
    next old new delay message,
  V293_event_wait_queue events tasks eid reason data waiters ->
  get tasks next = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  V293_event_wait_queue events
    (set tasks next (Int.repr (Z.of_nat new),wait reason delay,message))
    eid reason data waiters.
Proof.
  intros events tasks eid reason data waiters next old new delay message
    (Lookup & Kind & Members) Task.
  split; [exact Lookup | ]. split; [exact Kind | ]. intro t.
  destruct (TcbMod.eq_dec t next) as [-> | Other].
  - split.
    + intros _. exists (Int.repr (Z.of_nat new)). exists delay. exists message.
      apply map_get_set.
    + intros _. apply (proj2 (Members next)).
      exists (Int.repr (Z.of_nat old)). exists delay. exists message. exact Task.
  - rewrite map_get_set' by congruence. exact (Members t).
Qed.

(* Each physical bitmap priority is represented by an actual waiter of the
   very same ECB, not merely a task with a similar waiting status. *)
Definition V293_event_queue_priorities lo hi (tasks : TcbMod.map)
    (waiters : waitset) : Prop :=
  forall p, p < 13 ->
    (V293_bitmap_ready lo hi p <->
      exists t status message, In t waiters /\
        get tasks t = Some (Int.repr (Z.of_nat p),status,message)).

Theorem V293_event_queue_priorities_bound : forall lo hi events tasks eid reason data waiters,
  V293_event_wait_tasks lo hi tasks reason ->
  V293_event_wait_queue events tasks eid reason data waiters ->
  V293_event_queue_priorities lo hi tasks waiters.
Proof.
  intros lo hi events tasks eid reason data waiters Bitmap (_ & _ & Members) p P.
  split.
  - intro Bit. destruct (proj1 (Bitmap p P) Bit) as (t & delay & message & Task).
    exists t. exists (wait reason delay). exists message. split; [ | exact Task].
    apply (proj2 (Members t)). exists (Int.repr (Z.of_nat p)). exists delay.
    exists message. exact Task.
  - intros (t & status & message & Member & Task).
    destruct (proj1 (Members t) Member) as (priority & delay & msg & Waiting).
    unfold language.priority in Waiting.
    rewrite Task in Waiting. inversion Waiting;subst priority status msg.
    apply (proj2 (Bitmap p P)). exists t. exists delay. exists message. exact Task.
Qed.

Theorem V293_critical_event_queue_execution_event_frame :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (V293_event_type_matches M be ebase data -> V293_event_type_matches Mf be ebase data).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue.
  destruct (V293_critical_wait_payload_execution_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend
    Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload)
    as (Mf & Os' & OO' & Identity & AbstractFrame & Abstract & Exec & Updated & Ready & Table & EventReady & Internal & PhysicalFrame & Freed & FinalOwned & FinalBitmap & FinalTable & FinalEvent & Moving & PayloadOut & NotReady & EventHeader).
  assert (FinalQueue : V293_event_wait_queue events
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters).
  { eapply V293_event_wait_queue_rekey; [exact Queue | exact Task]. }
  exists Mf. exists Os'. exists OO'. cbn zeta; fold old.
  split; [exact Identity | ]. split; [exact AbstractFrame | ]. split; [exact Abstract | ].
  split; [exact Exec | ]. split; [exact Updated | ]. split; [exact Ready | ].
  split; [exact Table | ]. split; [exact EventReady | ]. split; [exact Internal | ].
  split; [exact PhysicalFrame | ]. split; [exact Freed | ]. split; [exact FinalOwned | ].
  split; [exact FinalBitmap | ]. split; [exact FinalTable | ]. split; [exact FinalEvent | ].
  split; [exact Moving | ]. split; [exact PayloadOut | ]. split; [exact FinalQueue | ]. split.
  - eapply V293_event_queue_priorities_bound; [exact FinalEvent | exact FinalQueue].
  - split; [exact NotReady | ]. split; [exact EventHeader | ].
    intro Kind. eapply V293_event_type_matches_frame; [ | exact Kind ].
    apply EventHeader. left. lia.
Qed.

(* Original interface retained without any extra entry condition. *)
Theorem V293_critical_event_queue_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue.
  destruct (V293_critical_event_queue_execution_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue) as (Mf & Os' & OO' & Result).
  exists Mf. exists Os'. exists OO'. cbn zeta in *. tauto.
Qed.

(* OSEventType is an ECB discriminator, not the OSTCBStat wait-bit mask.
   This boundary covers the real event substatement, not prefix/return/free. *)




(* The original successful pointer store identifies Me; no second execution
   or determinism assumption is used to obtain the finer frame. *)
Theorem V293_event_nonnull_type_execution :
  forall P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt bp tcbbase be base lo hi old new data,
  old < 13 -> new < 13 -> lo < 256 -> hi < 256 -> bp <> be ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  load (Tptr V293_tcb_type) M (bc,0%Z) = Some (Vptr (bt,Int.repr tcbbase)) ->
  (0 <= tcbbase)%Z -> (tcbbase+28 <= Int.max_unsigned)%Z ->
  load (Tcom_ptr 411%Z) M (bt,(tcbbase+28)%Z) = Some (Vptr (be,Int.repr base)) ->
  V293_bytes_writable M bp 0%Z 4 ->
  (0 <= base)%Z -> (base+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be base lo hi (V293_ready_group lo hi) ->
  V293_event_bitmap_writable M be base ->
  V293_rekey_locals ge le M be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp) ->
  V293_event_type_matches M be base data ->
  exists Me,
  let Mf := V293_event_rekey_memory Me be base lo hi old new in
  let fr := V293_ready_rekey_rows lo hi old new in
  store (Tptr V293_event_type) M (bp,0%Z) (Vptr (be,Int.repr base)) = Some Me /\
  cstepstar P (curs (V293_task_prio_event ptcb pevent yo yn xo xn byo byn),(kenil,ks))
    (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
  V293_event_bitmap_loads Mf be base (fst fr) (snd fr) (V293_ready_group (fst fr) (snd fr)) /\
  V293_event_bitmap_writable Mf be base /\
  V293_rekey_locals ge le Mf be be (V293_rekey_ready_bindings yo yn xo xn byo byn old new) /\
  load (Tptr V293_event_type) Mf (bp,0%Z) = Some (Vptr (be,Int.repr base)) /\
  (forall c i, c <> bp -> c <> be -> get Mf (c,i) = get M (c,i)) /\
  (forall i, (i < base+10)%Z \/ (base+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  V293_event_type_matches Mf be base data.
Proof.
  intros P ks ge le M ptcb pevent yo yn xo xn byo byn bc bt bp tcbbase be base lo hi old new data
    O N L H Apart Bp Be Lp TB TR Event Dest Base Limit Loads W Loc LocalApart Kind.
  destruct (V293_task_prio_event_nonnull_execution P ks ge le M ptcb pevent yo yn xo xn byo byn
    bc bt bp tcbbase be base lo hi old new O N L H Apart Bp Be Lp TB TR Event Dest Base Limit
    Loads W Loc LocalApart) as (Me & Store & Exec & FinalLoads & FinalW & FinalLoc & FinalPtr & Frame).
  assert (Header : forall i, (i < base+10)%Z \/ (base+12 < i)%Z ->
    get (V293_event_rekey_memory Me be base lo hi old new) (be,i) = get M (be,i)).
  { intros i Outside. rewrite V293_event_rekey_byte_frame by (try assumption; tauto).
    eapply V293_storebytes_outside; [exact Store | left; congruence]. }
  exists Me. cbn zeta. split; [exact Store | ]. split; [exact Exec | ].
  split; [exact FinalLoads | ]. split; [exact FinalW | ]. split; [exact FinalLoc | ].
  split; [exact FinalPtr | ]. split; [exact Frame | ]. split; [exact Header | ].
  eapply V293_event_type_matches_frame; [apply Header; left; lia | exact Kind].
Qed.

(* A genuine write prevents extending the frame to event-table byte +12.
   This is a semantic counterexample, not a deliberately failing proof. *)
Theorem V293_event_rekey_changes_wait_byte : forall M,
  get (V293_event_rekey_memory M 72%positive 5%Z 0 1 8 6) (72%positive,17%Z) =
    Some (true,Byte (Byte.repr 0)).
Proof.
  intro M. change (get
    (V293_put_byte (V293_put_byte (V293_put_byte (V293_put_byte M
      (72%positive,17%Z) 0) (72%positive,15%Z) 0)
      (72%positive,15%Z) 1) (72%positive,16%Z) 64)
    (72%positive,17%Z) = Some (true,Byte (Byte.repr 0))).
  repeat rewrite V293_put_byte_other by discriminate.
  apply V293_put_byte_get_same.
Qed.

(* Header data for the two directly represented ECB kinds. Queue backing
   storage and mutex ownership are intentionally not represented here. *)
Theorem V293_event_data_field_layout :
  ftype 2%Z V293_event_fields = Some (Tptr Tvoid) /\
  field_offset 2%Z V293_event_fields = Some (Int.repr 4) /\
  ftype 3%Z V293_event_fields = Some Tint16 /\
  field_offset 3%Z V293_event_fields = Some (Int.repr 8).
Proof. repeat split; reflexivity. Qed.

Definition V293_event_sem_mbox_data (M : mem) (be : block) (base : Z)
    (data : edata) : Prop :=
  V293_event_type_matches M be base data /\
  match data with
  | abssem count =>
      (Int.unsigned count <= 65535)%Z /\
      load Tint16 M (be,(base+8)%Z) = Some (Vint32 count) /\
      load (Tptr Tvoid) M (be,(base+4)%Z) = Some Vnull
  | absmbox message =>
      load Tint16 M (be,(base+8)%Z) = Some (Vint32 Int.zero) /\
      load (Tptr Tvoid) M (be,(base+4)%Z) = Some message
  | _ => False
  end.

Lemma V293_event_header_load_frame : forall M M' be base tp delta,
  (0 <= delta)%Z -> (delta + Z.of_nat (typelen tp) <= 10)%Z ->
  (forall i, (i < base+10 \/ base+12 < i)%Z -> get M' (be,i) = get M (be,i)) ->
  load tp M' (be,(base+delta)%Z) = load tp M (be,(base+delta)%Z).
Proof.
  intros M M' be base tp delta D Width Frame. unfold load,loadm.
  rewrite (V293_loadbytes_ext _ M M'); [reflexivity | ].
  intros k K. apply Frame. left. lia.
Qed.

Lemma V293_event_sem_mbox_data_frame : forall M M' be base data,
  (forall i, (i < base+10 \/ base+12 < i)%Z -> get M' (be,i) = get M (be,i)) ->
  V293_event_sem_mbox_data M be base data ->
  V293_event_sem_mbox_data M' be base data.
Proof.
  intros M M' be base data Frame [Kind Data]. split.
  - eapply V293_event_type_matches_frame; [apply Frame; left; lia | exact Kind].
  - destruct data as [count|messages capacity|message|ceiling owned];
      cbn beta iota zeta in Data |- *; try contradiction.
    + destruct Data as (Bound & Count & Pointer). split; [exact Bound | ]. split.
      * rewrite (V293_event_header_load_frame M M' be base Tint16 8) by (cbn [typelen]; try lia; exact Frame). exact Count.
      * rewrite (V293_event_header_load_frame M M' be base (Tptr Tvoid) 4) by (cbn [typelen]; try lia; exact Frame). exact Pointer.
    + destruct Data as (Count & Pointer). split.
      * rewrite (V293_event_header_load_frame M M' be base Tint16 8) by (cbn [typelen]; try lia; exact Frame). exact Count.
      * rewrite (V293_event_header_load_frame M M' be base (Tptr Tvoid) 4) by (cbn [typelen]; try lia; exact Frame). exact Pointer.
Qed.

Theorem V293_critical_event_queue_execution_event_frame_data :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (V293_event_type_matches M be ebase data -> V293_event_type_matches Mf be ebase data) /\
  (V293_event_sem_mbox_data M be ebase data -> V293_event_sem_mbox_data Mf be ebase data).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue.
  pose proof (V293_critical_event_queue_execution_event_frame P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue) as Result.
  destruct Result as (Mf & Os' & OO' & Result).
  assert (Header : forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)).
  { cbn zeta in Result. tauto. }
  exists Mf. exists Os'. exists OO'. cbn zeta in *.
  assert (Data : V293_event_sem_mbox_data M be ebase data -> V293_event_sem_mbox_data Mf be ebase data).
  { apply V293_event_sem_mbox_data_frame. exact Header. }
  tauto.
Qed.

(* This is a pure ready-member lemma, not a second current-task invariant. *)
Lemma V293_wait_rekey_preserves_ready_current : forall tasks moving old new reason delay message current p current_message,
  get tasks moving = Some (old,wait reason delay,message) ->
  get tasks current = Some (p,rdy,current_message) ->
  get (set tasks moving (new,wait reason delay,message)) current = Some (p,rdy,current_message).
Proof.
  intros tasks moving old new reason delay message current p current_message Moving Current.
  rewrite map_get_set'; [exact Current | ]. intro Equal. subst moving. congruence.
Qed.

(* Conditional pure current correspondence through the SAME full return/free.
   CurTid ownership and the shared invariant are not reconstructed from loads. *)
Theorem V293_critical_event_current_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (V293_event_type_matches M be ebase data -> V293_event_type_matches Mf be ebase data) /\
  (V293_event_sem_mbox_data M be ebase data -> V293_event_sem_mbox_data Mf be ebase data) /\
  (forall pointer_block tp p current_message,
    get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) ->
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    load (Tptr tp) M (pointer_block,0%Z) = Some (Vptr abstract_current) ->
    get tasks abstract_current = Some (p,rdy,current_message) ->
    load (Tptr tp) Mf (pointer_block,0%Z) = Some (Vptr abstract_current) /\
    get OO' curtid = Some (oscurt abstract_current) /\
    get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
      abstract_current = Some (p,rdy,current_message)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue.
  pose proof (V293_critical_event_queue_execution_event_frame_data P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue) as Result.
  destruct Result as (Mf & Os' & OO' & Result).
  assert (Outside : forall c i, ~ In c (map fst (getaddr le)) ->
      ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
      get Mf (c,i) = get M (c,i)).
  { cbn zeta in Result. tauto. }
  assert (FinalOwned : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue).
  { cbn zeta in Result. tauto. }
  assert (CurrentLookup : get OO' curtid = Some (oscurt abstract_current)).
  { change (get (getabst (ge,caller,Mf,ir,(enabled,si,ci),OO',op)) curtid = Some (oscurt abstract_current)).
    eapply V293_star_abst_get_l; [ | exact FinalOwned].
    intros s Hs. exact (proj1 (V293_shared_fields_get _ _ _ _ _ Hs)). }
  exists Mf. exists Os'. exists OO'. cbn zeta in *.
  assert (Current : forall pointer_block tp p current_message,
    get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) ->
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    load (Tptr tp) M (pointer_block,0%Z) = Some (Vptr abstract_current) ->
    get tasks abstract_current = Some (p,rdy,current_message) ->
    load (Tptr tp) Mf (pointer_block,0%Z) = Some (Vptr abstract_current) /\
    get OO' curtid = Some (oscurt abstract_current) /\
    get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
      abstract_current = Some (p,rdy,current_message)).
  { intros pointer_block tp p current_message Binding NotLocal NotWritten Pointer ReadyCurrent.
    split.
    - etransitivity; [apply V293_load_block_frame; intro i; apply Outside; assumption | exact Pointer].
    - split; [exact CurrentLookup | ].
      eapply V293_wait_rekey_preserves_ready_current; [exact Task | exact ReadyCurrent]. }
  tauto.
Qed.

Require Import CertiOS.tactics.basetac.join_lib.

(* Spatial support, not a load-to-permission implication. *)
Lemma V293_ptomvallist_other_block : forall bytes b offset permission m c i,
  ptomvallist (b,offset) permission bytes m -> c <> b -> get m (c,i) = None.
Proof.
  induction bytes as [ | byte rest IH]; intros b offset permission m c i Owned Apart.
  - cbn [ptomvallist] in Owned. subst m. apply map_emp_get.
  - destruct Owned as (mh & mt & Joined & Head & Tail).
    unfold ptomval in Head. subst mh.
    erewrite map_join_get_none; [eapply IH; eauto | exact Joined | ].
    apply map_get_sig'. intro Equal. inversion Equal. congruence.
Qed.

Lemma V293_owned_block_frame : forall (owned before after : mem) b,
  Maps.sub owned before ->
  (forall c i, c <> b -> get owned (c,i) = None) ->
  (forall i, get after (b,i) = get before (b,i)) ->
  Maps.sub owned after.
Proof.
  intros owned before after b Sub Support Frame.
  unfold addr in *.
  apply sub_semp; [reflexivity | ]. intros [c i].
  destruct (Pos.eq_dec c b) as [Equal | Apart].
  - subst c. rewrite Frame.
    destruct (get owned (b,i)) as [[permission value] | ] eqn:Cell.
    + destruct (@sub_semp1 (block*offset) (bool*memval) mem memMap owned before (b,i) (permission,value)
        eq_refl Sub Cell) as [Same | [Split Read]].
      * rewrite Same. destruct permission; reflexivity.
      * rewrite Split. destruct permission; cbn in *; try discriminate; reflexivity.
    + destruct (get before (b,i)); exact I.
  - rewrite Support by exact Apart. destruct (get after (c,i)); exact I.
Qed.

(* Retain precisely the entry CurTid fragment across an untouched block.
   No preservation of an arbitrary physical frame across free is claimed. *)
Lemma V293_current_owned_frame : forall current R ge le M ir aux O op
    le' Mf ir' aux' O' op',
  (ge,le,M,ir,aux,O,op) |= CurTid current ** R ->
  (forall b tp, get ge OSTCBCur = Some (b,Tptr tp) ->
    forall i, get Mf (b,i) = get M (b,i)) ->
  (ge,le',Mf,ir',aux',O',op') |= CurTid current ** Atrue.
Proof.
  intros current R ge le M ir aux O op le' Mf ir' aux' O' op' Owned Frame.
  apply sat_split in Owned.
  destruct Owned as (mc & mr & oc & ore & JM & JO & Current & Rest).
  destruct Current as [tp Current]. unfold Agvarmapsto in Current.
  destruct Current as [b Current]. apply sat_split in Current.
  destruct Current as (me & mp & oe & oa & JMc & JOc & Env & Pointer).
  destruct Env as (bound & Binding & Address & EmptyM & EmptyO).
  cbn in Address, EmptyM, EmptyO, Binding. inversion Address; subst bound.
  change (me = emp) in EmptyM. change (oe = emp) in EmptyO.
  subst me oe. destruct Pointer as [Pointer EmptyA]. change (oa = emp) in EmptyA. subst oa.
  apply map_join_comm in JMc. apply map_join_emp' in JMc. subst mc.
  apply map_join_comm in JOc. apply map_join_emp' in JOc. subst oc.
  assert (Sub : Maps.sub mp Mf).
  { eapply V293_owned_block_frame with (b:=b) (before:=M).
    - exists mr. exact JM.
    - destruct Pointer as (bytes & Encoding & Cells).
      intros c i Apart. eapply V293_ptomvallist_other_block; eauto.
    - apply (Frame b tp Binding). }
  destruct Sub as [remainder Joined].
  apply sat_split'. exists mp. exists remainder. exists (emp:osabst). exists O'.
  split; [exact Joined | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; [ | exact I]. exists tp. unfold Agvarmapsto. exists b.
  apply sat_split'. exists (emp:mem). exists mp. exists (emp:osabst). exists (emp:osabst).
  split; [apply map_join_comm; apply map_join_emp | ]. split; [apply map_join_emp | ].
  split; [exists b; repeat split; assumption || reflexivity | ]. split; [exact Pointer | reflexivity].
Qed.

(* The physical current fragment has empty abstract ownership; the shared
   fields have empty physical ownership.  This is an orthogonal-domain
   conjunction elimination, not arbitrary duplication of separation resources. *)
Lemma V293_current_fields_reconstruct : forall current tasks events now ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= CurTid current ** Atrue ->
  (ge,le,M,ir,aux,O,op) |= V293_shared_fields current tasks events now ** Atrue ->
  (ge,le,M,ir,aux,O,op) |=
    (CurTid current ** V293_shared_fields current tasks events now) ** Atrue.
Proof.
  intros current tasks events now ge le M ir aux O op HC HF.
  apply sat_split in HC. destruct HC as (mc & mr & oc & orc & JM & JO & Current & _).
  assert (Empty : oc = emp).
  { destruct Current as [tp C]. unfold Agvarmapsto in C. destruct C as [b C].
    apply sat_split in C. destruct C as (me & mp & oe & oa & JMC & JOC & Env & [_ EA]).
    destruct Env as (b0 & GE & EQ & EM & EO). change (oe = emp) in EO.
    change (oa = emp) in EA. subst oe oa. apply map_join_comm in JOC.
    apply map_join_emp' in JOC. symmetry. exact JOC. }
  subst oc.
  apply sat_split in HF. destruct HF as (mf & mrf & ofields & orest & JMF & JOF & Fields & _).
  pose proof (V293_shared_fields_empty_heap _ _ _ _ _ _ _ _ _ _ _ Fields) as EmptyM. subst mf.
  apply sat_split'. exists mc. exists mr. exists ofields. exists orest.
  split; [exact JM | ]. split; [exact JOF | ]. split; [ | exact I].
  apply sat_split'. exists mc. exists (emp:mem). exists (emp:osabst). exists ofields.
  split; [apply map_join_emp | ]. split; [apply map_join_comm; apply map_join_emp | ].
  split; [exact Current | exact Fields].
Qed.

(* Same full return with an owned shared core, not a whole-kernel invariant. *)
Theorem V293_critical_event_current_owned_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    (CurTid abstract_current ** V293_shared_fields abstract_current tasks events now) ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) /\
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx]) ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (V293_event_type_matches M be ebase data -> V293_event_type_matches Mf be ebase data) /\
  (V293_event_sem_mbox_data M be ebase data -> V293_event_sem_mbox_data Mf be ebase data) /\
  (forall pointer_block tp p current_message,
    get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) ->
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    load (Tptr tp) M (pointer_block,0%Z) = Some (Vptr abstract_current) ->
    get tasks abstract_current = Some (p,rdy,current_message) ->
    load (Tptr tp) Mf (pointer_block,0%Z) = Some (Vptr abstract_current) /\
    get OO' curtid = Some (oscurt abstract_current) /\
    get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
      abstract_current = Some (p,rdy,current_message)) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (CurTid abstract_current ** V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue.
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue PointerApart.
  assert (FieldsOwned : (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    V293_shared_fields abstract_current tasks events now ** (CurTid abstract_current ** R)) by (sep auto).
  assert (EntryCurrent : (ge,le,M,ir,(enabled,si,ci),Os,op) |= CurTid abstract_current ** Atrue).
  { clear FieldsOwned. sep auto. }
  pose proof (V293_critical_event_current_execution P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op (CurTid abstract_current ** R) reason delay message pend data waiters Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task FieldsOwned Frame Payload Queue) as Result.
  destruct Result as (Mf & Os' & OO' & Result).
  assert (Outside : forall c i, ~ In c (map fst (getaddr le)) ->
    ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) by (cbn zeta in Result; tauto).
  assert (FinalFields : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue)
    by (cbn zeta in Result; tauto).
  assert (FinalCurrent : (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |= CurTid abstract_current ** Atrue).
  { eapply V293_current_owned_frame; [exact EntryCurrent | ].
    intros pointer_block tp Binding i. destruct (PointerApart pointer_block tp Binding).
    apply Outside; assumption. }
  pose proof (V293_current_fields_reconstruct _ _ _ _ _ _ _ _ _ _ _ FinalCurrent FinalFields) as FinalCore.
  exists Mf. exists Os'. exists OO'. cbn zeta in *. tauto.
Qed.
(* Selected physical fields for every abstract task member.  This is not
   ownership of the complete TCB or a linked-list/allocator invariant. *)
Definition V293_task_record (M : mem) (t : tid) (priority : int32)
    (status : taskstatus) (message : val) : Prop :=
  exists p, p < 13 /\ priority = Int.repr (Z.of_nat p) /\
  V293_tcb_updated_loads M (fst t) (Int.unsigned (snd t)) p /\
  match status with
  | rdy =>
      load Tint8 M (fst t,(Int.unsigned (snd t)+48)%Z) = Some (V293_byteval 0) /\
      load (Tptr Tvoid) M (fst t,(Int.unsigned (snd t)+32)%Z) = Some message
  | wait os_stat_time delay =>
      load Tint8 M (fst t,(Int.unsigned (snd t)+48)%Z) = Some (V293_byteval 0) /\
      load Tint32 M (fst t,(Int.unsigned (snd t)+44)%Z) = Some (Vint32 delay) /\
      load (Tptr Tvoid) M (fst t,(Int.unsigned (snd t)+32)%Z) = Some message
  | wait reason delay =>
      exists pend, V293_wait_payload M (fst t) (Int.unsigned (snd t)) reason delay message pend /\
      match reason with
      | os_stat_sem eid | os_stat_q eid | os_stat_mbox eid | os_stat_mutexsem eid =>
          load (Tcom_ptr 411%Z) M (fst t,(Int.unsigned (snd t)+28)%Z) = Some (Vptr eid)
      | os_stat_time => False
      end
  end.

Definition V293_task_records (M : mem) (tasks : TcbMod.map) : Prop :=
  forall t priority status message, get tasks t = Some (priority,status,message) ->
    V293_task_record M t priority status message.

Lemma V293_task_record_frame : forall M Mf t priority status message,
  (forall i, get Mf (fst t,i) = get M (fst t,i)) ->
  V293_task_record M t priority status message ->
  V293_task_record Mf t priority status message.
Proof.
  intros M Mf t priority status message Frame (p & Range & Priority & Fields & Status).
  exists p. split; [exact Range | ]. split; [exact Priority | ].
  unfold V293_tcb_updated_loads in *. split.
  - repeat rewrite (V293_load_block_frame _ M Mf _ _ Frame). exact Fields.
  - destruct status as [ | reason delay]; [ | destruct reason];
      cbn -[load loadm loadbytes] in *; unfold V293_wait_payload in *;
      repeat rewrite (V293_load_block_frame _ M Mf _ _ Frame); exact Status.
Qed.

Lemma V293_task_records_update_frame : forall M Mf tasks next priority status message,
  V293_task_records M tasks ->
  V293_task_record Mf next priority status message ->
  (forall t p st msg, get tasks t = Some (p,st,msg) -> t <> next ->
    forall i, get Mf (fst t,i) = get M (fst t,i)) ->
  V293_task_records Mf (set tasks next (priority,status,message)).
Proof.
  intros M Mf tasks next priority status message Records Changed OtherFrame t p st msg Lookup.
  destruct (TcbMod.eq_dec next t) as [Same | Apart].
  - subst t. rewrite map_get_set in Lookup. inversion Lookup; subst. exact Changed.
  - rewrite map_get_set' in Lookup by exact Apart.
    eapply V293_task_record_frame; [ | apply Records; exact Lookup].
    intro i. apply (OtherFrame t p st msg Lookup); congruence.
Qed.

Theorem V293_critical_event_task_records_execution :
  forall P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn
    b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx
    current reserved bcur bct curbase rb curprio
    running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters,
  initial < 256 -> (initial < 12 \/ initial = 255) -> new < 12 ->
  let old := if initial =? 255 then curprio else initial in
  old < 13 -> lo < 256 -> hi < 256 -> br <> bg ->
  (0 <= base)%Z -> (base+55 <= Int.max_unsigned)%Z ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr V293_tcb_type) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  b <> bo -> b <> bn -> b <> bc -> b <> bt ->
  b <> dy -> b <> dby -> b <> dx -> b <> br -> b <> bg ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval initial) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->
  V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->
  length entries = 13 -> V293_table_loads V293_tcb_type M b entries ->
  get le yo = Some (dy,Tint8) -> get le byo = Some (dby,Tint8) -> get le xo = Some (dx,Tint8) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  dy <> dby -> dy <> dx -> dby <> dx ->
  (forall c, c = dy \/ c = dby \/ c = dx -> c <> bc /\ c <> bt /\ c <> br /\ c <> bg) ->
  V293_tcb_old_loads M bt base (V293_prio_row old)
    (2 ^ V293_prio_row old) (2 ^ V293_prio_bit old) ->
  (exists v, get M (dy,0%Z) = Some (true,v)) ->
  (exists v, get M (dby,0%Z) = Some (true,v)) ->
  (exists v, get M (dx,0%Z) = Some (true,v)) ->
  V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->
  V293_rekey_bitmap_writable M br bg ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> b /\ c <> dy /\ c <> dby /\ c <> dx) ->
  get le pevent = Some (bp,Tptr V293_event_type) ->
  V293_bytes_writable M bp 0%Z 4 ->
  load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) ->
  bc <> br -> bc <> bg -> bt <> br -> bt <> bg ->
  bp <> b -> bp <> dy -> bp <> dby -> bp <> dx -> bp <> br -> bp <> bg ->
  bp <> be ->
  be <> b -> be <> dy -> be <> dby -> be <> dx -> be <> br -> be <> bg ->
  elo < 256 -> ehi < 256 -> (0 <= ebase)%Z -> (ebase+12 <= Int.max_unsigned)%Z ->
  V293_event_bitmap_loads M be ebase elo ehi (V293_ready_group elo ehi) ->
  V293_event_bitmap_writable M be ebase ->
  (forall x v c, In (x,v) (V293_rekey_ready_bindings yo yn xo xn byo byn old new) ->
    get le x = Some (c,Tint8) -> c <> bp /\ c <> be) ->
  bc <> bt -> bc <> bp -> bc <> be -> bt <> bp -> bt <> be ->
  get le xi = Some (bi,Tint8) ->
  (forall c, c = bn \/ c = bi ->
    c <> b /\ c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be /\ c <> bt) ->
  (forall x v c, In (x,v) (V293_rekey_new_bindings yn xn byn new) ->
    get le x = Some (c,Tint8) -> c <> bt) ->
  V293_tcb_update_writable M bt base ->
  get le yn = Some (ny,Tint8) -> get le byn = Some (nby,Tint8) ->
  get le xn = Some (nbx,Tint8) ->
  ny <> bi -> ny <> nby -> ny <> nbx -> bi <> nby -> bi <> nbx -> nby <> nbx ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    c <> b /\ c <> bo /\ c <> bn /\ c <> bc /\ c <> bt /\
    c <> dy /\ c <> dby /\ c <> dx /\ c <> br /\ c <> bg /\ c <> bp /\ c <> be) ->
  (forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->
    exists v, get M (c,0%Z) = Some (true,v)) ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat new)%Z) = Some Vnull ->
  load (Tptr V293_tcb_type) M (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base)) ->
  bo <> bn -> bc <> bn -> bc <> bo ->
  (initial = 255 ->
    get le current = None /\ get ge current = Some (bcur,Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) M (bcur,0%Z) = Some (Vptr (bct,Int.repr curbase)) /\
    (0 <= curbase)%Z /\ (curbase+50 <= Int.max_unsigned)%Z /\
    load Tint8 M (bct,(curbase+50)%Z) = Some (V293_byteval curprio) /\
    (exists v, get M (bo,0%Z) = Some (true,v))) ->
  get le reserved = None -> get ge reserved = Some (rb,Tint8) ->
  (bt,Int.repr base) <> (rb,Int.zero) ->
  V293_bytes_writable M bc 0%Z 4 ->
  (forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->
    c <> bo /\ c <> bc) ->
  run < 256 -> get le running = None -> get ge running = Some (runblock,Tint8) ->
  load Tint8 M (runblock,0%Z) = Some (V293_byteval run) ->
  (run = 1 ->
    P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target schedcurrent counter) /\
    saved <> interrupt /\ saved <> lock /\ V293_success_sched_blocked ge M interrupt lock) ->
  V293_success_globals_away ge [running;interrupt;lock] [bo;bc;b;dy;dby;dx;br;bg;bp;bt;ny;bi;nby;nbx;be] ->
  callcont ks = Some (kcall f body caller next) ->
  NoDup (map fst (getaddr le)) ->
  (forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t)) ->
  (forall c, In c [b;bt;br;bg;be] -> ~ In c (map fst (getaddr le))) ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  V293_event_wait_tasks elo ehi tasks reason ->
  (reason = os_stat_sem (be,Int.repr ebase) \/ reason = os_stat_q (be,Int.repr ebase) \/
    reason = os_stat_mbox (be,Int.repr ebase) \/ reason = os_stat_mutexsem (be,Int.repr ebase)) ->
  get tasks (bt,Int.repr base) = Some (Int.repr (Z.of_nat old),wait reason delay,message) ->
  (ge,le,M,ir,(enabled,si,ci),Os,op) |=
    (CurTid abstract_current ** V293_shared_fields abstract_current tasks events now) ** R ->
  join Os Of OO ->
  V293_wait_payload M bt base reason delay message pend ->
  V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->
  (forall pointer_block tp, get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) /\
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx]) ->
  V293_task_records M tasks ->
  (forall t p st msg, get tasks t = Some (p,st,msg) -> t <> (bt,Int.repr base) ->
    ~ In (fst t) (map fst (getaddr le)) /\
    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx]) ->
  exists Mf Os' OO',
  let old := if initial =? 255 then curprio else initial in
  Os' = set Os abstcblsid (abstcblist (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))) /\
  join Os' Of OO' /\
  spec_step sc (spec_prim nil (V293_wait_prio_step (bt,Int.repr base) old new)) OO
    (spec_done (Some (Vint32 Int.zero))) OO' /\
  V293_local_steps P
    (curs (sseq (V293_primitive_success_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi current reserved)
      (V293_task_prio_success_tail running sched)),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip (Some (Vint32 Int.zero))),(kenil,next))
    ((ge,caller,Mf),ir,(enabled,si,ci)) /\
  V293_tcb_updated_loads Mf bt base new /\
  V293_rekey_bitmap_loads Mf br bg lo hi (V293_ready_group lo hi) /\
  V293_table_loads V293_tcb_type Mf b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_bitmap_loads Mf be ebase (fst er) (snd er) (V293_ready_group (fst er) (snd er))) /\
  load (Tcom_ptr 411%Z) Mf (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase)) /\
  (forall c i, ~ In c (map fst (getaddr le)) -> ~ In c [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    get Mf (c,i) = get M (c,i)) /\
  (forall c t k, In (c,t) (getaddr le) -> k < typelen t ->
    get Mf (c,Z.of_nat k) = None) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    V293_shared_fields abstract_current (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now ** Atrue /\
  V293_bitmap_tasks lo hi (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr (bt,Int.repr base))) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_wait_tasks (fst er) (snd er) (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) reason) /\
  get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) =
    Some (Int.repr (Z.of_nat new),wait reason delay,message) /\
  V293_wait_payload Mf bt base reason delay message pend /\
  V293_event_wait_queue events (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
    (be,Int.repr ebase) reason data waiters /\
  (let er := V293_ready_rekey_rows elo ehi old new in
    V293_event_queue_priorities (fst er) (snd er)
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) waiters) /\
  (forall p msg, get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) (bt,Int.repr base) <> Some (p,rdy,msg)) /\
  (forall i, (i < ebase+10 \/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i)) /\
  (V293_event_type_matches M be ebase data -> V293_event_type_matches Mf be ebase data) /\
  (V293_event_sem_mbox_data M be ebase data -> V293_event_sem_mbox_data Mf be ebase data) /\
  (forall pointer_block tp p current_message,
    get ge OSTCBCur = Some (pointer_block,Tptr tp) ->
    ~ In pointer_block (map fst (getaddr le)) ->
    ~ In pointer_block [bo;bc;b;dy;dby;dx;br;bg;bp;be;bt;ny;bi;nby;nbx] ->
    load (Tptr tp) M (pointer_block,0%Z) = Some (Vptr abstract_current) ->
    get tasks abstract_current = Some (p,rdy,current_message) ->
    load (Tptr tp) Mf (pointer_block,0%Z) = Some (Vptr abstract_current) /\
    get OO' curtid = Some (oscurt abstract_current) /\
    get (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))
      abstract_current = Some (p,rdy,current_message)) /\
  (ge,caller,Mf,ir,(enabled,si,ci),OO',op) |=
    (CurTid abstract_current ** V293_shared_fields abstract_current
      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) events now) ** Atrue /\
  V293_task_records Mf
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)).
Proof.
  intros P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next
    sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters
    Input Valid N old O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart
    RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart
    TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue PointerApart Records RecordApart.
  pose proof (V293_critical_event_current_owned_execution P ks ge le caller M ir enabled si ci table oldprio newprio ptcb rows group yo yn xo xn byo byn b bo bn bc bt dy dby dx base br bg lo hi initial new entries pevent bp be ebase elo ehi xi bi ny nby nbx current reserved bcur bct curbase rb curprio running runblock run sched saved interrupt lock schednew high target schedcurrent counter f body next sc abstract_current tasks events now Os Of OO op R reason delay message pend data waiters Input Valid N O L H RG Base Limit Nt Gt Bo Bn Bc Tbo Tbn Tbc Tbt Tdy Tdby Tdx Tr Tg Lo Ln Wo Wn Len View By Bby Bx Nr Gr Ng Gg YBY YX BYX Apart Fields Wy Wby Wx Loads W NewApart Be We Event Cr Cg Br Bg Pb Py Pby Px Pr Pg PE Eb Ey Eby Ex Er Eg EL EH EB ELimit ELoads EW LocalApart CT CP CE TP TE Bi ExtraApart NewTcbApart TW NBy NBby NBx NYI NYBY NYBX NIBY NIBX NBYBX CoordApart CoordW Empty Slot Onew Cnew CO Self Nreserved Greserved Token CW EntryApart RunRange NoRun GlobalRun LoadRun WhenRunning Away Call ND InitialWritable HeapApart TaskTable Bitmap EventBitmap Reason Task Owned Frame Payload Queue PointerApart) as Result.
  destruct Result as (Mf & Os' & OO' & Result).
  cbn zeta in Result.
  destruct Result as (Identity & AbstractFrame & Abstract & Exec & Updated & Ready & Table
    & EventReady & FinalEventPointer & Outside & Removed & FinalOwned & FinalBitmap & FinalTable
    & FinalEvent & Moving & FinalPayload & FinalQueue & QueueBitmap & NotReady & Header
    & TypePreserved & DataPreserved & CurrentPreserved & FinalCore).
  assert (FinalRecord : V293_task_record Mf (bt,Int.repr base)
    (Int.repr (Z.of_nat new)) (wait reason delay) message).
  { unfold V293_task_record. cbn [fst snd].
    rewrite Int.unsigned_repr by lia. exists new.
    split; [clear -N; lia | ]. split; [reflexivity | ]. split; [exact Updated | ].
    destruct Reason as [Equal | [Equal | [Equal | Equal]]]; rewrite Equal in *;
      exists pend; split; assumption. }
  assert (FinalRecords : V293_task_records Mf
    (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message))).
  { eapply V293_task_records_update_frame; [exact Records | exact FinalRecord | ].
    intros t p st msg Lookup Different i. destruct (RecordApart t p st msg Lookup Different).
    apply Outside; assumption. }
  exists Mf. exists Os'. exists OO'. cbn zeta.
  repeat match goal with |- _ /\ _ => split; [assumption | ] end. exact FinalRecords.
Qed.
