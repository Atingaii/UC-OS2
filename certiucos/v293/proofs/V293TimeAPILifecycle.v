(* Original time API body and return, on the heap produced by a real call.
   These are finite non-interleaved paths, not a whole-kernel simulation. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_time_cell_store : forall local x b old n R ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_time_cell local x b old ** R ->
  exists Mp, store Tint32 M (b,0%Z) (Vint32 n)=Some Mp /\
    (ge,le,Mp,ir,aux,O,op) |= V293_time_cell local x b (Vint32 n) ** R.
Proof.
  intros local x b old n R ge le M ir aux O op Owned.
  assert(Raw:(ge,le,M,ir,aux,O,op) |= Amapsto(b,0%Z) Tint32 true old **
    (V293_time_binding local x b ** R)).
  { unfold V293_time_cell in Owned. sep auto. }
  destruct(V293_tick_raw_slot_update (b,0%Z) Tint32 old (Vint32 n)
    _ _ _ _ _ _ _ _ eq_refl Raw)as(Mp&Store&Post).
  exists Mp. split;[exact Store | ].
  unfold V293_owned_record_cell in Post. unfold V293_time_cell. sep auto.
Qed.

Lemma V293_time_local_layout : forall ticks saved bt bs,
  ticks<>saved -> Permutation (getaddr(V293_time_call_locals ticks saved bt bs))
    [(bt,Tint32);(bs,Tint32)].
Proof.
  intros ticks saved bt bs Different. unfold V293_time_call_locals.
  change(Permutation
    (getaddr(EnvMod.set(EnvMod.set EnvMod.emp ticks(bt,Tint32))saved(bs,Tint32)))
    [(bt,Tint32);(bs,Tint32)]).
  cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist].
  destruct(identspec.blt saved ticks)eqn:Order.
  - apply perm_swap.
  - rewrite identspec.neq_beq_false by congruence. apply Permutation_refl.
Qed.

Definition V293_time_return_start result ks : code :=
  match result with
  | None => (curs sret,(kenil,ks))
  | Some v => (curs(sskip(Some v)),(kenil,kret ks))
  end.
Lemma V293_time_locals_return : forall P ks ge caller M ir aux O op
    ticks saved bt bs tmp save f body result R,
  ticks<>saved -> bt<>bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    V293_time_cell true ticks bt tmp ** (V293_time_cell true saved bs save ** R) ->
  exists Mf,
    V293_local_steps P (V293_time_return_start result (kcall f body caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,aux)
      (curs(sskip result),(kenil,ks)) ((ge,caller,Mf),ir,aux) /\
    (forall b i,b<>bt -> b<>bs -> get Mf(b,i)=get M(b,i)) /\
    (forall k,k<4 -> get Mf(bt,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
  intros P ks ge caller M ir aux O op ticks saved bt bs tmp save f body result R
    Different Blocks Owned.
  pose proof(V293_time_local_layout ticks saved bt bs Different)as Layout.
  assert(Two:NoDup(map fst [(bt,Tint32);(bs,Tint32)])).
  { cbn. constructor;[cbn;intuition congruence | constructor;[cbn;tauto | constructor]]. }
  assert(ND:NoDup(map fst(getaddr(V293_time_call_locals ticks saved bt bs)))).
  { eapply Permutation_NoDup;[apply Permutation_map;apply Permutation_sym;exact Layout | exact Two]. }
  assert(T:(ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    Amapsto(bt,0%Z) Tint32 true tmp ** Atrue).
  { unfold V293_time_cell in Owned. clear -Owned. sep auto. }
  assert(S:(ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    Amapsto(bs,0%Z) Tint32 true save ** Atrue).
  { unfold V293_time_cell in Owned. clear -Owned. sep auto. }
  pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ T)as WT.
  pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ S)as WS.
  assert(W:forall b tp,In(b,tp)(getaddr(V293_time_call_locals ticks saved bt bs)) ->
    V293_bytes_writable M b 0%Z (typelen tp)).
  { intros b tp Member. apply(Permutation_in (b,tp) Layout)in Member.
    destruct Member as[E|[E|E]];[inversion E;subst | inversion E;subst | contradiction];assumption. }
  assert(Return:exists Mf,
    cstepstar P (V293_time_return_start result (kcall f body caller ks))
      (ge,V293_time_call_locals ticks saved bt bs,M)
      (curs(sskip result),(kenil,ks)) (ge,caller,Mf) /\
    (forall b i,~In b(map fst(getaddr(V293_time_call_locals ticks saved bt bs))) -> get Mf(b,i)=get M(b,i)) /\
    (forall b tp k,In(b,tp)(getaddr(V293_time_call_locals ticks saved bt bs)) ->
      k<typelen tp -> get Mf(b,Z.of_nat k)=None)).
  { destruct result as [v | ];unfold V293_time_return_start.
    - eapply V293_evaluated_return_execution;[reflexivity | exact ND | exact W].
    - eapply V293_tick_void_return;[reflexivity | exact ND | exact W]. }
  destruct Return as(Mf&Exec&Frame&Removed). exists Mf. split;[apply V293_csteps_local;exact Exec | ]. split.
  - intros b i BT BS. apply Frame. intro Member. apply in_map_iff in Member.
    destruct Member as([c tp]&E&Member). cbn in E. subst c.
    apply(Permutation_in (b,tp) Layout)in Member. cbn in Member. intuition congruence.
  - intros k K. split.
    + apply Removed with Tint32;[ | exact K]. eapply Permutation_in;[apply Permutation_sym;exact Layout | left;reflexivity].
    + apply Removed with Tint32;[ | exact K]. eapply Permutation_in;[apply Permutation_sym;exact Layout | right;left;reflexivity].
Qed.

(* Both unchanged bodies have this exact shape. The copy is justified by
   owned source bytes and a constructed destination store, not an eval oracle. *)
Lemma V293_time_body_prefix : forall P ks ge le M ir enabled si ci O op
    saved bs dl dst bd old sl src bc n tail R,
  get le saved=Some(bs,Tint32) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell dl dst bd old ** (V293_time_cell sl src bc (Vint32 n) ** R)) ->
  exists Mz Mc,
    store Tint32 M (bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz (bd,0%Z)(Vint32 n)=Some Mc /\
    V293_local_steps P
      (curs(sseq(sassign(evar saved)(econst32 Int.zero))
        (sseq(sseq(sprim encrit)(sseq(sassign(evar dst)(evar src))(sprim excrit)))tail)),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs tail,(kenil,ks)) ((ge,le,Mc),ir,(enabled,si,ci)) /\
    (ge,le,Mc,ir,(enabled,si,ci),O,op) |=
      V293_time_cell true saved bs (Vint32 Int.zero) **
        (V293_time_cell dl dst bd (Vint32 n) ** (V293_time_cell sl src bc (Vint32 n) ** R)).
Proof.
  intros P ks ge le M ir enabled si ci O op saved bs dl dst bd old sl src bc n tail R Saved Owned.
  destruct(V293_time_cell_store true saved bs Vundef Int.zero _ _ _ _ _ _ _ _ Owned)
    as(Mz&Zero&AfterZero).
  assert(Target:(ge,le,Mz,ir,(enabled,si,ci),O,op) |=
    V293_time_cell dl dst bd old **
      (V293_time_cell sl src bc(Vint32 n) ** (V293_time_cell true saved bs(Vint32 Int.zero) ** R))).
  { clear -AfterZero. sep auto. }
  destruct(V293_time_cell_store dl dst bd old n _ _ _ _ _ _ _ _ Target)
    as(Mc&Copy&AfterCopy).
  assert(B:(ge,le,Mz,ir,(enabled,si,ci),O,op) |= V293_time_binding dl dst bd ** Atrue).
  { unfold V293_time_cell in Target. clear -Target. sep auto. }
  assert(S:(ge,le,Mz,ir,(enabled,si,ci),O,op) |= V293_time_cell sl src bc(Vint32 n) ** Atrue).
  { clear -Target. sep auto. }
  destruct(V293_time_binding_star dl dst bd Atrue _ B)as[Address DestType].
  destruct(V293_time_cell_read sl src bc n Atrue _ S)as[Value SrcType].
  exists Mz. exists Mc. split;[exact Zero | ]. split;[exact Copy | ]. split.
  - eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply V293_success_assign_zero;[exact Saved | exact Zero]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. eapply V293_tick_assign32_execution with(off:=0%Z);
        [exact DestType | exact SrcType | exact Address | exact Value | vm_compute;split;discriminate | exact Copy]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
    apply V293_local_refl.
  - clear -AfterCopy. sep auto.
Qed.

Theorem V293_time_get_body_return : forall P ks ge caller M ir enabled si ci O op
    now ticks saved bn bt bs clock tmp R f,
  ticks<>saved -> bt<>bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell true ticks bt tmp ** (V293_time_cell false now bn(Vint32 clock) ** R)) ->
  exists Mz Mc Mf,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bt,0%Z)(Vint32 clock)=Some Mc /\
    V293_local_steps P
      (curs(V293_TimeGet_body now ticks saved),
        (kenil,kcall f (V293_TimeGet_body now ticks saved) caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,(enabled,si,ci))
      (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,op) |=
      V293_time_cell true saved bs(Vint32 Int.zero) **
        (V293_time_cell true ticks bt(Vint32 clock) ** (V293_time_cell false now bn(Vint32 clock) ** R)) /\
    (forall b i,b<>bt -> b<>bs -> get Mf(b,i)=get Mc(b,i)) /\
    (forall k,k<4 -> get Mf(bt,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
  intros P ks ge caller M ir enabled si ci O op now ticks saved bn bt bs clock tmp R f
    Different Blocks Owned.
  assert(Saved:get(V293_time_call_locals ticks saved bt bs)saved=Some(bs,Tint32)).
  { unfold V293_time_call_locals. apply map_get_set. }
  destruct(V293_time_body_prefix P (kcall f(V293_TimeGet_body now ticks saved)caller ks)
    ge _ M ir enabled si ci O op saved bs true ticks bt tmp false now bn clock
    (srete(evar ticks)) R Saved Owned)as(Mz&Mc&Zero&Copy&Prefix&Post).
  assert(Read:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true ticks bt(Vint32 clock) ** Atrue).
  { clear -Post. sep auto. }
  destruct(V293_time_cell_read true ticks bt clock Atrue _ Read)as[Value Typed].
  assert(Locals:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true ticks bt(Vint32 clock) **
      (V293_time_cell true saved bs(Vint32 Int.zero) ** (V293_time_cell false now bn(Vint32 clock) ** R))).
  { clear -Post. sep auto. }
  destruct(V293_time_locals_return P ks ge caller Mc ir (enabled,si,ci) O op
    ticks saved bt bs (Vint32 clock)(Vint32 Int.zero) f(V293_TimeGet_body now ticks saved)
    (Some(Vint32 clock)) _ Different Blocks Locals)as(Mf&Return&Frame&Removed).
  exists Mz. exists Mc. exists Mf. split;[exact Zero | ]. split;[exact Copy | ]. split.
  - eapply V293_local_trans;[exact Prefix | ].
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply srete_step]. }
    eapply V293_local_trans.
    { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Value. }
    exact Return.
  - split;[exact Post | ]. split;assumption.
Qed.

Theorem V293_time_set_body_return : forall P ks ge caller M ir enabled si ci O op
    now ticks saved bn bt bs clock n R f,
  ticks<>saved -> bt<>bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell false now bn(Vint32 clock) ** (V293_time_cell true ticks bt(Vint32 n) ** R)) ->
  exists Mz Mc Mf,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bn,0%Z)(Vint32 n)=Some Mc /\
    V293_local_steps P
      (curs(V293_TimeSet_body now ticks saved),
        (kenil,kcall f(V293_TimeSet_body now ticks saved)caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,(enabled,si,ci))
      (curs(sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,op) |=
      V293_time_cell true saved bs(Vint32 Int.zero) **
        (V293_time_cell false now bn(Vint32 n) ** (V293_time_cell true ticks bt(Vint32 n) ** R)) /\
    (forall b i,b<>bt -> b<>bs -> get Mf(b,i)=get Mc(b,i)) /\
    (forall k,k<4 -> get Mf(bt,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
  intros P ks ge caller M ir enabled si ci O op now ticks saved bn bt bs clock n R f
    Different Blocks Owned.
  assert(Saved:get(V293_time_call_locals ticks saved bt bs)saved=Some(bs,Tint32)).
  { unfold V293_time_call_locals. apply map_get_set. }
  destruct(V293_time_body_prefix P(kcall f(V293_TimeSet_body now ticks saved)caller ks)
    ge _ M ir enabled si ci O op saved bs false now bn(Vint32 clock) true ticks bt n
    sret R Saved Owned)as(Mz&Mc&Zero&Copy&Prefix&Post).
  assert(Locals:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true ticks bt(Vint32 n) **
      (V293_time_cell true saved bs(Vint32 Int.zero) ** (V293_time_cell false now bn(Vint32 n) ** R))).
  { clear -Post. sep auto. }
  destruct(V293_time_locals_return P ks ge caller Mc ir (enabled,si,ci) O op
    ticks saved bt bs(Vint32 n)(Vint32 Int.zero) f(V293_TimeSet_body now ticks saved)
    None _ Different Blocks Locals)as(Mf&Return&Frame&Removed).
  exists Mz. exists Mc. exists Mf. split;[exact Zero | ]. split;[exact Copy | ]. split.
  - eapply V293_local_trans;[exact Prefix | exact Return].
  - split;[exact Post | ]. split;assumption.
Qed.
