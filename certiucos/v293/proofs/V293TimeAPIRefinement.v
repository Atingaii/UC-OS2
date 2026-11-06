(* The original critical copy, a legal abstract step before excrit, and exact
   residual ownership after real free/return. Finite paths, not all schedules. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPILifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
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

Lemma V293_time_freels_value : forall al P ks ge le M Mf result,
  freels al M Mf ->
  cstepstar P (curs(sfree al result),(kenil,ks))(ge,le,M)
    (curs(sfree nil result),(kenil,ks))(ge,le,Mf).
Proof.
  intros al P ks ge le M Mf result Free. induction Free.
  - apply c_stepstar0.
  - eapply c_stepstarn.
    + eapply stmt_step;[reflexivity | ]. eapply sfree_step;[reflexivity | reflexivity | exact H].
    + exact IHFree.
Qed.

Lemma V293_time_owned_return : forall P ks ge caller M ir aux O op
    ticks saved bt bs tmp save f body result R,
  ticks<>saved -> GoodFunAsrt R ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    Amapsto(bt,0%Z) Tint32 true tmp ** (Amapsto(bs,0%Z) Tint32 true save ** R) ->
  exists Mf,
    V293_local_steps P (V293_time_return_start result(kcall f body caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,aux)
      (curs(sskip result),(kenil,ks)) ((ge,caller,Mf),ir,aux) /\
    (ge,caller,Mf,ir,aux,O,op) |= R /\
    freels (getaddr(V293_time_call_locals ticks saved bt bs)) M Mf.
Proof.
  intros P ks ge caller M ir aux O op ticks saved bt bs tmp save f body result R Different Good Held.
  pose proof(V293_time_local_layout ticks saved bt bs Different)as Layout.
  apply Permutation_sym in Layout. apply Permutation_length_2_inv in Layout.
  assert(Free:exists Mf,freels(getaddr(V293_time_call_locals ticks saved bt bs)) M Mf /\
    (ge,V293_time_call_locals ticks saved bt bs,Mf,ir,aux,O,op) |= R).
  { destruct Layout as[Layout|Layout].
    - destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(M1&F1&Rest).
      destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Rest)as(Mf&F2&Returned).
      exists Mf. split;[rewrite Layout;econstructor;[exact F1|econstructor;[exact F2|constructor]]|exact Returned].
    - assert(Swapped:(ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
        Amapsto(bs,0%Z) Tint32 true save ** (Amapsto(bt,0%Z) Tint32 true tmp ** R)).
      { clear -Held. sep auto. }
      destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Swapped)as(M1&F1&Rest).
      destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Rest)as(Mf&F2&Returned).
      exists Mf. split;[rewrite Layout;econstructor;[exact F1|econstructor;[exact F2|constructor]]|exact Returned]. }
  destruct Free as(Mf&Free&Returned). exists Mf. split.
  - apply V293_csteps_local. unfold V293_time_return_start.
    eapply V293_cstepstar_trans with(C2:=(curs(sfree(getaddr(V293_time_call_locals ticks saved bt bs))result),
      (kenil,kcall f body caller ks))).
    + destruct result as [value | ].
      * eapply c_stepstarn.
        { eapply stmt_step;[reflexivity | ].
          eapply (sretv_step P f _ body);[reflexivity | cbn;discriminate | reflexivity]. }
        apply c_stepstar0.
      * eapply c_stepstarn.
        { eapply stmt_step;[reflexivity | ]. eapply sret_step;reflexivity. }
        apply c_stepstar0.
    + eapply V293_cstepstar_trans;[apply V293_time_freels_value;exact Free | ].
      eapply c_stepstarn;[eapply stmt_step;[reflexivity | eapply sfreeend_step;reflexivity] | apply c_stepstar0].
  - split;[eapply good_fun_asrt_absop;[exact Good | exact Returned] | exact Free].
Qed.

(* Ownership is stated at the original auxiliary snapshot. The operational
   endpoint is disabled with the saved IE pushed; no arbitrary frame is
   transported to that different snapshot. *)
Lemma V293_time_copy_before_exit : forall P ks ge le M ir enabled si ci O op
    saved bs dl dst bd old sl src bc n tail R,
  get le saved=Some(bs,Tint32) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell dl dst bd old ** (V293_time_cell sl src bc(Vint32 n) ** R)) ->
  exists Mz Mc,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bd,0%Z)(Vint32 n)=Some Mc /\
    V293_local_steps P
      (curs(sseq(sassign(evar saved)(econst32 Int.zero))
        (sseq(sseq(sprim encrit)(sseq(sassign(evar dst)(evar src))(sprim excrit)))tail)),(kenil,ks))
      ((ge,le,M),ir,(enabled,si,ci))
      (curs(sprim excrit),(kenil,kseq tail ks)) ((ge,le,Mc),ir,(false,si,enabled::ci)) /\
    (ge,le,Mc,ir,(enabled,si,ci),O,op) |=
      V293_time_cell true saved bs(Vint32 Int.zero) **
        (V293_time_cell dl dst bd(Vint32 n) ** (V293_time_cell sl src bc(Vint32 n) ** R)).
Proof.
  intros P ks ge le M ir enabled si ci O op saved bs dl dst bd old sl src bc n tail R Saved Owned.
  destruct(V293_time_cell_store true saved bs Vundef Int.zero _ _ _ _ _ _ _ _ Owned)
    as(Mz&Zero&AfterZero).
  assert(Target:(ge,le,Mz,ir,(enabled,si,ci),O,op) |=
    V293_time_cell dl dst bd old ** (V293_time_cell sl src bc(Vint32 n) **
      (V293_time_cell true saved bs(Vint32 Int.zero) ** R))).
  { clear -AfterZero. sep auto. }
  destruct(V293_time_cell_store dl dst bd old n _ _ _ _ _ _ _ _ Target)as(Mc&Copy&AfterCopy).
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
    apply V293_local_refl.
  - clear -AfterCopy. sep auto.
Qed.

Lemma V293_time_inv_action : forall A, GoodInvAsrt A -> can_change_aop A.
Proof. induction A; simpl; intros G; try exact I; try contradiction;
  try (destruct G; split; auto; fail); try (intro x; eauto).
  all: match goal with |- (if ?b then _ else _) => destruct b; exact I end. Qed.

Lemma V293_time_core_return_good : forall br bg bp bn R,
  GoodFunAsrt R -> GoodFunAsrt(V293_time_ready_core br bg bp bn ** R).
Proof.
  intros br bg bp bn R Good. split;[ | exact Good].
  apply V293_inv_function_assertion. apply V293_time_ready_core_good.
Qed.

Lemma V293_time_set_sync_owned : forall br bg bp bn old n R ge le M ir aux O,
  can_change_aop R ->
  (ge,le,M,ir,aux,O,V293_time_set_action n) |=
    V293_time_ready_fields br bg bp old ** (PV(bn,Int.zero) @ Tint32 |-> Vint32 n ** R) ->
  (ge,le,M,ir,aux,set O ostmid(ostm n),END None) |= V293_time_ready_core br bg bp bn ** R.
Proof.
  intros br bg bp bn old n R ge le M ir aux O Free Held.
  assert(Packed:(ge,le,M,ir,aux,O,V293_time_set_action n) |= Aabsdata ostmid(ostm old) **
    ((EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map,
      (CurTid t ** (Aabsdata curtid(oscurt t) **
        (Aabsdata abstcblsid(abstcblist ts) ** Aabsdata absecblsid(absecblist es)))) **
      V293_ready_payload br bg bp ts) ** (PV(bn,Int.zero) @ Tint32 |-> Vint32 n ** R))).
  { unfold V293_time_ready_fields,V293_shared_fields in Held. clear -Held. sep auto. }
  apply V293_shared_replace_slot with(new:=ostm n)in Packed.
  eapply change_aop_rule with(aop:=V293_time_set_action n).
  - unfold V293_time_ready_core,V293_time_ready_fields,V293_shared_fields. clear -Packed. sep auto.
  - split;[ | exact Free]. apply V293_time_inv_action. apply V293_time_ready_core_good.
Qed.

Lemma V293_time_core_frame_aux : forall br bg bp bn ge le M ir aux O op ir' aux',
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core br bg bp bn ** Atrue ->
  (ge,le,M,ir',aux',O,op) |= V293_time_ready_core br bg bp bn ** Atrue.
Proof.
  intros br bg bp bn ge le M ir aux O op ir' aux' Held.
  apply sat_split in Held. destruct Held as(m1&m2&o1&o2&JM&JO&Core&Rest).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM | ]. split;[exact JO | ]. split;[ | exact I].
  eapply V293_time_ready_core_aux;exact Core.
Qed.

Lemma V293_time_cell_raw : forall local x b v,
  V293_time_cell local x b v ==> PV(b,Int.zero) @ Tint32 |-> v.
Proof.
  intros local x b v s Held. unfold V293_time_cell in Held.
  eapply astar_l_aemp_elim. eapply astar_mono;[ | intros st H; exact H | exact Held].
  intros st H. destruct local.
  - exact(proj2(@alvarenv_elim _ _ _ _ H)).
  - unfold V293_time_binding,V293_counter_bindings in H.
    exact(proj2(@agvarenv_elim _ _ _ _ (proj1 H))).
Qed.

Theorem V293_time_set_body_refinement : forall br bg bp P sd ks ge caller M ir enabled si ci O
    now ticks saved bn bt bs clock n R f,
  ticks<>saved -> GoodFunAsrt R -> can_change_aop R ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,(enabled,si,ci),O,V293_time_set_action n) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell false now bn(Vint32 clock) ** (V293_time_cell true ticks bt(Vint32 n) **
        (V293_time_ready_fields br bg bp clock ** R))) ->
  exists Mz Mc Mf,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bn,0%Z)(Vint32 n)=Some Mc /\
    V293_local_steps P
      (curs(V293_TimeSet_body now ticks saved),
        (kenil,kcall f(V293_TimeSet_body now ticks saved)caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,(enabled,si,ci))
      (curs(sprim excrit),(kenil,kseq sret(kcall f(V293_TimeSet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci)) /\
    spec_step sd(V293_time_set_action n)O(END None)(set O ostmid(ostm n)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),
      set O ostmid(ostm n),END None) |= V293_time_ready_core br bg bp bn ** Atrue /\
    V293_local_steps P
      (curs(sprim excrit),(kenil,kseq sret(kcall f(V293_TimeSet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci))
      (curs(sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (ge,caller,Mf,ir,(enabled,si,ci),set O ostmid(ostm n),END None) |=
      V293_time_ready_core br bg bp bn ** R /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp P sd ks ge caller M ir enabled si ci O now ticks saved bn bt bs clock n R f
    Different Good Free Owned.
  assert(Saved:get(V293_time_call_locals ticks saved bt bs)saved=Some(bs,Tint32)).
  { unfold V293_time_call_locals. apply map_get_set. }
  destruct(V293_time_copy_before_exit P(kcall f(V293_TimeSet_body now ticks saved)caller ks)
    ge _ M ir enabled si ci O(V293_time_set_action n) saved bs false now bn(Vint32 clock)
    true ticks bt n sret _ Saved Owned)as(Mz&Mc&Zero&Copy&Prefix&Post).
  assert(Time:get O ostmid=Some(ostm clock)).
  { change(get(getabst(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
      V293_time_set_action n))ostmid=Some(ostm clock)).
    eapply V293_star_abst_get_l with(p:=V293_time_ready_fields br bg bp clock)(q:=Atrue).
    - apply V293_time_ready_fields_clock.
    - clear -Post. sep auto. }
  assert(SyncInput:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
    V293_time_set_action n) |= V293_time_ready_fields br bg bp clock **
      (PV(bn,Int.zero) @ Tint32 |-> Vint32 n **
        (Amapsto(bt,0%Z) Tint32 true(Vint32 n) ** (Amapsto(bs,0%Z) Tint32 true(Vint32 Int.zero) ** R)))).
  { assert(Raw:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
        V293_time_set_action n) |= PV(bs,Int.zero) @ Tint32 |-> Vint32 Int.zero **
        (PV(bn,Int.zero) @ Tint32 |-> Vint32 n ** (PV(bt,Int.zero) @ Tint32 |-> Vint32 n **
          (V293_time_ready_fields br bg bp clock ** R)))).
    { eapply astar_mono;[apply V293_time_cell_raw | | exact Post].
      eapply astar_mono;[apply V293_time_cell_raw | ].
      eapply astar_mono;[apply V293_time_cell_raw | intros st H;exact H]. }
    clear -Raw. unfold Aptrmapsto in *. sep auto. }
  pose proof(V293_time_set_sync_owned br bg bp bn clock n
    (Amapsto(bt,0%Z) Tint32 true(Vint32 n) ** (Amapsto(bs,0%Z) Tint32 true(Vint32 Int.zero) ** R))
    _ _ _ _ _ _ ltac:(simpl;auto) SyncInput)as Synced.
  assert(ReturnInput:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),
    set O ostmid(ostm n),END None) |= Amapsto(bt,0%Z) Tint32 true(Vint32 n) **
      (Amapsto(bs,0%Z) Tint32 true(Vint32 Int.zero) ** (V293_time_ready_core br bg bp bn ** R))).
  { clear -Synced. sep auto. }
  destruct(V293_time_owned_return P ks ge caller Mc ir(enabled,si,ci)(set O ostmid(ostm n))(END None)
    ticks saved bt bs(Vint32 n)(Vint32 Int.zero) f(V293_TimeSet_body now ticks saved) None _
    Different(V293_time_core_return_good br bg bp bn R Good) ReturnInput)as(Mf&Return&Final&Freed).
  exists Mz. exists Mc. exists Mf. split;[exact Zero | ]. split;[exact Copy | ].
  split;[exact Prefix | ]. split;[apply V293_time_set_transition with(old:=clock);exact Time | ]. split.
  - eapply V293_time_core_frame_aux with(ir:=ir)(aux:=(enabled,si,ci)). clear -Synced. sep auto.
  - split.
    + eapply V293_local_cons. { apply excrit_step;reflexivity. }
      eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
      exact Return.
    + split;assumption.
Qed.

Theorem V293_time_get_body_refinement : forall br bg bp P sd ks ge caller M ir enabled si ci O
    now ticks saved bn bt bs clock tmp R f,
  ticks<>saved -> GoodFunAsrt R -> can_change_aop R ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,(enabled,si,ci),O,V293_time_get_action) |=
    V293_time_cell true saved bs Vundef **
      (V293_time_cell true ticks bt tmp ** (V293_time_cell false now bn(Vint32 clock) **
        (V293_time_ready_fields br bg bp clock ** R))) ->
  exists Mz Mc Mf,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bt,0%Z)(Vint32 clock)=Some Mc /\
    V293_local_steps P
      (curs(V293_TimeGet_body now ticks saved),
        (kenil,kcall f(V293_TimeGet_body now ticks saved)caller ks))
      ((ge,V293_time_call_locals ticks saved bt bs,M),ir,(enabled,si,ci))
      (curs(sprim excrit),(kenil,kseq(srete(evar ticks))(kcall f(V293_TimeGet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci)) /\
    spec_step sd V293_time_get_action O(END(Some(Vint32 clock)))O /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),
      O,END(Some(Vint32 clock))) |= V293_time_ready_core br bg bp bn ** Atrue /\
    V293_local_steps P
      (curs(sprim excrit),(kenil,kseq(srete(evar ticks))(kcall f(V293_TimeGet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci))
      (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    (ge,caller,Mf,ir,(enabled,si,ci),O,END(Some(Vint32 clock))) |=
      V293_time_ready_core br bg bp bn ** R /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp P sd ks ge caller M ir enabled si ci O now ticks saved bn bt bs clock tmp R f
    Different Good Free Owned.
  assert(Saved:get(V293_time_call_locals ticks saved bt bs)saved=Some(bs,Tint32)).
  { unfold V293_time_call_locals. apply map_get_set. }
  destruct(V293_time_copy_before_exit P(kcall f(V293_TimeGet_body now ticks saved)caller ks)
    ge _ M ir enabled si ci O V293_time_get_action saved bs true ticks bt tmp
    false now bn clock(srete(evar ticks)) _ Saved Owned)as(Mz&Mc&Zero&Copy&Prefix&Post).
  assert(Time:get O ostmid=Some(ostm clock)).
  { change(get(getabst(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
      V293_time_get_action))ostmid=Some(ostm clock)).
    eapply V293_star_abst_get_l with(p:=V293_time_ready_fields br bg bp clock)(q:=Atrue).
    - apply V293_time_ready_fields_clock.
    - clear -Post. sep auto. }
  assert(Read:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,V293_time_get_action) |=
    V293_time_cell true ticks bt(Vint32 clock) ** Atrue).
  { clear -Post. sep auto. }
  destruct(V293_time_cell_read true ticks bt clock Atrue _ Read)as[Value Typed].
  assert(Raw:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
      V293_time_get_action) |= PV(bs,Int.zero) @ Tint32 |-> Vint32 Int.zero **
      (PV(bt,Int.zero) @ Tint32 |-> Vint32 clock ** (PV(bn,Int.zero) @ Tint32 |-> Vint32 clock **
        (V293_time_ready_fields br bg bp clock ** R)))).
  { eapply astar_mono;[apply V293_time_cell_raw | | exact Post].
    eapply astar_mono;[apply V293_time_cell_raw | ].
    eapply astar_mono;[apply V293_time_cell_raw | intros st H;exact H]. }
  assert(ReturnInput:(ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(enabled,si,ci),O,
    END(Some(Vint32 clock))) |= Amapsto(bt,0%Z) Tint32 true(Vint32 clock) **
      (Amapsto(bs,0%Z) Tint32 true(Vint32 Int.zero) ** (V293_time_ready_core br bg bp bn ** R))).
  { eapply change_aop_rule with(aop:=V293_time_get_action).
    - unfold V293_time_ready_core,Aptrmapsto in *. clear -Raw. sep auto.
    - split;[exact I | ]. split;[exact I | ]. split;[ | exact Free].
      apply V293_time_inv_action. apply V293_time_ready_core_good. }
  destruct(V293_time_owned_return P ks ge caller Mc ir(enabled,si,ci)O(END(Some(Vint32 clock)))
    ticks saved bt bs(Vint32 clock)(Vint32 Int.zero) f(V293_TimeGet_body now ticks saved)(Some(Vint32 clock)) _
    Different(V293_time_core_return_good br bg bp bn R Good) ReturnInput)as(Mf&Return&Final&Freed).
  exists Mz. exists Mc. exists Mf. split;[exact Zero | ]. split;[exact Copy | ].
  split;[exact Prefix | ]. split;[apply V293_time_get_transition;exact Time | ]. split.
  - eapply V293_time_core_frame_aux with(ir:=ir)(aux:=(enabled,si,ci)). clear -ReturnInput. sep auto.
  - split.
    + eapply V293_local_cons. { apply excrit_step;reflexivity. }
      eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply sskip_step]. }
      eapply V293_local_cons. { apply ostc_step. eapply stmt_step;[reflexivity | apply srete_step]. }
      eapply V293_local_trans.
      { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Value. }
      exact Return.
    + split;assumption.
Qed.
