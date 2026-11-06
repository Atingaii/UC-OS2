(* Generated complete time functions, from a caller-owned ready/clock core
   through allocation, linearization and return. Finite local paths only. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPIRefinement.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeNamesGood.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_source_time_current_good : forall t,
  GoodFunAsrt(CurTid t) /\ can_change_aop(CurTid t).
Proof. intros. unfold CurTid,Agvarmapsto,Aptrmapsto. simpl. auto. Qed.

Lemma V293_source_time_entry_core : forall br bg bp bn t ge caller le M ir aux O op ir' aux' op',
  (ge,caller,M,ir,aux,O,op) |= V293_time_ready_core br bg bp bn ** CurTid t ->
  (ge,le,M,ir',aux',O,op') |= V293_time_ready_core br bg bp bn ** CurTid t.
Proof.
  intros br bg bp bn t ge caller le M ir aux O op ir' aux' op' Held.
  apply sat_split in Held. destruct Held as(m1&m2&o1&o2&JM&JO&Core&Current).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM | ]. split;[exact JO | ]. split.
  - eapply V293_time_ready_entry_context;[reflexivity | exact Core].
  - eapply V293_current_entry_context;[reflexivity | exact Current].
Qed.

Lemma V293_source_time_empty_names : forall ge ir aux op now ticks saved bn bt bs,
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  (ge,V293_time_call_locals ticks saved bt bs,emp,ir,aux,emp,op) |=
    V293_time_binding true saved bs ** (V293_time_binding true ticks bt **
      V293_time_binding false now bn).
Proof.
  intros ge ir aux op now ticks saved bn bt bs TS NT NS Global.
  assert(S:(ge,V293_time_call_locals ticks saved bt bs,emp,ir,aux,emp,op) |=
    V293_time_binding true saved bs).
  { exists bs. split;[apply map_get_set | ]. repeat split;reflexivity. }
  assert(T:(ge,V293_time_call_locals ticks saved bt bs,emp,ir,aux,emp,op) |=
    V293_time_binding true ticks bt).
  { exists bt. split;[ | repeat split;reflexivity].
    change(get(V293_time_call_locals ticks saved bt bs)ticks=Some(bt,Tint32)).
    unfold V293_time_call_locals. rewrite map_get_set' by congruence. apply map_get_set. }
  assert(N:(ge,V293_time_call_locals ticks saved bt bs,emp,ir,aux,emp,op) |=
    V293_time_binding false now bn).
  { split.
    - exists bn. split;[exact Global | ]. repeat split;reflexivity.
    - split;[ | split;reflexivity]. intros[v E]. change(get(V293_time_call_locals ticks saved bt bs)now=Some v)in E.
      unfold V293_time_call_locals in E.
      repeat rewrite map_get_set' in E by congruence. rewrite map_emp_get in E. discriminate. }
  apply sat_split'. exists empmem. exists empmem. exists empabst. exists empabst.
  split;[apply map_join_emp | ]. split;[apply map_join_emp | ]. split;[exact S | ].
  apply sat_split'. exists empmem. exists empmem. exists empabst. exists empabst.
  split;[apply map_join_emp | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.

Lemma V293_source_time_name_owned : forall br bg bp bn t ge M ir aux O op
    now ticks saved bt bs clock tmp,
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  get O ostmid=Some(ostm clock) ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    Amapsto(bs,0%Z) Tint32 true Vundef ** (Amapsto(bt,0%Z) Tint32 true tmp **
      (V293_time_ready_core br bg bp bn ** CurTid t)) ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    V293_time_cell true saved bs Vundef ** (V293_time_cell true ticks bt tmp **
      (V293_time_cell false now bn(Vint32 clock) **
        (V293_time_ready_fields br bg bp clock ** CurTid t))).
Proof.
  intros br bg bp bn t ge M ir aux O op now ticks saved bt bs clock tmp TS NT NS Global Slot Held.
  unfold V293_time_ready_core in Held. sep normal in Held. sep destruct Held.
  assert(Actual:get O ostmid=Some(ostm x)).
  { change(get(getabst(ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op))ostmid=Some(ostm x)).
    eapply V293_star_abst_get_l with(p:=V293_time_ready_fields br bg bp x)(q:=Atrue).
    - apply V293_time_ready_fields_clock.
    - clear -Held. sep auto. }
  rewrite Slot in Actual. inversion Actual;subst x.
  pose proof(V293_source_time_empty_names ge ir aux op now ticks saved bn bt bs TS NT NS Global)as Names.
  assert(Packed:(ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op) |=
    (V293_time_binding true saved bs ** (V293_time_binding true ticks bt **
      V293_time_binding false now bn)) **
    (Amapsto(bs,0%Z) Tint32 true Vundef ** (Amapsto(bt,0%Z) Tint32 true tmp **
      ((V293_time_ready_fields br bg bp clock ** PV(bn,Int.zero)@Tint32|->Vint32 clock) ** CurTid t)))).
  { apply sat_split'. exists empmem. exists M. exists empabst. exists O.
    split;[apply map_join_comm;apply map_join_emp | ].
    split;[apply map_join_comm;apply map_join_emp | ]. split;[exact Names | ].
    clear -Held. sep auto. }
  unfold V293_time_cell,Aptrmapsto. clear -Packed. sep auto.
Qed.

Theorem V293_source_time_get_ready_call : forall br bg bp bn t P sd ks ge caller M ir enabled si ci O
    f now ticks saved bt bs clock,
  P f=Some(V293_source_OSTimeGet_function now ticks saved) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M bt -> fresh M bs -> bt<>bs -> get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,(enabled,si,ci),O,V293_time_get_action) |=
    V293_time_ready_core br bg bp bn ** CurTid t ->
  exists Mc Mf,
    V293_local_steps P (curs(scall f []),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
      (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    V293_local_steps P (curs(scall f []),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
      (curs(sprim excrit),(kenil,kseq(srete(evar ticks))(kcall f(V293_TimeGet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci)) /\
    V293_local_steps P
      (curs(sprim excrit),(kenil,kseq(srete(evar ticks))(kcall f(V293_TimeGet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci))
      (curs(sskip(Some(Vint32 clock))),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    spec_step sd V293_time_get_action O(END(Some(Vint32 clock)))O /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),
      O,END(Some(Vint32 clock))) |= V293_time_ready_core br bg bp bn ** Atrue /\
    (ge,caller,Mf,ir,(enabled,si,ci),O,END(Some(Vint32 clock))) |=
      V293_time_ready_core br bg bp bn ** CurTid t /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp bn t P sd ks ge caller M ir enabled si ci O f now ticks saved bt bs clock
    Program TS NT NS Global FT FS Blocks Slot Held.
  rewrite V293_source_time_get_exact in Program.
  pose proof(V293_source_time_entry_core br bg bp bn t ge caller
    (V293_time_call_locals ticks saved bt bs) M ir(enabled,si,ci)O V293_time_get_action ir(enabled,si,ci)V293_time_get_action Held)as Callee.
  destruct(V293_time_get_call_entry P ks ge caller M ir(enabled,si,ci)O V293_time_get_action f
    now ticks saved bt bs(V293_time_ready_core br bg bp bn ** CurTid t) Program TS FT
    (V293_time_fresh_after_alloc M bt bs Blocks FS) Callee)as[Call Owned].
  pose proof(V293_source_time_name_owned br bg bp bn t ge _ ir(enabled,si,ci)O V293_time_get_action
    now ticks saved bt bs clock Vundef TS NT NS Global Slot Owned)as Named.
  destruct(V293_source_time_current_good t)as[Good Free].
  destruct(V293_time_get_body_refinement br bg bp P sd ks ge caller _ ir enabled si ci O
    now ticks saved bn bt bs clock Vundef(CurTid t) f TS Good Free Named)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  exists Mc. exists Mf. split.
  - eapply V293_local_trans;[exact Call | ]. eapply V293_local_trans;[exact Prefix | exact Suffix].
  - split;[eapply V293_local_trans;[exact Call | exact Prefix] | ].
    split;[exact Suffix | ]. split;[exact Step | ]. split;[exact Closed | ]. split;assumption.
Qed.

Theorem V293_source_time_set_ready_call : forall br bg bp bn t P sd ks ge caller M ir enabled si ci O
    f now ticks saved bt bs clock n,
  P f=Some(V293_source_OSTimeSet_function now ticks saved) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M bt -> fresh M bs -> bt<>bs -> get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,(enabled,si,ci),O,V293_time_set_action n) |=
    V293_time_ready_core br bg bp bn ** CurTid t ->
  exists Mc Mf,
    V293_local_steps P (curs(scall f [econst32 n]),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
      (curs(sskip None),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    V293_local_steps P (curs(scall f [econst32 n]),(kenil,ks)) ((ge,caller,M),ir,(enabled,si,ci))
      (curs(sprim excrit),(kenil,kseq(sret)(kcall f(V293_TimeSet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci)) /\
    V293_local_steps P
      (curs(sprim excrit),(kenil,kseq(sret)(kcall f(V293_TimeSet_body now ticks saved)caller ks)))
      ((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci))
      (curs(sskip(None)),(kenil,ks)) ((ge,caller,Mf),ir,(enabled,si,ci)) /\
    spec_step sd(V293_time_set_action n)O(END None)(set O ostmid(ostm n)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),
      set O ostmid(ostm n),END None) |= V293_time_ready_core br bg bp bn ** Atrue /\
    (ge,caller,Mf,ir,(enabled,si,ci),set O ostmid(ostm n),END None) |=
      V293_time_ready_core br bg bp bn ** CurTid t /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp bn t P sd ks ge caller M ir enabled si ci O f now ticks saved bt bs clock n
    Program TS NT NS Global FT FS Blocks Slot Held.
  rewrite V293_source_time_set_exact in Program.
  pose proof(V293_source_time_entry_core br bg bp bn t ge caller
    (V293_time_call_locals ticks saved bt bs) M ir(enabled,si,ci)O(V293_time_set_action n) ir(enabled,si,ci)(V293_time_set_action n) Held)as Callee.
  destruct(V293_time_set_call_entry P ks ge caller M ir(enabled,si,ci)O(V293_time_set_action n)f
    now ticks saved bt bs n(V293_time_ready_core br bg bp bn ** CurTid t) Program TS FT FS Blocks Callee)
    as(Mp&Ma&ParameterStore&Memory&Call&Owned).
  pose proof(V293_source_time_name_owned br bg bp bn t ge Ma ir(enabled,si,ci)O(V293_time_set_action n)
    now ticks saved bt bs clock(Vint32 n) TS NT NS Global Slot Owned)as Named.
  assert(Reorder:(ge,V293_time_call_locals ticks saved bt bs,Ma,ir,(enabled,si,ci),O,V293_time_set_action n) |=
    V293_time_cell true saved bs Vundef ** (V293_time_cell false now bn(Vint32 clock) **
      (V293_time_cell true ticks bt(Vint32 n) ** (V293_time_ready_fields br bg bp clock ** CurTid t)))).
  { clear -Named. sep auto. }
  destruct(V293_source_time_current_good t)as[Good Free].
  destruct(V293_time_set_body_refinement br bg bp P sd ks ge caller Ma ir enabled si ci O
    now ticks saved bn bt bs clock n(CurTid t) f TS Good Free Reorder)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  exists Mc. exists Mf. split.
  - eapply V293_local_trans;[exact Call | ]. eapply V293_local_trans;[exact Prefix | exact Suffix].
  - split;[eapply V293_local_trans;[exact Call | exact Prefix] | ].
    split;[exact Suffix | ]. split;[exact Step | ]. split;[exact Closed | ]. split;assumption.
Qed.

(* Same generated program, real API builders and shared ready invariant.
   The body contracts themselves are the existing strong contracts. *)
Theorem V293_source_time_ready_api_rule : forall br bg bp fget fset now ticks saved bn Spec sd li lg,
  fget <> fset -> ticks <> saved -> now <> ticks -> now <> saved ->
  GoodLInvAsrt li -> NoAbs li ->
  (forall t args, p_local li t args ==>
    Agvarenv now Tint32 (bn,0%Z) ** p_local li t args) ->
  APIRule (V293_source_time_program fget fset now ticks saved)
    (V293_source_time_spec fget fset) Spec sd li (V293_time_ready_inv br bg bp bn) lg.
Proof.
  intros br bg bp fget fset now ticks saved bn Spec sd li lg GS TS NT NS Good NA Globals.
  apply api_rule;[apply V293_source_time_domains | ].
  intros f ab vl pre post ft tid API Pre Post.
  unfold V293_source_time_spec in API.
  destruct (Z.eq_dec f fget) as [Get | NotGet].
  - inversion API;subst ab ft.
    assert (Code : V293_source_time_program fget fset now ticks saved f =
      Some (V293_TimeGet_function now ticks saved)).
    { unfold V293_source_time_program. destruct (Z.eq_dec f fget);
        [rewrite V293_source_time_get_exact;reflexivity | contradiction]. }
    exists Tint32. exists dnil. exists (dcons ticks Tint32 (dcons saved Tint32 dnil)).
    exists (V293_source_OSTimeGet_body now ticks saved). split.
    + exact Code.
    + change (InfRules Spec sd li (V293_time_ready_inv br bg bp bn) post Afalse pre
        (V293_TimeGet_body now ticks saved) Afalse tid).
      eapply V293_TimeGet_ready_api_contract; eassumption.
  - destruct (Z.eq_dec f fset) as [Setter | NotSetter];try discriminate.
    inversion API;subst ab ft.
    assert (Code : V293_source_time_program fget fset now ticks saved f =
      Some (V293_TimeSet_function now ticks saved)).
    { unfold V293_source_time_program. destruct (Z.eq_dec f fget);[contradiction | ].
      destruct (Z.eq_dec f fset);
        [rewrite V293_source_time_set_exact;reflexivity | contradiction]. }
    exists Tvoid. exists (dcons ticks Tint32 dnil). exists (dcons saved Tint32 dnil).
    exists (V293_source_OSTimeSet_body now ticks saved). split.
    + exact Code.
    + change (InfRules Spec sd li (V293_time_ready_inv br bg bp bn) post Afalse pre
        (V293_TimeSet_body now ticks saved) Afalse tid).
      eapply V293_TimeSet_ready_api_contract; eassumption.
Qed.

Theorem V293_source_time_ready_coherent : forall br bg bp fget fset now ticks saved bn Spec lg,
  fget <> fset -> ticks <> saved -> now <> ticks -> now <> saved ->
  GoodI (V293_time_ready_inv br bg bp bn) V293_scheduler (V293_time_names_li now bn) /\
  APIRule (V293_source_time_program fget fset now ticks saved)
    (V293_source_time_spec fget fset) Spec V293_scheduler
    (V293_time_names_li now bn) (V293_time_ready_inv br bg bp bn) lg.
Proof.
  intros. split;[apply V293_time_ready_names_good | ].
  apply V293_source_time_ready_api_rule;try assumption.
  - apply V293_time_names_local_good.
  - apply V293_time_names_noabs.
  - apply V293_time_names_global.
Qed.

Lemma V293_source_time_clock_owned : forall br bg bp bn ge le M ir aux O op clock R,
  get O ostmid=Some(ostm clock) ->
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core br bg bp bn ** R ->
  load Tint32 M(bn,0%Z)=Some(Vint32 clock).
Proof.
  intros br bg bp bn ge le M ir aux O op clock R Slot Held.
  destruct(V293_time_ready_clock_agreement br bg bp bn R _ Held)as(n&Actual&Load).
  change(get O ostmid=Some(ostm n))in Actual. rewrite Slot in Actual.
  inversion Actual;subst n. exact Load.
Qed.
