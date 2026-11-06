(* Reassemble canonical ownership from JOINTLY separated task records.
   Loads alone, or two overlapping Atrue projections, do not suffice. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_task_list_nodup : forall entries,
  TcbMod.is_orderset entries -> NoDup entries.
Proof.
  induction entries as [ | [head value] rest IH]; intros Order; [constructor | ].
  destruct Order as [Lower Order]. constructor; [ | apply IH; exact Order].
  intro Member. pose proof (V293_task_list_member_lookup rest head value Order Member) as Lookup.
  rewrite (@TcbMod.lb_notin rest head Lower) in Lookup. discriminate.
Qed.

Lemma V293_task_update_enumeration : forall tasks t value,
  Permutation ((t,value)::TcbMod.lst (del tasks t)) (TcbMod.lst (set tasks t value)).
Proof.
  intros tasks t value. apply NoDup_Permutation.
  - constructor.
    + intro Member.
      pose proof (V293_task_list_member_lookup _ _ _ (TcbMod.prf (del tasks t)) Member) as Lookup.
      change (get (del tasks t) t = Some value) in Lookup.
      rewrite map_del_sem in Lookup; destruct (map_dec_a t t); [ | contradiction]. discriminate.
    + apply V293_task_list_nodup. apply TcbMod.prf.
  - apply V293_task_list_nodup. apply TcbMod.prf.
  - intros [u v]. split.
    + intros [Same|Member].
      * inversion Same; subst. apply V293_task_lookup_list. change (get (set tasks u v) u = Some v). apply map_get_set.
      * pose proof (V293_task_list_member_lookup _ _ _ (TcbMod.prf (del tasks t)) Member) as Lookup.
        change (get (del tasks t) u = Some v) in Lookup.
        rewrite map_del_sem in Lookup.
        destruct (map_dec_a t u) as [Same|Apart]; [discriminate | ].
        apply V293_task_lookup_list. change (get (set tasks t value) u = Some v). rewrite map_get_set' by congruence. exact Lookup.
    + intro Member.
      pose proof (V293_task_list_member_lookup _ _ _ (TcbMod.prf (set tasks t value)) Member) as Lookup.
      change (get (set tasks t value) u = Some v) in Lookup.
      destruct (TcbMod.eq_dec u t) as [Same|Apart].
      * subst u. rewrite map_get_set in Lookup. inversion Lookup; subst v. left; reflexivity.
      * right. apply V293_task_lookup_list.
        change (get (del tasks t) u = Some v).
        rewrite map_del_sem. destruct (map_dec_a t u); [congruence | ].
        rewrite map_get_set' in Lookup by congruence. exact Lookup.
Qed.

Lemma V293_owned_task_list_permutation : forall before after,
  Permutation before after -> forall R s,
  s |= V293_owned_task_list before ** R -> s |= V293_owned_task_list after ** R.
Proof.
  intros before after Perm. induction Perm; intros R s Owned.
  - exact Owned.
  - destruct x as [t [[p st] msg]]. cbn [V293_owned_task_list] in *.
    assert (Opened : s |= V293_owned_task_list l ** (V293_owned_task_record t p st msg ** R))
      by (clear -Owned; sep auto).
    specialize (IHPerm _ _ Opened). clear -IHPerm. sep auto.
  - destruct x as [t [[p st] msg]]; destruct y as [u [[q ust] umsg]].
    cbn [V293_owned_task_list] in *. clear -Owned. sep auto.
  - apply IHPerm2. apply IHPerm1. exact Owned.
Qed.

Theorem V293_owned_task_records_reassemble : forall tasks t priority status message R s,
  s |= V293_owned_task_record t priority status message **
    (V293_owned_task_records (del tasks t) ** R) ->
  s |= V293_owned_task_records (set tasks t (priority,status,message)) ** R.
Proof.
  intros tasks t priority status message R s Owned.
  unfold V293_owned_task_records in *.
  eapply V293_owned_task_list_permutation;
    [apply V293_task_update_enumeration | ].
  cbn [V293_owned_task_list]. clear -Owned. sep auto.
Qed.

(* Focus any present task, including a non-head entry in canonical order.
   This is a permission-preserving inverse interface, not a fresh allocation. *)
Theorem V293_owned_task_records_focus : forall tasks t priority status message R s,
  get tasks t = Some (priority,status,message) ->
  s |= V293_owned_task_records tasks ** R ->
  s |= V293_owned_task_record t priority status message **
    (V293_owned_task_records (del tasks t) ** R).
Proof.
  intros tasks t priority status message R s Lookup Owned.
  assert (Same : set tasks t (priority,status,message)=tasks).
  { apply TcbMod.extensionality. intro u.
    change (get (set tasks t (priority,status,message)) u = get tasks u).
    destruct (TcbMod.eq_dec u t) as [Equal|Apart].
    - subst u. rewrite map_get_set. symmetry. exact Lookup.
    - rewrite map_get_set' by congruence. reflexivity. }
  assert (Order : Permutation ((t,(priority,status,message))::TcbMod.lst (del tasks t))
    (TcbMod.lst (set tasks t (priority,status,message)))).
  { apply V293_task_update_enumeration. }
  rewrite Same in Order. apply Permutation_sym in Order.
  assert (Focused : s |= V293_owned_task_list
      ((t,(priority,status,message))::TcbMod.lst (del tasks t)) ** R).
  { eapply V293_owned_task_list_permutation; [exact Order | exact Owned]. }
  cbn [V293_owned_task_list] in Focused. clear -Focused. sep auto.
Qed.

(* Keep R in the SAME separated fragment rather than recover it from a
   second Atrue projection, which would permit overlapping permissions. *)
Lemma V293_tick_wait_record_after_frame : forall b base d reason pend p message next R
    ge le M ir aux O op,
  (0<=base /\ base+54<=Int.max_unsigned)%Z -> p<13 -> pend<256 ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) ** R) ->
  (ge,le,M,ir,aux,O,op) |=
    V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
      (V293_tick_wait_status reason d) message ** (R ** Atrue).
Proof.
  intros b base d reason pend p message next R ge le M ir aux O op Base P Pend Owned.
  assert (Opened : (ge,le,M,ir,aux,O,op) |=
    (V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
     V293_owned_record_cells (V293_tick_record_extra b base p reason message)) ** R)
    by (clear -Owned; sep auto).
  assert (Result : (ge,le,M,ir,aux,O,op) |=
    (V293_owned_task_record (b,Int.repr base) (Int.repr (Z.of_nat p))
      (V293_tick_wait_status reason d) message ** Atrue) ** R).
  { eapply astar_mono; [ | | exact Opened]; [ | intros; assumption].
    intros st Cells. destruct st as [[[[[[ge' le'] M'] ir'] aux'] O'] op'].
    eapply V293_tick_wait_record_after with (R:=Aemp); [exact Base | exact P | exact Pend | ].
    clear -Cells. sep auto. }
  clear -Result. sep auto.
Qed.

(* Stable vertical interface: full canonical task ownership and the caller
   frame are jointly available in the actual execution result. *)
Theorem V293_tick_wait_iteration_owned_records :
  forall P ks ge le M ir enabled si ci O op sd ptcb rows group bc b base next d
    reason pend p bg br lo hi message current tasks events now entries R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  (0<=base /\ base+54<=Int.max_unsigned)%Z ->
  (0<=d<=Int.max_unsigned)%Z -> pend<256 -> p<13 -> p<>12 -> lo<256 -> hi<256 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks (b,Int.repr base) =
    Some (Int.repr (Z.of_nat p),wait reason (Int.repr d),message) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_owned_record_cell (V293_tick_pointer_cell bc (b,Int.repr base)) **
    (V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_wait_node b base d reason pend p) next) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br (V293_ready_group lo hi) lo hi) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    (V293_shared_fields current tasks events now ** R))))) ->
  exists Mf,
  let tasks' := set tasks (b,Int.repr base)
    (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message) in
  let O' := set O abstcblsid (abstcblist tasks') in
  let rr := V293_tick_wait_rows lo hi d p in
  spec_step sd (spec_prim nil (V293_tick_wait_step (b,Int.repr base))) O (END None) O' /\
  V293_local_steps P (curs (V293_tick_iteration ptcb rows group),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  V293_task_records Mf tasks' /\
  V293_priority_table entries tasks' /\ V293_bitmap_tasks (fst rr) (snd rr) tasks' /\
  (ge,le,Mf,ir,(enabled,si,ci),O',op) |=
    V293_owned_task_records tasks' **
    ((V293_owned_record_cell (V293_tick_pointer_cell bc next) **
     (V293_owned_record_cells (V293_tick_bitmap_cells bg br
        (V293_ready_group (fst rr) (snd rr)) (fst rr) (snd rr)) **
     (V293_shared_fields current tasks' events now ** R))) ** Atrue).
Proof.
  intros P ks ge le M ir enabled si ci O op sd ptcb rows group bc b base next d
    reason pend p bg br lo hi message current tasks events now entries R
    Bind Nr Gr Ng Gg Base D Pend Pr Nonidle Lo Hi Table Bitmap Task Owned.
  destruct (V293_tick_wait_iteration_refines P ks ge le M ir enabled si ci O op sd
    ptcb rows group bc b base next d reason pend p bg br lo hi message current tasks events now entries R
    Bind Nr Gr Ng Gg Base D Pend Pr Nonidle Lo Hi Table Bitmap Task Owned)
    as (Mf & Step & Exec & Records & Table' & Bitmap' & Returned).
  exists Mf. cbn zeta in *.
  split; [exact Step | ]. split; [exact Exec | ]. split; [exact Records | ].
  split; [exact Table' | ]. split; [exact Bitmap' | ].
  eapply V293_owned_task_records_reassemble.
  assert (Opened : (ge,le,Mf,ir,(enabled,si,ci),
      set O abstcblsid (abstcblist (set tasks (b,Int.repr base)
        (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message))),op) |=
    V293_owned_record_cells (V293_tick_task_cells
      (V293_tick_task_after (V293_tick_wait_node b base d reason pend p)) next) **
    (V293_owned_record_cells (V293_tick_record_extra b base p reason message) **
    (V293_owned_task_records (del tasks (b,Int.repr base)) **
    (V293_owned_record_cell (V293_tick_pointer_cell bc next) **
    (V293_owned_record_cells (V293_tick_bitmap_cells bg br
      (V293_ready_group (fst (V293_tick_wait_rows lo hi d p)) (snd (V293_tick_wait_rows lo hi d p)))
      (fst (V293_tick_wait_rows lo hi d p)) (snd (V293_tick_wait_rows lo hi d p))) **
    (V293_shared_fields current (set tasks (b,Int.repr base)
      (Int.repr (Z.of_nat p),V293_tick_wait_status reason d,message)) events now ** R))))))
    by (clear -Returned; sep auto).
  pose proof (V293_tick_wait_record_after_frame b base d reason pend p message next _
    _ _ _ _ _ _ _ Base Pr Pend Opened) as Combined.
  clear -Combined. sep auto.
Qed.
