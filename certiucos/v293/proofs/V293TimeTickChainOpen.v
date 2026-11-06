(* Open the SAME canonical full task map. Event pend is existential in the
   canonical record and must be read as a witness, not copied from a hint.
   Only genuinely absent Next / ready delay-pend / time pend are supplements. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCoreFocus.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReadyUpdate.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tick_choose_pend (binding:V293_tick_task*(taskstatus*val)) pend :=
  let '(t,(status,msg)):=binding in
  match status with
  | rdy | wait os_stat_time _ => binding
  | wait _ _ =>
      (Build_V293_tick_task (V293_tick_block t) (V293_tick_base t)
        (V293_tick_delay_value t) (V293_tick_stat_value t) pend
        (V293_tick_y t) (V293_tick_x t) (V293_tick_prio t),(status,msg))
  end.
Definition V293_tick_pend_choices := Forall2
  (fun before after=>exists (pend:nat),pend<256 /\ after=V293_tick_choose_pend before pend).
Definition V293_tick_node_missing (binding:V293_tick_task*(taskstatus*val)) next :=
  let t:=fst binding in
  ((V293_tick_block t,(V293_tick_base t+20)%Z),Tcom_ptr 410%Z,Vptr next)::
  match fst(snd binding) with
  | rdy => [((V293_tick_block t,(V293_tick_base t+44)%Z),Tint32,Vint32(Int.repr 0));
            ((V293_tick_block t,(V293_tick_base t+49)%Z),Tint8,V293_byteval(V293_tick_pend_value t))]
  | wait os_stat_time _ =>
      [((V293_tick_block t,(V293_tick_base t+49)%Z),Tint8,V293_byteval(V293_tick_pend_value t))]
  | wait _ _ => []
  end.
Fixpoint V293_tick_chain_missing (bindings:list(V293_tick_task*(taskstatus*val))) idle :=
  match bindings with
  | []=>[]
  | binding::rest=>V293_tick_node_missing binding(V293_tick_head(map fst rest)idle)++
      V293_tick_chain_missing rest idle
  end.

Lemma V293_tick_choose_pend_identity : forall binding pend,
  V293_tick_task_pointer(fst(V293_tick_choose_pend binding pend))=V293_tick_task_pointer(fst binding) /\
  V293_tick_binding_value false(V293_tick_choose_pend binding pend)=V293_tick_binding_value false binding /\
  V293_tick_binding_value true(V293_tick_choose_pend binding pend)=V293_tick_binding_value true binding /\
  fst(snd(V293_tick_choose_pend binding pend))=fst(snd binding).
Proof.
  intros [[b base d stat old y x p][status msg]] pend.
  destruct status as [ |reason delay];[ |destruct reason];repeat split;reflexivity.
Qed.
Lemma V293_tick_choose_pend_valid : forall binding pend,
  V293_tick_binding_valid binding -> pend<256 ->
  V293_tick_binding_valid(V293_tick_choose_pend binding pend).
Proof.
  intros [[b base d stat old y x p][status msg]] pend [Valid[P Shape]] Bound.
  destruct status as [ |reason delay];[exact(conj Valid(conj P Shape))| ].
  destruct reason;try exact(conj Valid(conj P Shape));
    (destruct Shape as [Shape Delay];cbn in Shape,Delay;inversion Shape;subst stat y x delay;
    split;[unfold V293_tick_task_valid in *;cbn in *;tauto|split;[exact P|split;reflexivity]]).
Qed.

Lemma V293_tick_pend_choices_properties : forall before after,
  V293_tick_pend_choices before after -> forall idle message,
  V293_tick_record_keys after idle=V293_tick_record_keys before idle /\
  V293_tick_head(map fst after)idle=V293_tick_head(map fst before)idle /\
  V293_tick_record_map false after idle message=V293_tick_record_map false before idle message /\
  V293_tick_record_map true after idle message=V293_tick_record_map true before idle message /\
  V293_tick_chain_code after=V293_tick_chain_code before /\
  (Forall V293_tick_binding_valid before -> Forall V293_tick_binding_valid after).
Proof.
  intros before after Choices;induction Choices as [ |b a bs aa [pend[Bound Same]] Tail IH];
    intros idle message;[repeat split;auto| ].
  subst a;destruct(V293_tick_choose_pend_identity b pend)as[Pointer[Old[New Status]]].
  destruct(IH idle message)as[Keys[Head[OldMap[NewMap[Code Valid]]]]].
  cbn [V293_tick_record_keys map V293_tick_record_map V293_tick_head app].
  rewrite Pointer,Old,New,OldMap,NewMap. repeat split;try reflexivity.
  - change(V293_tick_task_pointer(fst b)::V293_tick_record_keys aa idle=
      V293_tick_task_pointer(fst b)::V293_tick_record_keys bs idle);rewrite Keys;reflexivity.
  - cbn [V293_tick_chain_code]. rewrite Status,Code,Pointer;reflexivity.
  - intro All;inversion All;subst;constructor;[apply V293_tick_choose_pend_valid;assumption|apply Valid;assumption].
Qed.

Local Ltac open_permute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail => eapply Permutation_trans with(l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle|apply perm_skip;cbn [app];open_permute]
    | ?h::?tail => extract(before++[h])tail
    end
   in extract(@nil V293_record_cell)xs
 end.

Lemma V293_tick_before_layout_permutation : forall binding pend next,
  V293_tick_binding_valid binding ->
  Permutation
    (V293_record_layout(V293_tick_task_pointer(fst binding))(V293_tick_prio(fst binding))
      (fst(snd binding))(snd(snd binding))pend ++ V293_tick_node_missing binding next)
    (V293_tick_task_cells(fst(V293_tick_choose_pend binding pend))next ++
      V293_tick_binding_extra(V293_tick_choose_pend binding pend)).
Proof.
  intros [[b base d stat old y x p][status msg]] pend next [Valid[P Shape]].
  unfold V293_tick_task_valid in Valid;cbn in Valid.
  destruct Valid as([Base Limit]&D&Stat&Old&Y&X&Prio&Nonidle).
  assert(U:Int.unsigned(Int.repr base)=base)
    by(apply Int.unsigned_repr;change(0<=base<=4294967295)%Z;lia).
  destruct status as [ |reason delay].
  - cbn in Shape;inversion Shape;subst d stat y x.
    unfold V293_record_layout,V293_tick_task_pointer,V293_tick_node_missing,
      V293_tick_choose_pend,V293_tick_task_cells,V293_tick_binding_extra,V293_tick_record_extra.
    cbn;rewrite U;cbn;open_permute.
  - destruct Shape as[Shape Delay];cbn in Shape,Delay;inversion Shape;subst stat y x delay.
    destruct reason;unfold V293_record_layout,V293_tick_task_pointer,V293_tick_node_missing,
      V293_tick_choose_pend,V293_tick_task_cells,V293_tick_binding_extra,V293_tick_record_extra;
      cbn;rewrite U;cbn;open_permute.
Qed.

Lemma V293_tick_canonical_node_open : forall binding next R s,
  V293_tick_binding_valid binding ->
  s |= V293_owned_task_record(V293_tick_task_pointer(fst binding))
    (Int.repr(Z.of_nat(V293_tick_prio(fst binding))))(fst(snd binding))(snd(snd binding)) **
    (V293_owned_record_cells(V293_tick_node_missing binding next) ** R) ->
  exists (pend:nat),pend<256 /\
    s |= V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend binding pend))next) **
      (V293_owned_record_cells(V293_tick_binding_extra(V293_tick_choose_pend binding pend)) ** R).
Proof.
  intros binding next R s Valid Held.
  unfold V293_owned_task_record in Held.
  apply astar_l_aexists_elim in Held;destruct Held as[q Held].
  apply astar_l_aexists_elim in Held;destruct Held as[pend Held].
  assert(K:s |= [|q<13 /\ Int.repr(Z.of_nat(V293_tick_prio(fst binding)))=Int.repr(Z.of_nat q) /\ pend<256|] **
    (V293_owned_record_cells(V293_record_layout(V293_tick_task_pointer(fst binding))q
      (fst(snd binding))(snd(snd binding))pend) **
      (V293_owned_record_cells(V293_tick_node_missing binding next) ** R)))by(clear -Held;sep auto).
  clear Held;rename K into Held.
  apply astar_l_apure_elim in Held;destruct Held as[[Q[Priority Bound]]Held].
  assert(P:V293_tick_prio(fst binding)<13)by(destruct binding as[t[status msg]];exact(proj1(proj2 Valid))).
  assert(E:V293_tick_prio(fst binding)=q)by(eapply V293_tick_wait_priority_unique;eassumption).
  subst q;exists pend;split;[exact Bound| ].
  assert(Joined:s |= V293_owned_record_cells
    (V293_record_layout(V293_tick_task_pointer(fst binding))(V293_tick_prio(fst binding))
      (fst(snd binding))(snd(snd binding))pend ++ V293_tick_node_missing binding next) ** R).
  { eapply astar_mono;[ |intros st H;exact H| ];[intros st H;apply V293_tick_cells_append;exact H| ].
    clear -Held;sep auto. }
  eapply astar_mono in Joined;[ |apply V293_owned_cells_permutation;apply V293_tick_before_layout_permutation;exact Valid|intros st H;exact H].
  assert(Split:s |= (V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend binding pend))next) **
      V293_owned_record_cells(V293_tick_binding_extra(V293_tick_choose_pend binding pend))) ** R).
  { eapply astar_mono;[ |intros st H;exact H|exact Joined].
    intros st H;apply V293_tick_cells_append;exact H. }
  clear -Split;sep auto.
Qed.

Lemma V293_tick_canonical_cons_open : forall tasks t p status message R s,
  get tasks t=None ->
  s |= V293_owned_task_records(set tasks t (p,status,message)) ** R ->
  s |= V293_owned_task_record t p status message ** (V293_owned_task_records tasks ** R).
Proof.
  intros tasks t p status message R s Missing Held.
  pose proof(V293_task_update_enumeration tasks t (p,status,message))as Order.
  rewrite V293_tick_delete_absent in Order by exact Missing.
  apply Permutation_sym in Order.
  assert(Opened:s |= V293_owned_task_list((t,(p,status,message))::TcbMod.lst tasks) ** R).
  { eapply V293_owned_task_list_permutation;[exact Order|exact Held]. }
  cbn [V293_owned_task_list] in Opened. clear -Opened;sep auto.
Qed.

Lemma V293_tick_canonical_idle_open : forall idle message R s,
  s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R ->
  s |= V293_owned_record_cell(V293_tick_idle_cell idle) **
    (V293_owned_record_cells(V293_tick_idle_extra idle message) ** R).
Proof.
  intros idle message R s Held. unfold V293_owned_task_record in Held.
  apply astar_l_aexists_elim in Held;destruct Held as[q Held].
  apply astar_l_aexists_elim in Held;destruct Held as[pend Held].
  assert(K:s |= [|q<13 /\ Int.repr 12=Int.repr(Z.of_nat q) /\ pend<256|] **
    (V293_owned_record_cells(V293_record_layout idle q rdy message pend) ** R))by(clear -Held;sep auto).
  apply astar_l_apure_elim in K;destruct K as[[Q[Priority Bound]]Cells].
  assert(E:12=q)by(eapply V293_tick_wait_priority_unique;[lia|exact Q|exact Priority]).
  subst q. unfold V293_tick_idle_cell,V293_tick_idle_extra,V293_record_layout in *.
  cbn [tl app V293_owned_record_cells] in *. clear -Cells;sep auto.
Qed.

Theorem V293_tick_canonical_chain_open : forall bindings idle message R s,
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  s |= V293_owned_task_records(V293_tick_record_map false bindings idle message) **
    (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** R) ->
  exists actual,
    V293_tick_pend_choices bindings actual /\
    s |= V293_owned_record_cells(V293_tick_chain_cells(map fst actual)idle) **
      (V293_owned_record_cells(concat(map V293_tick_binding_extra actual)) **
      (V293_owned_record_cell(V293_tick_idle_cell idle) **
      (V293_owned_record_cells(V293_tick_idle_extra idle message) ** R))).
Proof.
  induction bindings as [ |[t[status msg]] rest IH];intros idle message R s Valid Unique Held.
  - exists (@nil(V293_tick_task*(taskstatus*val)));split;[constructor| ].
    cbn [V293_tick_record_map V293_tick_chain_missing V293_owned_record_cells] in Held.
    unfold V293_owned_task_records in Held.
    change(s |= (V293_owned_task_record idle (Int.repr 12) rdy message ** Aemp) ** (Aemp ** R))in Held.
    assert(Entry:s |= V293_owned_task_record idle (Int.repr 12) rdy message ** R)by(clear -Held;sep auto).
    pose proof(V293_tick_canonical_idle_open _ _ _ _ Entry)as Idle.
    cbn [map concat V293_tick_chain_cells V293_owned_record_cells]. clear -Idle;sep auto.
  - inversion Valid as[ |head tail HeadValid TailValid];subst head tail.
    change(NoDup(V293_tick_task_pointer t::V293_tick_record_keys rest idle))in Unique.
    inversion Unique as[ |key keys Fresh TailUnique];subst key keys.
    assert(Absent:get(V293_tick_record_map false rest idle message)(V293_tick_task_pointer t)=None)
      by(apply V293_tick_record_map_absent;exact Fresh).
    cbn [V293_tick_record_map V293_tick_chain_missing] in Held.
    assert(Split:s |= V293_owned_task_records
      (set(V293_tick_record_map false rest idle message)(V293_tick_task_pointer t)
        (Int.repr(Z.of_nat(V293_tick_prio t)),status,msg)) **
      ((V293_owned_record_cells(V293_tick_node_missing(t,(status,msg))(V293_tick_head(map fst rest)idle)) **
        V293_owned_record_cells(V293_tick_chain_missing rest idle)) ** R)).
    { eapply astar_mono;[intros st H;exact H| |exact Held].
      intros st H;eapply astar_mono;[ |intros st0 H0;exact H0|exact H].
      intros st0 H0;apply V293_tick_cells_append;exact H0. }
    pose proof(V293_tick_canonical_cons_open _ _ _ _ _ _ _ Absent Split)as Cons.
    assert(NodeEntry:s |= V293_owned_task_record(V293_tick_task_pointer t)
        (Int.repr(Z.of_nat(V293_tick_prio t)))status msg **
      (V293_owned_record_cells(V293_tick_node_missing(t,(status,msg))(V293_tick_head(map fst rest)idle)) **
      (V293_owned_task_records(V293_tick_record_map false rest idle message) **
      (V293_owned_record_cells(V293_tick_chain_missing rest idle) ** R))))by(clear -Cons;sep auto).
    destruct(V293_tick_canonical_node_open _ _ _ _ HeadValid NodeEntry)as[pend[Bound Node]].
    assert(TailEntry:s |= V293_owned_task_records(V293_tick_record_map false rest idle message) **
      (V293_owned_record_cells(V293_tick_chain_missing rest idle) **
      (V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend(t,(status,msg))pend))
        (V293_tick_head(map fst rest)idle)) **
      (V293_owned_record_cells(V293_tick_binding_extra(V293_tick_choose_pend(t,(status,msg))pend)) ** R))))
      by(clear -Node;sep auto).
    destruct(IH _ _ _ _ TailValid TailUnique TailEntry)as[actual[Choices Opened]].
    exists(V293_tick_choose_pend(t,(status,msg))pend::actual);split.
    + constructor;[exists pend;auto|exact Choices].
    + destruct(V293_tick_pend_choices_properties _ _ Choices idle message)as[Keys[Head Props]].
      rewrite <-Head in Opened.
      cbn [map concat V293_tick_chain_cells].
      apply astar_mono with
        (P:=V293_owned_record_cells(V293_tick_task_cells(fst(V293_tick_choose_pend(t,(status,msg))pend))
          (V293_tick_head(map fst actual)idle)) **
          V293_owned_record_cells(V293_tick_chain_cells(map fst actual)idle))
        (Q:=(V293_owned_record_cells(V293_tick_binding_extra(V293_tick_choose_pend(t,(status,msg))pend)) **
          V293_owned_record_cells(concat(map V293_tick_binding_extra actual))) **
          (V293_owned_record_cell(V293_tick_idle_cell idle) **
          (V293_owned_record_cells(V293_tick_idle_extra idle message) ** R))).
      * intros st H;apply V293_tick_cells_append;exact H.
      * intros st H;eapply astar_mono;[ |intros st0 H0;exact H0|exact H].
        intros st0 H0;apply V293_tick_cells_append;exact H0.
      * clear -Opened;sep auto.
Qed.

Section CanonicalCore.
Variables (bindings:list(V293_tick_task*(taskstatus*val))) (idle:addrval) (message:val)
  (ct:tid) (es:EcbMod.map) (n:int32) (br bg bp bn bc:block) (frame:asrt).
Let tasks:=V293_tick_record_map false bindings idle message.

Definition V293_tick_chain_core_pre :=
  ((CurTid ct ** V293_shared_fields ct tasks es n) ** V293_ready_payload br bg bp tasks) **
  (PV(bn,Int.zero)@Tint32|->Vint32 n **
  (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst bindings)idle)) **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** frame))).

Lemma V293_tick_chain_core_fold : V293_tick_chain_core_pre ==>
  V293_time_ready_core br bg bp bn **
  (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst bindings)idle)) **
  (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** frame)).
Proof.
  unfold V293_tick_chain_core_pre,V293_time_ready_core,V293_time_ready_fields.
  intros s H;clear -H;sep auto.
Qed.

Lemma V293_tick_chain_core_open :
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  V293_tick_chain_core_pre ==>
  EX actual:list(V293_tick_task*(taskstatus*val)), EX lo:nat, EX hi:nat, EX entries:list val,
    [|V293_tick_pend_choices bindings actual /\
      V293_ready_rel lo hi entries(V293_tick_record_map false actual idle message)|] **
    V293_tick_while_core_pre actual idle message ct es n br bg bp bn bc frame lo hi entries.
Proof.
  intros Valid Unique s Held.
  unfold V293_tick_chain_core_pre,V293_ready_payload in Held.
  set(other:=(CurTid ct ** V293_shared_fields ct tasks es n) **
    (PV(bn,Int.zero)@Tint32|->Vint32 n **
    (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst bindings)idle)) ** frame))).
  assert(Ready:s |= V293_ready_owned br bg bp tasks **
    (V293_owned_task_records tasks ** (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** other)))
    by(unfold other;clear -Held;sep auto).
  unfold V293_ready_owned in Ready.
  apply astar_l_aexists_elim in Ready;destruct Ready as[lo Ready].
  apply astar_l_aexists_elim in Ready;destruct Ready as[hi Ready].
  apply astar_l_aexists_elim in Ready;destruct Ready as[entries Ready].
  assert(K:s |= [|V293_ready_rel lo hi entries tasks|] **
    (V293_owned_record_cells(V293_ready_cells br bg bp lo hi entries) **
    (V293_owned_task_records tasks ** (V293_owned_record_cells(V293_tick_chain_missing bindings idle) ** other))))
    by(clear -Ready;sep auto).
  apply astar_l_apure_elim in K;destruct K as[Rel K].
  assert(Entry:s |= V293_owned_task_records tasks **
    (V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
    (V293_owned_record_cells(V293_ready_cells br bg bp lo hi entries) ** other)))by(clear -K;sep auto).
  destruct(V293_tick_canonical_chain_open _ _ _ _ _ Valid Unique Entry)as[actual[Choices Opened]].
  destruct(V293_tick_pend_choices_properties _ _ Choices idle message)as[Keys[Head[OldMap Props]]].
  exists actual. exists lo. exists hi. exists entries.
  apply astar_l_apure_intro;[ |split;[exact Choices|rewrite OldMap;exact Rel]].
  unfold V293_tick_while_core_pre. apply V293_tick_owned_to_raw.
  unfold other in Opened. unfold tasks in Opened. rewrite <-OldMap,<-Head in Opened.
  set(remainder:=V293_tick_while_core_remainder actual idle message ct es n bp bn frame
    (V293_tick_record_map false actual idle message)entries).
  assert(Spatial:s |= V293_owned_record_cells(V293_tick_chain_cells(map fst actual)idle) **
    (V293_owned_record_cells(V293_tick_bitmap_cells bg br(V293_ready_group lo hi)lo hi) **
    (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst actual)idle)) **
    (V293_owned_record_cell(V293_tick_idle_cell idle) ** remainder)))).
  { unfold remainder,V293_tick_while_core_remainder,V293_ready_cells,V293_tick_bitmap_cells in *.
    cbn [app V293_owned_record_cells] in Opened |- *. clear -Opened;sep auto. }
  assert(Tail:s |= V293_owned_record_cells
    (V293_tick_chain_cells(map fst actual)idle ++
      (V293_tick_bitmap_cells bg br(V293_ready_group lo hi)lo hi ++[V293_tick_idle_cell idle])) **
    (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst actual)idle)) ** remainder)).
  { eapply astar_mono;[intros st H;apply V293_tick_cells_append;exact H|intros st H;exact H| ].
    assert(Split:s |= V293_owned_record_cells(V293_tick_chain_cells(map fst actual)idle) **
      (V293_owned_record_cells(V293_tick_bitmap_cells bg br(V293_ready_group lo hi)lo hi ++
        [V293_tick_idle_cell idle]) **
      (V293_owned_record_cell(V293_tick_pointer_cell bc(V293_tick_head(map fst actual)idle)) ** remainder))).
    { unfold V293_ready_cells,V293_tick_bitmap_cells in *.
      cbn [app V293_owned_record_cells] in *.
      unfold remainder,V293_tick_while_core_remainder in Spatial |- *. clear -Spatial;sep auto. }
    clear -Split;sep auto. }
  unfold V293_tick_while_cells. cbn [app V293_owned_record_cells].
  unfold remainder in Tail. clear -Tail;sep auto.
Qed.

Theorem V293_tick_chain_core_hoare : forall Spec sd li I r ri tid
  ptcb rows group enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  (forall st,st |= frame -> V293_tick_delay_env ptcb rows group bc br bg(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  InfRules Spec sd li I r ri
    (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_tick_chain_core_pre)
    (swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))
    (EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,enabled,si,ci] **
        V293_tick_while_core_post actual idle br bg bp bn bc frame) **
      [|V293_tick_pend_choices bindings actual|])tid.
Proof.
  intros Spec sd li I r ri tid ptcb rows group enabled ir si ci
    NA IdleLimit Valid Unique Env Inv GF Free Bound.
  eapply conseq_rule with
    (p:=EX actual:list(V293_tick_task*(taskstatus*val)), EX lo:nat, EX hi:nat, EX entries:list val,
      (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] **
        V293_tick_while_core_pre actual idle message ct es n br bg bp bn bc frame lo hi entries) **
      [|V293_tick_pend_choices bindings actual /\
        V293_ready_rel lo hi entries(V293_tick_record_map false actual idle message)|]).
  - intros s H.
    assert(K:s |= <||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] **
      (EX actual:list(V293_tick_task*(taskstatus*val)), EX lo:nat, EX hi:nat, EX entries:list val,
      [|V293_tick_pend_choices bindings actual /\
        V293_ready_rel lo hi entries(V293_tick_record_map false actual idle message)|] **
      V293_tick_while_core_pre actual idle message ct es n br bg bp bn bc frame lo hi entries)).
    { eapply astar_mono;[intros st Hs;exact Hs| |exact H].
      apply astar_mono;[intros st Hs;exact Hs|apply V293_tick_chain_core_open;assumption]. }
    clear -K;sep auto.
  - intros s H;exact H.
  - apply ex_intro_rule;intro actual. apply ex_intro_rule;intro lo.
    apply ex_intro_rule;intro hi. apply ex_intro_rule;intro entries.
    apply pure_split_rule;intros[Choices Rel].
    destruct(V293_tick_pend_choices_properties _ _ Choices idle message)as[Keys[Head[OldMap[NewMap[Code All]]]]].
    rewrite <-Code.
    eapply conseq_rule with(q:=<||END None||> ** OS[ir,enabled,si,ci] **
      V293_tick_while_core_post actual idle br bg bp bn bc frame).
    + intros s H;exact H.
    + intros s H;exists actual. clear -H Choices;sep auto.
    + apply V293_tick_while_core_hoare with(lo:=lo)(hi:=hi)(entries:=entries).
      * exact NA.
      * exact IdleLimit.
      * apply All;exact Valid.
      * rewrite Keys;exact Unique.
      * exact Rel.
      * exact Env.
      * exact Inv.
      * exact GF.
      * exact Free.
      * exact Bound.
Qed.

Theorem V293_tick_chain_core_semantics : forall Spec sd li I r ri tid
  ptcb rows group enabled ir si ci,
  NoAbs li -> (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_binding_valid bindings -> NoDup(V293_tick_record_keys bindings idle) ->
  (forall st,st |= frame -> V293_tick_delay_env ptcb rows group bc br bg(getgenv st)(getlenv st)) ->
  ((CurTid ct ** frame) ==> CurLINV li tid) -> GoodFrm frame -> can_change_aop frame ->
  (gettopis si<=INUM)%nat ->
  simulation.RuleSem Spec sd li I r ri
    (<||V293_tick_chain_code bindings||> ** OS[ir,enabled,si,ci] ** V293_tick_chain_core_pre)
    (swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))
    (EX actual:list(V293_tick_task*(taskstatus*val)),
      (<||END None||> ** OS[ir,enabled,si,ci] **
        V293_tick_while_core_post actual idle br bg bp bn bc frame) **
      [|V293_tick_pend_choices bindings actual|])tid.
Proof. intros;apply RuleSound;apply V293_tick_chain_core_hoare;assumption. Qed.
End CanonicalCore.
