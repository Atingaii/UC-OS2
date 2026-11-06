(* Same-memory startup bridge for a real initialized TCB. Seven selected
   fields move into task-record ownership; the other eleven remain separate.
   No port execution, full TCB/global invariant, or OSInit reachability claim. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSStart.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293Start.
Require Import CertiOS.certiucos.v293.proofs.V293StartCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_raw_record_ownership : forall cells R,
  Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true) cells ->
  V293_rdy_raw_cells cells R ==> V293_owned_record_cells cells ** R.
Proof.
  intros cells R Valid. induction Valid as [ | [[a tp] v] cells Head Tail IH];intros s Owned.
  - cbn [V293_rdy_raw_cells V293_owned_record_cells] in *. clear -Owned. sep auto.
  - cbn [V293_rdy_raw_cells V293_owned_record_cells] in *.
    assert (Typed : s |= V293_owned_record_cell (a,tp,v) **
      (V293_owned_record_cells cells ** R)).
    { eapply astar_mono;[ | exact IH | exact Owned].
      intros st HS. unfold V293_owned_record_cell. apply astar_l_apure_intro;assumption. }
    clear -Typed. sep auto.
Qed.

Definition V293_tcb_init_record_remainder bt base top bottom identity size ext options
    : list V293_record_cell :=
  [((bt,(base+0)%Z),Tptr Tint32,top);
   ((bt,(base+49)%Z),Tint8,Vint32 Int.zero);
   ((bt,(base+44)%Z),Tint32,Vint32 Int.zero);
   ((bt,(base+4)%Z),Tptr Tvoid,ext);
   ((bt,(base+12)%Z),Tint32,size);
   ((bt,(base+8)%Z),Tptr Tint32,bottom);
   ((bt,(base+16)%Z),Tint16,options);
   ((bt,(base+18)%Z),Tint16,identity);
   ((bt,(base+55)%Z),Tint8,Vint32 Int.zero);
   ((bt,(base+28)%Z),Tcom_ptr 411%Z,Vnull);
   ((bt,(base+36)%Z),Tcom_ptr 412%Z,Vnull)].

Lemma V293_initialized_ready_record : forall bt base p top bottom identity size ext options R,
  p<13 -> (0<=base<=Int.max_unsigned)%Z ->
  V293_tcb_init_values_valid top bottom identity size ext options ->
  V293_rdy_raw_cells (V293_tcb_init_final_fields bt base p top bottom identity size ext options) R ==>
  V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat p)) rdy Vnull **
    V293_rdy_raw_cells (V293_tcb_init_record_remainder bt base top bottom identity size ext options) R.
Proof.
  intros bt base p top bottom identity size ext options R Range Bound Valid s Owned.
  set (rest:=V293_rdy_raw_cells
    (V293_tcb_init_record_remainder bt base top bottom identity size ext options) R).
  assert (Reordered : s |= V293_rdy_raw_cells
    (V293_record_layout (bt,Int.repr base) p rdy Vnull 0) rest).
  { unfold V293_record_layout. cbn [fst snd]. rewrite Int.unsigned_repr by exact Bound.
    unfold rest,V293_tcb_init_record_remainder,V293_tcb_init_final_fields in *.
    cbn [V293_rdy_raw_cells app] in *. change (V293_byteval 0) with (Vint32 Int.zero).
    clear -Owned. sep auto. }
  assert (Types : Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true)
      (V293_record_layout (bt,Int.repr base) p rdy Vnull 0)).
  { pose proof (V293_tcb_init_final_valid bt base p top bottom identity size ext options Range Valid) as All.
    rewrite Forall_forall in All |- *. intros [[a tp] v] Member.
    apply (All (a,tp,v)). unfold V293_record_layout in Member. cbn [fst snd] in Member.
    rewrite Int.unsigned_repr in Member by exact Bound.
    unfold V293_tcb_init_final_fields. cbn [In app] in *;tauto. }
  apply (V293_raw_record_ownership _ _ Types) in Reordered.
  eapply astar_mono;[ | intros st HS;exact HS | exact Reordered].
  intros st HS. exists p. exists 0. apply astar_l_apure_intro;[exact HS | repeat split;try reflexivity;lia].
Qed.

(* The abstract lookup is publication evidence, not an abstract-current update.
   The concrete priority and all six other record fields come from initialized
   bytes retained through the actual call, not from that lookup. *)
Theorem V293_OSStart_initialized_task : forall entries tasks frame P ks ge caller M ir aux O op
  startfn running sched prio high table top port unmap group rows y
  brun bc bh bp bt bu bm bg br lo hi hv cv tv uv tcb base p
  stack bottom identity size ext options,
  P startfn=Some (V293_OSStart_function running sched prio high table top OSTCBCur port) ->
  P sched=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bm,Tarray Tint8 256) -> get ge group=Some (bg,Tint8) ->
  get ge rows=Some (br,Tarray Tint8 2) -> get ge high=Some (bh,Tint8) ->
  get ge running=Some (brun,Tint8) -> get ge prio=Some (bc,Tint8) ->
  get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get ge top=Some (bt,Tptr V293_tcb_type) -> get ge OSTCBCur=Some (bu,Tptr V293_tcb_type) ->
  lo<256 -> hi<256 -> (exists q,V293_bitmap_ready lo hi q) ->
  p=V293_ready_select lo hi (V293_ready_group lo hi) ->
  (0<=base<=Int.max_unsigned)%Z ->
  V293_tcb_init_values_valid stack bottom identity size ext options ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  nth p entries Vnull=Vptr (tcb,Int.repr base) ->
  get tasks (tcb,Int.repr base)=Some (Int.repr (Z.of_nat p),rdy,Vnull) ->
  get O abstcblsid=Some (abstcblist tasks) ->
  V293_sched_read_memory M bm bg br lo hi (V293_ready_group lo hi) ->
  (ge,emp,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_start_cells bh bc bt bu brun bp p hv cv tv uv (Vint32 Int.zero)
      (Vptr (tcb,Int.repr base))
      (V293_tcb_init_final_fields tcb base p stack bottom identity size ext options++frame)) Atrue ->
  exists Mf,
    get tasks (tcb,Int.repr base)=Some (Int.repr (Z.of_nat p),rdy,Vnull) /\
    V293_scheduler O (tcb,Int.repr base) /\
    cstepstar P (curs (scall startfn nil),(kenil,ks)) (ge,caller,M)
      (curs (sfexec port nil nil),(kenil,kseq sret (kcall startfn
        (V293_OSStart_body running sched prio high table top OSTCBCur port) caller ks))) (ge,emp,Mf) /\
    (ge,emp,Mf,ir,aux,O,op) |=
      CurTid (tcb,Int.repr base) ** CurTid (tcb,Int.repr base) **
      V293_owned_task_record (tcb,Int.repr base) (Int.repr (Z.of_nat p)) rdy Vnull **
      V293_rdy_raw_cells (V293_tcb_init_record_remainder tcb base stack bottom identity size ext options)
        (V293_rdy_raw_cells (V293_start_other_cells bh bc bt brun bp p (tcb,Int.repr base) frame) Atrue).
Proof.
  intros entries tasks frame P ks ge caller M ir aux O op startfn running sched prio high table top port
    unmap group rows y brun bc bh bp bt bu bm bg br lo hi hv cv tv uv tcb base p
    stack bottom identity size ext options Program Scheduler Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu
    Lo Hi Nonempty Priority Bound Valid Bitmap Table Entry Member Abstract Reads Owned.
  subst p.
  pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Lo Hi eq_refl Nonempty) as Range.
  destruct (V293_ready_selection_task lo hi entries tasks Lo Hi Nonempty Bitmap Table)
    as (target&message&Found&Selected&Highest).
  rewrite Entry in Selected. inversion Selected;subst target.
  assert (Decision : V293_scheduler O (tcb,Int.repr base)).
  { exists tasks. split;assumption. }
  destruct (V293_OSStart_call_establishes_current
    (V293_tcb_init_final_fields tcb base (V293_ready_select lo hi (V293_ready_group lo hi))
      stack bottom identity size ext options++frame)
    P ks ge caller M ir aux O op startfn running sched prio high table top port unmap group rows y
    brun bc bh bp bt bu bm bg br lo hi hv cv tv uv (tcb,Int.repr base)
    Program Scheduler Nu Ng Nr Nh Gm Gg Gr Gh Grun Gc Gp Gt Gu Lo Hi Nonempty Reads Owned)
    as (Mf&Exec&Final).
  exists Mf. split;[exact Member | ]. split;[exact Decision | ]. split;[exact Exec | ].
  assert (Grouped : (ge,emp,Mf,ir,aux,O,op) |=
    CurTid (tcb,Int.repr base) ** CurTid (tcb,Int.repr base) **
    V293_rdy_raw_cells
      (V293_tcb_init_final_fields tcb base (V293_ready_select lo hi (V293_ready_group lo hi))
        stack bottom identity size ext options)
      (V293_rdy_raw_cells
        (V293_start_other_cells bh bc bt brun bp
          (V293_ready_select lo hi (V293_ready_group lo hi)) (tcb,Int.repr base) frame) Atrue)).
  { unfold V293_start_other_cells,V293_tcb_init_final_fields in *.
    cbn [V293_rdy_raw_cells app] in *. clear -Final. sep auto. }
  eapply astar_mono;[intros st HS;exact HS | | exact Grouped].
  eapply astar_mono;[intros st HS;exact HS | ].
  apply V293_initialized_ready_record;assumption.
Qed.
Print Assumptions V293_initialized_ready_record.
Print Assumptions V293_OSStart_initialized_task.
