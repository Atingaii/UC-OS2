(* Same-memory selection -> original target assignment -> switch precondition.
   The target cell is NOT promised as a private frame across a context switch. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_ready_named_target : forall ge le M ir aux O op target bo t,
  get ge target=Some (bo,Tptr V293_tcb_type) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr t) ->
  (ge,le,M,ir,aux,O,op) |= GV target @ (Tptr V293_tcb_type) |-> (Vptr t).
Proof.
  intros ge le M ir aux O op target bo t GE Cell.
  unfold V293_owned_record_cell in Cell. apply astar_l_apure_elim in Cell.
  destruct Cell as [_ [Mapsto Empty]]. exists bo.
  unfold Agvarmapsto,Aptrmapsto. apply sat_split'.
  exists (emp:mem). exists M. exists (emp:osabst). exists O.
  split; [apply map_join_comm;apply map_join_emp | ].
  split; [apply map_join_comm;apply map_join_emp | ]. split.
  - exists bo. repeat split;try reflexivity;exact GE.
  - split;assumption.
Qed.

Lemma V293_ready_named_target_frame : forall ge le M ir aux O op target bo t R,
  get ge target=Some (bo,Tptr V293_tcb_type) ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr t) ** R ->
  (ge,le,M,ir,aux,O,op) |= (GV target @ (Tptr V293_tcb_type) |-> (Vptr t)) ** R.
Proof.
  intros ge le M ir aux O op target bo t R GE Held. apply sat_split in Held.
  destruct Held as (m1&m2&o1&o2&JM&JO&Cell&Rest).
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split; [ | exact Rest].
  eapply V293_ready_named_target; [exact GE | exact Cell].
Qed.

(* This helper consumes the task-map assertion into AHprio. The only public
   execution theorem below obtains Sched from the owned bitmap/table relation. *)
Lemma V293_ready_target_pre : forall br bg bp current target bo next R ge le M ir aux O op,
  get ge target=Some (bo,Tptr V293_tcb_type) ->
  V293_scheduler O next ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R) ->
  (ge,le,M,ir,aux,O,op) |= SWPRE V293_scheduler target current.
Proof.
  intros br bg bp current target bo next R ge le M ir aux O op GE [ts [Map Highest]] Held.
  assert (Named : (ge,le,M,ir,aux,O,op) |=
    (GV target @ (Tptr V293_tcb_type) |-> (Vptr next)) **
    (SWINVt (V293_ready_inv br bg bp) current ** R)).
  { eapply V293_ready_named_target_frame; [exact GE | ]. sep auto. }
  clear Held.
  assert (Held : (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    ((GV target @ (Tptr V293_tcb_type) |-> (Vptr next)) ** R)) by (sep auto).
  clear Named.
  eapply astar_mono in Held; [ | apply V293_ready_switch_full | intros st H; exact H].
  unfold V293_ready_full in Held. sep normal in Held. sep destruct Held.
  assert (TaskMap : get O abstcblsid=Some (abstcblist x)).
  { eapply V293_star_abst_get_l with (s:=(ge,le,M,ir,aux,O,op)) (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue).
    - intros st H;rewrite <- (proj1 H);apply map_get_sig.
    - unfold V293_shared_fields in Held. sep auto. }
  assert (x=ts) by congruence. subst x.
  assert (Payload : (ge,le,M,ir,aux,O,op) |=
    Aabsdata abstcblsid (abstcblist ts) **
    ((GV target @ (Tptr V293_tcb_type) |-> (Vptr next)) **
      (isrclr ** ((EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr current)) ** Atrue)))).
  { unfold V293_shared_fields,V293_shared_flags in Held. sep auto. }
  eapply astar_mono in Payload; [ | apply V293_tasks_highest_spatial;exact Highest | ].
  2: { intros st H;exact H. }
  unfold SWPRE. exists next. clear Held. sep auto.
Qed.

Theorem V293_ready_dispatch_updates : forall br bg bp P ks ge le M ir aux O op current R
    unmap group rows high y table target bt bh byblock bo oldy oldhigh oldtarget,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  get le y=Some (byblock,Tint8) ->
  get le high=None -> get ge high=Some (bh,Tint8) ->
  get le table=None -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get le target=None -> get ge target=Some (bo,Tptr V293_tcb_type) ->
  byblock<>bt -> byblock<>bg -> byblock<>br -> byblock<>bh -> byblock<>bp -> bh<>bp ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,le,M,ir,aux,O,op) |=
    (V293_owned_record_cell ((byblock,0%Z),Tint8,oldy) **
     V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh)) **
    (SWINVt (V293_ready_inv br bg bp) current **
     (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)) ->
  exists tasks lo hi entries next message Mselected Mf,
    get O abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    get tasks next=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (V293_OSSchedNew_updates unmap group rows high y),
      (kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,le,M)
      (curs (sskip None),(kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,le,Mselected) /\
    (ge,le,Mselected,ir,aux,O,op) |=
      (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
       V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (SWINVt (V293_ready_inv br bg bp) current **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)) /\
    load Tint8 Mselected (bh,0%Z)=Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    cstepstar P
      (curs (sseq (V293_OSSchedNew_updates unmap group rows high y)
        (V293_OSSched_target_update table high target)),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    store (Tptr V293_tcb_type) Mselected (bo,0%Z) (Vptr next)=Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |=
      (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
       V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (SWINVt (V293_ready_inv br bg bp) current **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)) /\
    load (Tptr V293_tcb_type) Mf (bo,0%Z)=Some (Vptr next) /\
    V293_scheduler O next /\
    (ge,le,Mf,ir,aux,O,op) |= SWPRE V293_scheduler target current /\
    (indom tasks current -> (ge,le,Mf,ir,aux,O,op) |= SWPRE_NDEAD V293_scheduler target current) /\
    (~ indom tasks current -> (ge,le,Mf,ir,aux,O,op) |= SWPRE_DEAD V293_scheduler target current) /\
    (forall b i, (b,i)<>(byblock,0%Z) -> (b,i)<>(bh,0%Z) ->
      (b<>bo \/ (i<0)%Z \/ (4<=i)%Z) -> get Mf (b,i)=get M (b,i)).
Proof.
  intros br bg bp P ks ge le M ir aux O op current R unmap group rows high y table target
    bt bh byblock bo oldy oldhigh oldtarget Env Y HN HG TN TG ON OG YT YG YR YH YP HP Lookup Held.
  destruct (V293_ready_sched_updates br bg bp P (kseq (V293_OSSched_target_update table high target) ks)
    ge le M ir aux O op current
    (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)
    unmap group rows high y table bt bh byblock oldy oldhigh
    Env Y HN HG TN TG YT YG YR YH YP HP Lookup Held)
    as (tasks&lo&hi&entries&next&message&Mselected&Map&Rel&Task&Selection&Selected&High&Value&Ty&Sched&Frame).
  assert (Writable : (ge,le,Mselected,ir,aux,O,op) |=
    V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
    ((V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
      V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
     (SWINVt (V293_ready_inv br bg bp) current ** R))) by (sep auto).
  destruct (V293_owned_record_cell_update _ (Tptr V293_tcb_type) _ (Vptr next) _ _ _ _ _ _ _ _
    eq_refl Writable) as (Mf&Store&After).
  assert (Execution : cstepstar P
    (curs (sseq (V293_OSSchedNew_updates unmap group rows high y)
      (V293_OSSched_target_update table high target)),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf)).
  { eapply c_stepstarn. { eapply stmt_step; [reflexivity | constructor]. }
    eapply V293_cstepstar_trans; [exact Selection | ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | constructor]. }
    unfold V293_OSSched_target_update.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bo) (off:=0%Z);
      try eassumption.
    - cbn [evaltype]. rewrite ON,OG. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv get_genv]. rewrite ON,OG. reflexivity.
    - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
  assert (Ready : (ge,le,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** Atrue)) by (sep auto).
  pose proof (V293_ready_target_pre br bg bp current target bo next Atrue ge le Mf ir aux O op OG Sched Ready) as Pre.
  assert (Tasks : (ge,le,Mf,ir,aux,O,op) |= Aabsdata abstcblsid (abstcblist tasks) ** Atrue).
  { eapply astar_mono in Ready; [ | apply V293_ready_switch_full | intros st H;exact H].
    unfold V293_ready_full in Ready. sep normal in Ready. sep destruct Ready.
    assert (Map'' : get O abstcblsid=Some (abstcblist x)).
    { eapply V293_star_abst_get_l with (s:=(ge,le,Mf,ir,aux,O,op)) (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue); [intros st H;rewrite <- (proj1 H);apply map_get_sig | ].
      unfold V293_shared_fields in Ready. sep auto. }
    assert (x=tasks) by congruence. subst x. unfold V293_shared_fields in Ready. sep auto. }
  exists tasks. exists lo. exists hi. exists entries. exists next. exists message. exists Mselected. exists Mf.
  split; [exact Map | ]. split; [exact Rel | ]. split; [exact Task | ].
  split; [exact Selection | ]. split; [exact Selected | ]. split; [exact High | ].
  split; [exact Execution | ]. split; [exact Store | ]. split.
  - clear Held Selected Writable Ready Tasks Pre. sep auto.
  - split.
    + eapply V293_record_star_load_l with (s:=(ge,le,Mf,ir,aux,O,op)); [ | exact After].
      intros st H. eapply V293_owned_record_cell_load;exact H.
    + split; [exact Sched | ]. split; [exact Pre | ]. split.
      * intro Member. split; [exact Pre | ]. exists tasks. sep auto.
      * split.
        -- intro Dead. split; [exact Pre | ]. exists tasks. sep auto.
        -- intros b i NY NH Outside. rewrite <- Frame by assumption.
           eapply V293_storebytes_outside; [exact Store | destruct next as [nb ni];cbn [encode_val inj_pointer length];exact Outside].
Qed.
