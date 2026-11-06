(* Real no-argument OS_SchedNew call with its existential fresh byte local.
   Ready invariant and caller resources survive allocation and release.
   Uninterleaved source semantics; not WFIFun or a complete OS_Sched. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_ready_fresh_avoiding : forall M forbidden,
  exists b, fresh M b /\ ~ In b forbidden.
Proof.
  intros M forbidden. destruct (HalfPermMap.bounded M) as [upper Bound].
  set (limit:=fold_right Pos.max upper forbidden).
  assert (Upper : (upper<=limit)%positive).
  { unfold limit. induction forbidden as [ | x xs IH];cbn.
    - apply Pos.le_refl.
    - eapply Pos.le_trans;[exact IH | apply Pos.le_max_r]. }
  assert (All : forall x, In x forbidden -> (x<=limit)%positive).
  { clear Upper. unfold limit. induction forbidden as [ | x xs IH];intros c Member;cbn in *;
      [contradiction | destruct Member as [E | H]].
    - subst. apply Pos.le_max_l.
    - eapply Pos.le_trans;[apply IH;exact H | apply Pos.le_max_r]. }
  exists (Pos.succ limit). split.
  - intros a i E [v Read];subst a.
    pose proof (Bound _ _ _ Read). lia.
  - intro Member. specialize (All _ Member). lia.
Qed.

Lemma V293_ready_lenv_frame : forall br bg bp current R ge le M ir aux O op le',
  GoodInvAsrt R ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current ** R ->
  (ge,le',M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current ** R.
Proof.
  intros br bg bp current R ge le M ir [[ie si] cs] O op le' Good Held.
  eapply astar_mono in Held; [ | apply V293_ready_switch_full | intros st H;exact H].
  apply sat_split in Held. destruct Held as (m1&m2&o1&o2&JM&JO&Open&Rest).
  apply sat_split in Open. destruct Open as (mf&mc&oflags&oc&JMC&JOC&Flags&Core).
  assert (GCore : GoodInvAsrt (V293_ready_full br bg bp current)).
  { change (forall tasks events now, GoodInvAsrt
      ((EX tp : type, GV OSTCBCur @ (Tptr tp) |-> (Vptr current)) **
       (V293_shared_fields current tasks events now ** V293_ready_payload br bg bp tasks))).
    intros. split; [ | split; [ | apply V293_ready_payload_good]].
    - unfold Agvarmapsto,Aptrmapsto. cbn. intros. repeat split;exact I.
    - unfold V293_shared_fields. cbn. repeat split;exact I. }
  apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split;[exact JM | ]. split;[exact JO | ]. split.
  - apply V293_ready_switch_halves. apply sat_split'.
    exists mf. exists mc. exists oflags. exists oc.
    split;[exact JMC | ]. split;[exact JOC | ]. split;[exact Flags | ].
    eapply good_inv_prop;[exact GCore | exact Core].
  - eapply good_inv_prop;[exact Good | exact Rest].
Qed.

Lemma V293_ready_release_byte : forall ge le M ir aux O op b v R,
  (ge,le,M,ir,aux,O,op) |= Amapsto (b,0%Z) Tint8 true v ** R ->
  exists Mf, free Tint8 b M=Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |= R /\
    get Mf (b,0%Z)=None /\
    (forall c i, c<>b -> get Mf (c,i)=get M (c,i)).
Proof.
  intros ge le M ir aux O op b v R Held.
  apply sat_split in Held. destruct Held as (local&rest&ol&orest&JM&JO&[Slot Empty]&Rest).
  change (ol=emp) in Empty. subst ol. apply map_join_comm in JO. apply map_join_emp' in JO. subst orest.
  destruct Slot as (bytes&Encoding&Points).
  assert (Free : free Tint8 b M=Some rest).
  { unfold free. rewrite <- (encode_val_length Tint8 v),Encoding.
    apply free_locality2' with (M1:=local);assumption. }
  exists rest. split;[exact Free | ]. split;[exact Rest | ]. split.
  - change (get rest (b,(0+Z.of_nat 0)%Z)=None).
    eapply V293_freeb_removed;[exact Free | cbn;lia].
  - intros. eapply V293_freeb_outside;[exact Free | left;exact H].
Qed.

(* A fresh local is raw Vundef, not a typed initialized record. The first
   original assignment establishes the byte value; no extra store is inserted. *)
Lemma V293_ready_sched_raw_updates : forall br bg bp P ks ge le M ir aux O op current R
    unmap group rows high y table bt bh byblock oldy oldhigh,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  get le y=Some (byblock,Tint8) ->
  get le high=None -> get ge high=Some (bh,Tint8) ->
  get le table=None -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  byblock<>bt -> byblock<>bg -> byblock<>br -> byblock<>bh ->
  byblock<>bp -> bh<>bp ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,le,M,ir,aux,O,op) |=
    (Amapsto (byblock,0%Z) Tint8 true oldy **
     V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh)) **
    (SWINVt (V293_ready_inv br bg bp) current ** R) ->
  exists tasks lo hi entries t message Mf,
    get O abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    get tasks t=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (V293_OSSchedNew_updates unmap group rows high y),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |=
      (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
       V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
      (SWINVt (V293_ready_inv br bg bp) current ** R) /\
    load Tint8 Mf (bh,0%Z)=Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    evalval (V293_OSSched_target_expr table high) (ge,le,Mf)=Some (Vptr t) /\
    evaltype (V293_OSSched_target_expr table high) (ge,le,Mf)=Some (Tptr V293_tcb_type) /\
    load (Tptr V293_tcb_type) Mf (bp,(4*Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))))%Z=Some (Vptr t) /\
    V293_scheduler O t /\
    (forall a, a<>(byblock,0%Z) -> a<>(bh,0%Z) -> get Mf a=get M a).
Proof.
  intros br bg bp P ks ge le M ir aux O op current R unmap group rows high y table bt bh byblock oldy oldhigh
    Env Y HN HG TN TG YT YG YR YH YP HP Lookup Held.
  assert (InvHeld : (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current ** Atrue) by (sep auto).
  destruct (V293_ready_switch_selected br bg bp _ _ _ InvHeld)
    as (tasks&lo&hi&entries&t&message&TaskMap&Rel&Loads&Task&Pointer&Sched).
  destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
  set (g:=V293_ready_group lo hi). set (selected:=V293_ready_select lo hi g).
  assert (GB : g<256).
  { unfold g,V293_ready_group. destruct (lo=?0); destruct (hi=?0); lia. }
  assert (YB : V293_ready_lookup g<256).
  { pose proof (proj1 (V293_ready_row_spec g GB)). lia. }
  assert (SB : selected<13).
  { unfold selected,g. apply V293_ready_selection_range; assumption || reflexivity. }
  assert (First : (ge,le,M,ir,aux,O,op) |=
    Amapsto (byblock,0%Z) Tint8 true oldy **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) ** (SWINVt (V293_ready_inv br bg bp) current ** R))) by (apply astar_assoc_elim; exact Held).
  pose proof (V293_tick_raw_owned_writable byblock Tint8 oldy _ _ _ _ _ _ _ _ First) as WritableY.
  destruct (WritableY 0 ltac:(cbn;lia)) as [vy WY].
  change (get M (byblock,0%Z)=Some (true,vy)) in WY.
  destruct (V293_tick_raw_slot_update (byblock,0%Z) Tint8 oldy
    (V293_byteval (V293_ready_lookup g)) _ _ _ _ _ _ _ _
    (V293_byte_type _ YB) First) as (M1&StoreY&UpdatedY).
  pose proof (V293_write_byte_store M byblock (V293_ready_lookup g) vy WY) as StoreY'.
  assert (M1=V293_write_byte M byblock (V293_ready_lookup g)) by congruence.
  subst M1. set (M1:=V293_write_byte M byblock (V293_ready_lookup g)) in *.
  assert (Second : (ge,le,M1,ir,aux,O,op) |=
    V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) **
    (V293_owned_record_cell ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup g)) **
      (SWINVt (V293_ready_inv br bg bp) current ** R))) by (clear First Held InvHeld; sep auto).
  destruct (V293_owned_byte_update _ _ selected _ _ _ _ _ _ _ _ ltac:(lia) Second) as [WH UpdatedH].
  replace (V293_put_byte M1 (bh,0%Z) selected) with
    (V293_write_byte M1 bh selected) in UpdatedH by reflexivity.
  set (Mf:=V293_write_byte M1 bh selected) in *.
  assert (HM : V293_sched_read_memory M bt bg br lo hi g).
  { destruct Loads as [L [H [G T]]]. unfold V293_sched_read_memory. auto. }
  destruct WH as [vh WH].
  assert (WHold : get M (bh,0%Z)=Some (true,vh)).
  { unfold M1 in WH. rewrite V293_write_byte_other in WH by exact YH. exact WH. }
  assert (Execution : cstepstar P
    (curs (V293_OSSchedNew_updates unmap group rows high y),(kenil,ks)) (ge,le,M)
    (curs (sskip None),(kenil,ks)) (ge,le,Mf)).
  { unfold Mf,M1,selected. eapply V293_OSSchedNew_updates_execution; eassumption || reflexivity. }
  assert (HL : load Tint8 Mf (bh,0%Z)=Some (V293_byteval selected)).
  { unfold Mf. apply V293_write_byte_load. lia. }
  assert (PL : load (Tptr V293_tcb_type) Mf (bp,(4*Z.of_nat selected)%Z)=Some (Vptr t)).
  { unfold Mf,M1,load,loadm in *. cbn [typelen] in *.
    rewrite (V293_loadbytes_equal_range 4
      (V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g)) bh selected)
      M bp (4*Z.of_nat selected)%Z).
    - exact Pointer.
    - intros k Bound. unfold V293_write_byte. repeat rewrite map_get_set' by (intro E; inversion E; congruence). reflexivity. }
  destruct (V293_eval_pointer_array ge le Mf table high V293_tcb_type bp bh selected (Vptr t)
    TN HN TG HG HL SB PL) as [Value TargetType].
  exists tasks. exists lo. exists hi. exists entries. exists t. exists message. exists Mf.
  split; [exact TaskMap | ]. split; [exact (conj Lo (conj Hi (conj Nonempty (conj Bitmap Table)))) | ].
  split; [exact Task | ]. split; [exact Execution | ]. split.
  - clear Held First Second UpdatedY InvHeld. sep auto.
  - split; [exact HL | ]. split; [exact Value | ]. split; [exact TargetType | ]. split; [exact PL | ]. split; [exact Sched | ].
    intros a AY AH. unfold Mf,M1,selected,g. apply V293_OSSchedNew_updates_frame; assumption.
Qed.


(* Caller supplies global bindings and ownership, never a local address.
   The GoodInvAsrt frame excludes assertions sensitive to the callee lenv. *)
Theorem V293_ready_sched_call : forall br bg bp P ks ge caller M ir aux O op current R
    f unmap group rows high y table bt bh oldhigh,
  P f=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high -> y<>table -> bh<>bp ->
  get ge unmap=Some (bt,Tarray Tint8 256) ->
  get ge group=Some (bg,Tint8) -> get ge rows=Some (br,Tarray Tint8 2) ->
  get ge high=Some (bh,Tint8) -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  GoodInvAsrt R ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,caller,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) ** R) ->
  exists tasks lo hi entries next message b Ms Mf,
    fresh M b /\
    get O abstcblsid=Some (abstcblist tasks) /\ V293_ready_rel lo hi entries tasks /\
    get tasks next=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** R) /\
    free Tint8 b Ms=Some Mf /\ get Mf (b,0%Z)=None /\
    V293_scheduler O next /\
    load Tint8 Mf (bh,0%Z)=Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    load (Tptr V293_tcb_type) Mf (bp,(4*Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))))%Z=Some (Vptr next) /\
    (forall c i, (c,i)<>(bh,0%Z) -> get Mf (c,i)=get M (c,i)).
Proof.
  intros br bg bp P ks ge caller M ir aux O op current R f unmap group rows high y table bt bh oldhigh
    Program YT YG YR YH YP HP GT GG GR GH GP Good Lookup Held.
  destruct (V293_ready_fresh_avoiding M [bt;bg;br;bh;bp]) as (b&Fresh&Away).
  assert (BT : b<>bt) by (intro E;apply Away;subst;simpl;tauto).
  assert (BG : b<>bg) by (intro E;apply Away;subst;simpl;tauto).
  assert (BR : b<>br) by (intro E;apply Away;subst;simpl;tauto).
  assert (BH : b<>bh) by (intro E;apply Away;subst;simpl;tauto).
  assert (BP : b<>bp) by (intro E;apply Away;subst;simpl;tauto).
  set (le:=(set emp y (b,Tint8) : env)).
  set (Ma:=allocb M b 0%Z (typelen Tint8)).
  assert (Names : forall x, y<>x -> get le x=None).
  { intros x N. unfold le. rewrite map_get_set' by exact N. apply map_emp_get. }
  assert (Env : V293_sched_read_env ge le unmap group rows bt bg br).
  { repeat split;first [apply Names;assumption | assumption]. }
  assert (Frame : (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) ** R)).
  { eapply V293_ready_lenv_frame;[split;[unfold V293_owned_record_cell;cbn;split;exact I | exact Good] | exact Held]. }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op b Tint8 _ Fresh Frame) as Alloc.
  assert (Start : (ge,le,Ma,ir,aux,O,op) |=
    (Amapsto (b,0%Z) Tint8 true Vundef **
      V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh)) **
    (SWINVt (V293_ready_inv br bg bp) current ** R)).
  { sep auto. }
  assert (LookupA : forall n, n<256 -> load Tint8 Ma (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))).
  { intros n N. unfold Ma,load,loadm. cbn [typelen loadbytes].
    rewrite V293_success_allocb_outside by (left;congruence). apply Lookup;exact N. }
  set (body:=V293_OSSchedNew_body unmap group rows high y).
  destruct (V293_ready_sched_raw_updates br bg bp P (kseq sret (kcall f body caller ks))
    ge le Ma ir aux O op current R unmap group rows high y table bt bh b Vundef oldhigh
    Env ltac:(unfold le;apply map_get_set) (Names _ YH) GH (Names _ YP) GP
    BT BG BR BH BP HP LookupA Start)
    as (tasks&lo&hi&entries&next&message&Ms&Map&Rel&Task&Exec&After&High&Value&Ty&Pointer&Sched&Preserve).
  assert (Local : (ge,le,Ms,ir,aux,O,op) |= Amapsto (b,0%Z) Tint8 true
    (V293_byteval (V293_ready_lookup (V293_ready_group lo hi))) **
    (SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** R))).
  { unfold V293_owned_record_cell at 1 in After. sep auto. }
  destruct (V293_ready_release_byte _ _ _ _ _ _ _ _ _ _ Local) as (Mf&Free&Returned&Removed&Outside).
  assert (Caller : (ge,caller,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** R)).
  { eapply V293_ready_lenv_frame;[split;[unfold V293_owned_record_cell;cbn;split;exact I | exact Good] | exact Returned]. }
  assert (Layout : getaddr le=[(b,Tint8)]).
  { unfold le. change (getaddr (EnvMod.set EnvMod.emp y (b,Tint8))=[(b,Tint8)]).
    cbn [EnvMod.set EnvMod.lst EnvMod.set' EnvMod.emp EnvMod.emp' getaddr getaddrlist]. reflexivity. }
  exists tasks. exists lo. exists hi. exists entries. exists next. exists message. exists b. exists Ms. exists Mf.
  split;[exact Fresh | ]. split;[exact Map | ]. split;[exact Rel | ]. split;[exact Task | ]. split.
  - eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply snpcall_step]. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply sfexec_step with (d1:=dnil) (d2:=dcons y Tint8 dnil);
        [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
    eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | ]. eapply salloclv_step;[reflexivity | reflexivity | ].
      exists b. repeat split;try assumption;try reflexivity.
      intros [v E]. rewrite map_emp_get in E;discriminate. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sallocend_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_cstepstar_trans;[exact Exec | ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sskip_step]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sret_step;[reflexivity | reflexivity | exact Layout]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sfree_step;[reflexivity | reflexivity | exact Free]. }
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | ]. eapply sfreeend_step;reflexivity. }
    apply c_stepstar0.
  - split;[exact Caller | ]. split;[exact Free | ]. split;[exact Removed | ]. split;[exact Sched | ]. split.
    + unfold load,loadm. cbn [typelen loadbytes]. rewrite Outside by congruence. exact High.
    + split.
      * unfold load,loadm. cbn [typelen]. rewrite (V293_loadbytes_equal_range 4 Mf Ms bp
          (4*Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi)))%Z).
        -- exact Pointer.
        -- intros k K. apply Outside. congruence.
      * intros c i NotHigh. destruct (addr_eq_dec (c,i) (b,0%Z)) as [E | N].
        -- inversion E;subst. rewrite Removed. symmetry. apply V293_success_fresh_none;exact Fresh.
        -- destruct (Pos.eq_dec c b) as [E | E].
           ++ subst c. assert (NZ : i<>0%Z) by (intro E;apply N;congruence).
        rewrite (V293_freeb_outside _ _ _ _ _ _ _ Free) by (right;cbn;lia).
        rewrite Preserve by assumption. apply V293_success_allocb_outside. right;cbn;lia.
           ++ rewrite Outside by exact E. rewrite Preserve by assumption.
        apply V293_success_allocb_outside. left;exact E.
Qed.

(* Stable caller interface: actual no-argument call/return followed by the
   original target assignment. Target is a frame only up to this handoff. *)
Theorem V293_ready_dispatch_call : forall br bg bp P ks ge caller M ir aux O op current R
    f unmap group rows high y table target bt bh bo oldhigh oldtarget,
  P f=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high -> y<>table -> bh<>bp ->
  get ge unmap=Some (bt,Tarray Tint8 256) ->
  get ge group=Some (bg,Tint8) -> get ge rows=Some (br,Tarray Tint8 2) ->
  get ge high=Some (bh,Tint8) -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get caller high=None -> get caller table=None -> get caller target=None ->
  get ge target=Some (bo,Tptr V293_tcb_type) -> GoodInvAsrt R ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,caller,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) **
     (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)) ->
  exists tasks lo hi entries next message b Ms Mskip Mf,
    fresh M b /\ get O abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    get tasks next=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (scall f nil),(kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,caller,Mskip) /\
    (ge,caller,Mskip,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)) /\
    free Tint8 b Ms=Some Mskip /\ get Mskip (b,0%Z)=None /\
    load Tint8 Mskip (bh,0%Z)=Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) /\
    cstepstar P (curs (V293_OSSched_unlocked_prefix f table high target),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    store (Tptr V293_tcb_type) Mskip (bo,0%Z) (Vptr next)=Some Mf /\
    (ge,caller,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)) /\
    load (Tptr V293_tcb_type) Mf (bo,0%Z)=Some (Vptr next) /\
    V293_scheduler O next /\
    (ge,caller,Mf,ir,aux,O,op) |= SWPRE V293_scheduler target current /\
    (indom tasks current -> (ge,caller,Mf,ir,aux,O,op) |= SWPRE_NDEAD V293_scheduler target current) /\
    (~ indom tasks current -> (ge,caller,Mf,ir,aux,O,op) |= SWPRE_DEAD V293_scheduler target current) /\
    (forall c i, (c,i)<>(bh,0%Z) -> get Mskip (c,i)=get M (c,i)) /\
    (forall c i, c<>bo \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get Mskip (c,i)).
Proof.
  intros br bg bp P ks ge caller M ir aux O op current R f unmap group rows high y table target
    bt bh bo oldhigh oldtarget Program YT YG YR YH YP HP GT GG GR GH GP HN TN ON OG Good Lookup Held.
  assert (GFrame : GoodInvAsrt (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)).
  { split;[unfold V293_owned_record_cell;cbn;split;exact I | exact Good]. }
  destruct (V293_ready_sched_call br bg bp P (kseq (V293_OSSched_target_update table high target) ks)
    ge caller M ir aux O op current (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) ** R)
    f unmap group rows high y table bt bh oldhigh Program YT YG YR YH YP HP GT GG GR GH GP GFrame Lookup Held)
    as (tasks&lo&hi&entries&next&message&b&Ms&Mskip&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&Sched&High&Pointer&CallFrame).
  assert (Range : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
    apply V293_ready_selection_range;assumption || reflexivity. }
  destruct (V293_eval_pointer_array ge caller Mskip table high V293_tcb_type bp bh
    (V293_ready_select lo hi (V293_ready_group lo hi)) (Vptr next) TN HN GP GH High Range Pointer) as [Value Ty].
  assert (Writable : (ge,caller,Mskip,ir,aux,O,op) |=
    V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
    (SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ** R))) by (sep auto).
  destruct (V293_owned_record_cell_update _ (Tptr V293_tcb_type) _ (Vptr next) _ _ _ _ _ _ _ _
    eq_refl Writable) as (Mf&Store&After).
  assert (Execution : cstepstar P (curs (V293_OSSched_unlocked_prefix f table high target),(kenil,ks)) (ge,caller,M)
    (curs (sskip None),(kenil,ks)) (ge,caller,Mf)).
  { unfold V293_OSSched_unlocked_prefix. eapply c_stepstarn.
    { eapply stmt_step;[reflexivity | apply sseq_step]. }
    eapply V293_cstepstar_trans;[exact Call | ].
    eapply c_stepstarn. { eapply stmt_step;[reflexivity | apply sskip_step]. }
    unfold V293_OSSched_target_update.
    eapply V293_assign_pointer_execution with (tr:=Tptr V293_tcb_type) (b:=bo) (off:=0%Z);try eassumption.
    - cbn [evaltype]. rewrite ON,OG. reflexivity.
    - apply eq_vptr. eauto.
    - cbn [evaladdr get_lenv get_genv]. rewrite ON,OG. reflexivity.
    - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
  assert (Ready : (ge,caller,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** Atrue)) by (sep auto).
  pose proof (V293_ready_target_pre br bg bp current target bo next Atrue ge caller Mf ir aux O op OG Sched Ready) as Pre.
  assert (Tasks : (ge,caller,Mf,ir,aux,O,op) |= Aabsdata abstcblsid (abstcblist tasks) ** Atrue).
  { eapply astar_mono in Ready;[ | apply V293_ready_switch_full | intros st H;exact H].
    unfold V293_ready_full in Ready. sep normal in Ready. sep destruct Ready.
    assert (Map' : get O abstcblsid=Some (abstcblist x)).
    { eapply V293_star_abst_get_l with (s:=(ge,caller,Mf,ir,aux,O,op)) (p:=Aabsdata abstcblsid (abstcblist x)) (q:=Atrue);
        [intros st H;rewrite <- (proj1 H);apply map_get_sig | ].
      unfold V293_shared_fields in Ready. sep auto. }
    assert (x=tasks) by congruence. subst x. unfold V293_shared_fields in Ready. sep auto. }
  exists tasks. exists lo. exists hi. exists entries. exists next. exists message.
  exists b. exists Ms. exists Mskip. exists Mf.
  split;[exact Fresh | ]. split;[exact Map | ]. split;[exact Rel | ]. split;[exact Task | ].
  split;[exact Call | ]. split;[exact Skipped | ]. split;[exact Free | ]. split;[exact Removed | ]. split;[exact High | ].
  split;[exact Execution | ]. split;[exact Store | ]. split.
  - clear Held Skipped Writable Ready Tasks Pre. sep auto.
  - split.
    + eapply V293_record_star_load_l with (s:=(ge,caller,Mf,ir,aux,O,op));[ | exact After].
      intros st H. eapply V293_owned_record_cell_load;exact H.
    + split;[exact Sched | ]. split;[exact Pre | ]. split.
      * intro Live. split;[exact Pre | ]. exists tasks. sep auto.
      * split.
        -- intro Dead. split;[exact Pre | ]. exists tasks. sep auto.
        -- split;[exact CallFrame | ]. intros c i Outside.
           eapply V293_storebytes_outside;[exact Store | destruct next as [nb ni];cbn [encode_val inj_pointer length];exact Outside].
Qed.
