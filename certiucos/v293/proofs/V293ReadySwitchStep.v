(* One actual framework switch after selection. Immediate-step framing only;
   no ownership or stability claim across resumption or arbitrary interleaving. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Section ReadySwitch.
Variables br bg bp : block.
Lemma V293_ready_store_frame : forall ct t R ge le M M' ir aux O op b tp,
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) ct ** R ->
  get ge OSTCBCur=Some (b,Tptr tp) ->
  store (Tptr tp) M (b,0%Z) (Vptr t)=Some M' ->
  (ge,le,M',ir,aux,set O curtid (oscurt t),op) |= SWINVt (V293_ready_inv br bg bp) t ** R.
Proof.
  intros ct t R ge le M M' ir aux O op b tp Hs GE HS.
  eapply astar_mono in Hs; [ | apply V293_ready_switch_full | intros st H;exact H].
  unfold V293_ready_full in Hs.
  sep normal in Hs. sep destruct Hs.
  assert (HP : (ge,le,M,ir,aux,O,op) |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr ct)) **
    (V293_shared_flags ** (V293_shared_fields ct x x0 x1 ** (V293_ready_payload br bg bp x ** R)))) by (sep auto).
  assert (ET : x2=tp).
  { unfold Agvarmapsto in HP. sep normal in HP. sep destruct HP.
    apply sat_split in HP. destruct HP as (ma & mb & oa & ob & JM & JO & [b0 [G _]] & HR).
    change (get ge OSTCBCur=Some (b0,Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP GE HS) as Stored.
  assert (HN : (ge,le,M',ir,aux,O,op) |= Aabsdata curtid (oscurt ct) **
    ((GV OSTCBCur @ (Tptr tp) |-> (Vptr t)) ** (V293_shared_flags **
      ((Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1))) **
        (V293_ready_payload br bg bp x ** R))))).
  { unfold V293_shared_fields in Stored. clear HP Hs. sep auto. }
  apply V293_shared_replace_slot with (new:=oscurt t) in HN.
  apply astar_mono with (P:=V293_shared_flags ** V293_ready_full br bg bp t) (Q:=R);
    [apply V293_ready_switch_halves | intros st H;exact H | ].
  unfold V293_ready_full,V293_shared_fields.
  clear Hs HP Stored. sep auto.
Qed.
(* Full current ownership is sufficient to construct the physical store. *)
Lemma V293_ready_current_write : forall current next R ge le M ir aux O op b tp,
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current ** R ->
  get ge OSTCBCur=Some (b,Tptr tp) ->
  exists Mf, store (Tptr tp) M (b,0%Z) (Vptr next)=Some Mf /\
    (ge,le,Mf,ir,aux,set O curtid (oscurt next),op) |=
      SWINVt (V293_ready_inv br bg bp) next ** R /\
    load (Tptr tp) Mf (b,0%Z)=Some (Vptr next) /\
    (forall c i, c<>b \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get M (c,i)).
Proof.
  intros current next R ge le M ir aux O op b tp Held GE.
  assert (Open : (ge,le,M,ir,aux,O,op) |=
    (V293_shared_flags ** V293_ready_full br bg bp current) ** R).
  { eapply astar_mono; [apply V293_ready_switch_full | intros st H;exact H | exact Held]. }
  unfold V293_ready_full in Open. sep normal in Open. sep destruct Open.
  assert (Named : (ge,le,M,ir,aux,O,op) |=
    (GV OSTCBCur @ (Tptr x2) |-> (Vptr current)) ** Atrue) by (sep auto).
  apply sat_split in Named. destruct Named as (ma & mb & oa & ob & JM & JO & Cell & Frame).
  destruct (V293_dispatch_named_cell_parts _ _ _ _ _ _ _ _ _ _ Cell) as (b0  &  GE0  &  HC  &  HE).
  change (get ge OSTCBCur=Some (b0,Tptr x2)) in GE0.
  assert (b0=b /\ x2=tp) by (split;congruence). destruct H;subst b0 x2.
  destruct (store_exist_join' (b,0%Z) (Tptr tp) (Vptr current) (Vptr next) ma mb M HC JM) as [Mf Store].
  exists Mf. split; [exact Store | ]. split.
  - eapply V293_ready_store_frame; eassumption.
  - split.
    + eapply V293_store_readback; [reflexivity | exact Store].
    + intros c i Outside. eapply V293_storebytes_outside;
        [exact Store | destruct next as [nb ni];cbn [encode_val inj_pointer length];exact Outside].
Qed.

(* The actual primitive consumes one common pointee type for target/current.
   No successful store or chosen final memory is supplied by the caller. *)
Theorem V293_ready_switch_step :
  forall pc po pi ip T cst ks (current next : tid) target bt bc ge le les M ir aux au O op R tp,
  get les current=Some le -> get au current=Some aux ->
  get T current=Some (curs (sprim (switch target)),(kenil,ks)) ->
  get ge target=Some (bt,Tptr tp) ->
  load (Tptr tp) M (bt,0%Z)=Some (Vptr next) ->
  get ge OSTCBCur=Some (bc,Tptr tp) ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current ** R ->
  exists Mf,
    lpstep (pc,(po,pi,ip)) T cst (ge,les,M,ir,au) current
      (set T current (SKIP,(kenil,ks))) cst (ge,les,Mf,ir,au) next /\
    store (Tptr tp) M (bc,0%Z) (Vptr next)=Some Mf /\
    (ge,le,Mf,ir,aux,set O curtid (oscurt next),op) |=
      SWINVt (V293_ready_inv br bg bp) next ** R /\
    load (Tptr tp) Mf (bc,0%Z)=Some (Vptr next) /\
    get (set T current (SKIP,(kenil,ks))) current=Some (SKIP,(kenil,ks)) /\
    (forall t, t<>current -> get (set T current (SKIP,(kenil,ks))) t=get T t) /\
    (forall c i, c<>bc \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get M (c,i)).
Proof.
  intros pc po pi ip T cst ks current next target bt bc ge le les M ir aux au O op R tp
    Local Aux Code Target Read Current Held.
  destruct (V293_ready_current_write current next R ge le M ir aux O op bc tp Held Current)
    as (Mf & Store & After & Load & Outside).
  exists Mf. split.
  - eapply pswitch_step with (tst:=((ge,le,M),ir,aux)) (l:=bt) (tp:=tp) (b:=bc);
      try reflexivity; try eassumption.
    unfold projS,projD. cbn. rewrite Local,Aux. reflexivity.
  - split; [exact Store | ]. split; [exact After | ]. split; [exact Load | ].
    split; [apply map_get_set | ]. split; [ | exact Outside].
    intros t Apart. apply map_get_set'. intro E. apply Apart. symmetry;exact E.
Qed.
End ReadySwitch.

(* Source call-return/target segment and one switch share exactly Mtarget. This
   does not insert a switch into the original AST or prove all OS_Sched. *)
Theorem V293_ready_call_then_switch : forall br bg bp P ks ge caller M ir aux O op (current : tid) R
    f unmap group rows high y table target bt bh bo oldhigh oldtarget pc po pi ip T cst les au bc,
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
  get les current=Some caller -> get au current=Some aux ->
  get T current=Some (curs (sprim (switch target)),(kenil,ks)) ->
  get ge OSTCBCur=Some (bc,Tptr V293_tcb_type) ->
  exists tasks lo hi entries next message b Ms Mskip Mtarget, exists Mf,
    fresh M b /\ get O abstcblsid=Some (abstcblist tasks) /\
    V293_ready_rel lo hi entries tasks /\
    get tasks next=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P (curs (scall f nil),(kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (V293_OSSched_target_update table high target) ks)) (ge,caller,Mskip) /\
    free Tint8 b Ms=Some Mskip /\ get Mskip (b,0%Z)=None /\
    cstepstar P (curs (V293_OSSched_unlocked_prefix f table high target),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mtarget) /\
    store (Tptr V293_tcb_type) Mskip (bo,0%Z) (Vptr next)=Some Mtarget /\
    V293_scheduler O next /\
    (ge,caller,Mtarget,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)) /\
    (ge,caller,Mtarget,ir,aux,O,op) |= SWPRE V293_scheduler target current /\
    lpstep (pc,(po,pi,ip)) T cst (ge,les,Mtarget,ir,au) current
      (set T current (SKIP,(kenil,ks))) cst (ge,les,Mf,ir,au) next /\
    store (Tptr V293_tcb_type) Mtarget (bc,0%Z) (Vptr next)=Some Mf /\
    (ge,caller,Mf,ir,aux,set O curtid (oscurt next),op) |=
      SWINVt (V293_ready_inv br bg bp) next **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)) /\
    load (Tptr V293_tcb_type) Mf (bc,0%Z)=Some (Vptr next) /\
    (forall c i, c<>bc \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (c,i)=get Mtarget (c,i)).
Proof.
  intros br bg bp P ks ge caller M ir aux O op current R f unmap group rows high y table target
    bt bh bo oldhigh oldtarget pc po pi ip T cst les au bc
    Program YT YG YR YH YP HP GT GG GR GH GP HN TN ON OG Good Lookup Held Local Aux Code Cur.
  destruct (V293_ready_dispatch_call br bg bp P ks ge caller M ir aux O op current R
    f unmap group rows high y table target bt bh bo oldhigh oldtarget
    Program YT YG YR YH YP HP GT GG GR GH GP HN TN ON OG Good Lookup Held)
    as (tasks & lo & hi & entries & next & message & b & Ms & Mskip & Mtarget & Fresh & Map & Rel & Task & Call & Skipped & Free & Removed & High & Exec & Store & After & Load & Sched & Pre & Member & Dead & CallFrame & Frame).
  destruct (V293_ready_switch_step br bg bp pc po pi ip T cst ks current next target bo bc
    ge caller les Mtarget ir aux au O op
    (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
      (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R))
    V293_tcb_type Local Aux Code OG Load Cur After)
    as (Mf & Step & CurStore & Final & CurLoad & Hskip & Other & Outside).
  exists tasks. exists lo. exists hi. exists entries. exists next. exists message.
  exists b. exists Ms. exists Mskip. exists Mtarget. exists Mf.
  repeat first [assumption | split].
Qed.
