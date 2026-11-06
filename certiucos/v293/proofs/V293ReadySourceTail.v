(* Original priority-byte guard and modular counter write, up to the exact
   switch code. Uninterleaved source trace, not all OS_Sched or GOOD_OS.
   In particular the bare framework switch does not synchronize OSPrioCur. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Local Open Scope nat_scope.

Lemma V293_ready_counter_eval : forall ge le M counter b c,
  get le counter=None -> get ge counter=Some (b,Tint32) ->
  load Tint32 M (b,0%Z)=Some (Vint32 c) ->
  evaltype (evar counter) (ge,le,M)=Some Tint32 /\
  evaltype (ebinop oplus (evar counter) (econst32 Int.one)) (ge,le,M)=Some Tint32 /\
  evaladdr (evar counter) (ge,le,M)=Some (Vptr (b,Int.zero)) /\
  evalval (ebinop oplus (evar counter) (econst32 Int.one)) (ge,le,M)=
    Some (Vint32 (Int.add c Int.one)).
Proof.
  intros ge le M counter b c N G L.
  cbn [evaltype evaladdr evalval get_lenv get_genv get_mem]. rewrite N,G.
  cbn -[load]. rewrite L. repeat split;reflexivity.
Qed.

(* The endpoint code is decided by the ACTUAL two source bytes.  The counter
   store is constructed from ownership, and only the unequal branch writes. *)
Theorem V293_ready_source_change : forall br bg bp P ks ge le M ir aux O op
    (current : tid) high cached counter target bh bc bn nh nc c R,
  nh<256 -> nc<256 ->
  get le high=None -> get le cached=None -> get le counter=None ->
  get ge high=Some (bh,Tint8) -> get ge cached=Some (bc,Tint8) ->
  get ge counter=Some (bn,Tint32) ->
  (ge,le,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval nh) **
     (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
      (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) ** R))) ->
  exists Mf,
    cstepstar P (curs (V293_OSSched_change high cached counter (sprim (switch target))),(kenil,ks)) (ge,le,M)
      ((if Nat.eqb nh nc then SKIP else curs (sprim (switch target))),(kenil,ks)) (ge,le,Mf) /\
    (if Nat.eqb nh nc then Mf=M else
      store Tint32 M (bn,0%Z) (Vint32 (Int.add c Int.one))=Some Mf) /\
    (ge,le,Mf,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval nh) **
       (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
        (V293_owned_record_cell ((bn,0%Z),Tint32,
          Vint32 (if Nat.eqb nh nc then c else Int.add c Int.one)) ** R))) /\
    load Tint32 Mf (bn,0%Z)=Some (Vint32 (if Nat.eqb nh nc then c else Int.add c Int.one)) /\
    (forall b i, b<>bn \/ (i<0)%Z \/ (4<=i)%Z -> get Mf (b,i)=get M (b,i)).
Proof.
  intros br bg bp P ks ge le M ir aux O op current high cached counter target bh bc bn nh nc c R
    Nh Nc HN CN NN HG CG NG Held.
  assert (ReadHigh : load Tint8 M (bh,0%Z)=Some (V293_byteval nh)).
  { change (load Tint8 (getmem (ge,le,M,ir,aux,O,op)) (bh,0%Z)=Some (V293_byteval nh)).
    eapply V293_record_star_load_r; [ | exact Held].
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  assert (ReadCache : load Tint8 M (bc,0%Z)=Some (V293_byteval nc)).
  { change (load Tint8 (getmem (ge,le,M,ir,aux,O,op)) (bc,0%Z)=Some (V293_byteval nc)).
    eapply V293_record_star_load_r; [ | exact Held].
    eapply V293_record_star_load_r. eapply V293_record_star_load_l.
    apply V293_owned_record_cell_load. }
  assert (ReadCounter : load Tint32 M (bn,0%Z)=Some (Vint32 c)).
  { change (load Tint32 (getmem (ge,le,M,ir,aux,O,op)) (bn,0%Z)=Some (Vint32 c)).
    eapply V293_record_star_load_r; [ | exact Held].
    eapply V293_record_star_load_r. eapply V293_record_star_load_r.
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  destruct (V293_OSSched_byte_comparison_eval ge le M high cached bh bc nh nc
    Nh Nc HN CN HG CG ReadHigh ReadCache) as [Guard GuardType].
  destruct (Nat.eqb nh nc) eqn:Equal.
  - exists M. split.
    + unfold V293_OSSched_change. eapply V293_rekey_if_execution with (flag:=false);
        [exact Guard | discriminate | reflexivity].
    + repeat first [assumption | split | reflexivity].
  - assert (Cell : (ge,le,M,ir,aux,O,op) |=
      V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) **
      (SWINVt (V293_ready_inv br bg bp) current **
       (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval nh) **
        (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) ** R)))) by (sep auto).
    destruct (V293_owned_record_cell_update (bn,0%Z) Tint32 (Vint32 c) (Vint32 (Int.add c Int.one)) _
      _ _ _ _ _ _ _ ltac:(reflexivity) Cell) as (Mf & Store & After).
    destruct (V293_ready_counter_eval ge le M counter bn c NN NG ReadCounter)
      as (TL & TR & Addr & Value).
    exists Mf. split.
    + unfold V293_OSSched_change.
      eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sifthen_step]. }
      eapply V293_cstepstar_trans.
      { apply V293_expr_steps. apply evalval_imply_estepstar. exact Guard. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply svift_step;reflexivity]. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sseq_step]. }
      eapply V293_cstepstar_trans.
      { unfold V293_OSSched_increment. eapply V293_tick_assign32_execution with (off:=0%Z);
          try eassumption; try reflexivity; unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia. }
      eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sskip_step]. }
      apply c_stepstar0.
    + split; [exact Store | ]. split; [clear Held Cell;sep auto | ]. split.
      * change (load Tint32 (getmem (ge,le,Mf,ir,aux,O,op)) (bn,0%Z)=Some (Vint32 (Int.add c Int.one))).
        eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact After].
      * intros b i Outside. eapply V293_storebytes_outside;
          [exact Store | cbn [encode_val inj_bytes length];exact Outside].
Qed.

(* Same real call/return and target assignment, now with the source tail in
   their continuation. There is no independent 'current code is switch'
   premise. The unequal endpoint is exactly the code used by pswitch_step. *)
Theorem V293_ready_source_dispatch : forall br bg bp P ks ge caller M ir aux O op (current : tid) R
    f unmap group rows high y table target cached counter bt bh bo bc bn nc c oldhigh oldtarget,
  P f=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high -> y<>table -> bh<>bp ->
  get ge unmap=Some (bt,Tarray Tint8 256) ->
  get ge group=Some (bg,Tint8) -> get ge rows=Some (br,Tarray Tint8 2) ->
  get ge high=Some (bh,Tint8) -> get ge table=Some (bp,Tarray (Tptr V293_tcb_type) 13) ->
  get caller high=None -> get caller table=None -> get caller target=None ->
  get ge target=Some (bo,Tptr V293_tcb_type) ->
  get caller cached=None -> get caller counter=None ->
  get ge cached=Some (bc,Tint8) -> get ge counter=Some (bn,Tint32) -> nc<256 ->
  GoodInvAsrt R ->
  (forall n, n<256 -> load Tint8 M (bt,Z.of_nat n)=Some (V293_byteval (V293_ready_lookup n))) ->
  (ge,caller,M,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,oldhigh) **
     (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
      (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
       (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) ** R)))) ->
  exists tasks lo hi entries next message Mtarget Mtail,
    get O abstcblsid=Some (abstcblist tasks) /\ V293_ready_rel lo hi entries tasks /\
    get tasks next=Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))),rdy,message) /\
    cstepstar P
      (curs (sseq (V293_OSSched_unlocked_prefix f table high target)
        (V293_OSSched_change high cached counter (sprim (switch target)))),(kenil,ks)) (ge,caller,M)
      ((if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
        then SKIP else curs (sprim (switch target))),(kenil,ks)) (ge,caller,Mtail) /\
    (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Mtail=Mtarget else
      store Tint32 Mtarget (bn,0%Z) (Vint32 (Int.add c Int.one))=Some Mtail) /\
    (ge,caller,Mtail,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
      (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
       (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
        (V293_owned_record_cell ((bn,0%Z),Tint32,
          Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one)) **
         (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)))) /\
    load (Tptr V293_tcb_type) Mtail (bo,0%Z)=Some (Vptr next) /\
    load Tint32 Mtail (bn,0%Z)=Some (Vint32
      (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then c else Int.add c Int.one)) /\
    load Tint8 Mtail (bc,0%Z)=Some (V293_byteval nc) /\
    (forall b i, b<>bn \/ (i<0)%Z \/ (4<=i)%Z -> get Mtail (b,i)=get Mtarget (b,i)).
Proof.
  intros br bg bp P ks ge caller M ir aux O op current R f unmap group rows high y table target
    cached counter bt bh bo bc bn nc c oldhigh oldtarget
    Program YT YG YR YH YP HP GT GG GR GH GP HN TN ON OG CN NN CG NG Nc Good Lookup Held.
  assert (GFrame : GoodInvAsrt (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
    (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) ** R))).
  { split; [unfold V293_owned_record_cell;cbn;split;exact I | ].
    split; [unfold V293_owned_record_cell;cbn;split;exact I | exact Good]. }
  destruct (V293_ready_dispatch_call br bg bp P
    (kseq (V293_OSSched_change high cached counter (sprim (switch target))) ks)
    ge caller M ir aux O op current
    (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
      (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) ** R))
    f unmap group rows high y table target bt bh bo oldhigh oldtarget
    Program YT YG YR YH YP HP GT GG GR GH GP HN TN ON OG GFrame Lookup Held)
    as (tasks & lo & hi & entries & next & message & b & Ms & Mskip & Mtarget & Fresh & Map & Rel & Task & Call & Skipped & Free & Removed & High & Prefix & Store & After & Load & Sched & Pre & Member & Dead & CallFrame & Frame).
  assert (Range : V293_ready_select lo hi (V293_ready_group lo hi)<13).
  { destruct Rel as [Lo [Hi [Nonempty [Bitmap Table]]]].
    apply V293_ready_selection_range;assumption || reflexivity. }
  assert (TailEntry : (ge,caller,Mtarget,ir,aux,O,op) |= SWINVt (V293_ready_inv br bg bp) current **
    (V293_owned_record_cell ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) **
     (V293_owned_record_cell ((bc,0%Z),Tint8,V293_byteval nc) **
      (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 c) **
       (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R))))).
  { clear Held Skipped Pre. sep auto. }
  destruct (V293_ready_source_change br bg bp P ks ge caller Mtarget ir aux O op current
    high cached counter target bh bc bn (V293_ready_select lo hi (V293_ready_group lo hi)) nc c
    (V293_owned_record_cell ((bo,0%Z),Tptr V293_tcb_type,Vptr next) ** R)
    ltac:(lia) Nc HN CN NN GH CG NG TailEntry)
    as (Mtail & Tail & CounterStore & Final & CounterLoad & Outside).
  exists tasks. exists lo. exists hi. exists entries. exists next. exists message.
  exists Mtarget. exists Mtail.
  split; [exact Map | ]. split; [exact Rel | ]. split; [exact Task | ]. split.
  - eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sseq_step]. }
    eapply V293_cstepstar_trans; [exact Prefix | ].
    eapply c_stepstarn. { eapply stmt_step; [reflexivity | apply sskip_step]. }
    exact Tail.
  - split; [exact CounterStore | ]. split; [exact Final | ]. split.
    + change (load (Tptr V293_tcb_type) (getmem (ge,caller,Mtail,ir,aux,O,op)) (bo,0%Z)=Some (Vptr next)).
      eapply V293_record_star_load_r; [ | exact Final].
      do 3 eapply V293_record_star_load_r. eapply V293_record_star_load_l.
      apply V293_owned_record_cell_load.
    + split; [exact CounterLoad | ]. split; [ | exact Outside].
      change (load Tint8 (getmem (ge,caller,Mtail,ir,aux,O,op)) (bc,0%Z)=Some (V293_byteval nc)).
      eapply V293_record_star_load_r; [ | exact Final].
      eapply V293_record_star_load_r. eapply V293_record_star_load_l.
      apply V293_owned_record_cell_load.
Qed.
