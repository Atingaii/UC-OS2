(* Fresh ptcb storage and the real post-hook suffix, not a complete function. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Local Open Scope nat_scope.

(* Raw storage is deliberately not the typed value assertion: fresh pointer
   allocation contains Vundef, which fails rule_type_val_match. *)
Lemma V293_tick_raw_slot_update :
  forall a tp old replacement R ge le M ir aux O op,
  rule_type_val_match tp replacement = true ->
  (ge,le,M,ir,aux,O,op) |= Amapsto a tp true old ** R ->
  exists Mf, store tp M a replacement = Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cell (a,tp,replacement) ** R.
Proof.
  intros a tp old replacement R ge le M ir aux O op Valid Owned.
  apply sat_split in Owned.
  destruct Owned as (m1 & m2 & o1 & o2 & JM & JO & [Mapsto Empty] & Frame).
  destruct (store_exist_join' a tp old replacement m1 m2 M Mapsto JM) as [Mf Store].
  destruct (store_mapstoval_frame1 _ _ _ _ _ _ _ _ Mapsto JM Store)
    as (m1' & Mapsto' & LocalStore & JM').
  exists Mf. split; [exact Store | ].
  exists m1'. exists m2. exists Mf. exists o1. exists o2. exists O.
  split; [reflexivity | ]. split; [exact JM' | ].
  split; [reflexivity | ]. split; [exact JO | ]. split; [ | exact Frame].
  unfold V293_owned_record_cell. apply astar_l_apure_intro.
  - split; assumption.
  - exact Valid.
Qed.

Lemma V293_tick_raw_pointer_load : forall a tp v st,
  (v = Vundef \/ exists p, v = Vptr p) ->
  st |= Amapsto a (Tptr tp) true v ->
  load (Tptr tp) (getmem st) a = Some v.
Proof.
  intros a tp v st Values [Mapsto Empty].
  unfold mapstoval in Mapsto. destruct Mapsto as (vl & Enc & Bytes).
  subst vl. pose proof (ptomvallist_loadbytes _ _ _ _ Bytes) as Read.
  rewrite encode_val_length in Read. unfold load,loadm. destruct a as [b i].
  rewrite Read. destruct Values as [Undef | [p PointerValue]]; subst v.
  - reflexivity.
  - apply f_equal. apply type_val_mach_encode_val_decode_val. reflexivity.
Qed.

(* R is evaluated in the new environment. No arbitrary assertion is silently
   transported across an environment change. Allocation itself does not read ptcb. *)
Theorem V293_tick_scan_allocation : forall P ks dl ge le M ir aux O op ptcb bc R,
  fresh M bc -> ~ indom le ptcb ->
  (ge,set le ptcb (bc,Tptr V293_tcb_type),M,ir,aux,O,op) |= R ->
  let le' := set le ptcb (bc,Tptr V293_tcb_type) in
  let M' := allocb M bc 0%Z (typelen (Tptr V293_tcb_type)) in
  alloc ptcb (Tptr V293_tcb_type) le M le' M' /\
  cstep P (curs (salloc nil (dcons ptcb (Tptr V293_tcb_type) dl)),(kenil,ks))
    (ge,le,M) (curs (salloc nil dl),(kenil,ks)) (ge,le',M') /\
  (ge,le',M',ir,aux,O,op) |= Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef ** R /\
  load (Tptr V293_tcb_type) M' (bc,0%Z) = Some Vundef.
Proof.
  intros P ks dl ge le M ir aux O op ptcb bc R Fresh Unbound Frame le' M'.
  assert (Allocated : alloc ptcb (Tptr V293_tcb_type) le M le' M').
  { exists bc. repeat split; assumption || reflexivity. }
  assert (Joined : join (allocb empmem bc 0%Z (typelen (Tptr V293_tcb_type))) M M').
  { eapply join_allocb with (m1:=empmem) (m2:=M); [apply map_join_comm;apply map_join_emp | reflexivity | reflexivity | exact Fresh]. }
  assert (Owned : (ge,le',M',ir,aux,O,op) |=
    Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef ** R).
  { exists (allocb empmem bc 0%Z (typelen (Tptr V293_tcb_type))). exists M. exists M'.
    exists (emp:osabst). exists O. exists O.
    split; [reflexivity | ]. split; [exact Joined | ]. split; [reflexivity | ].
    split; [apply map_join_comm;apply map_join_emp | ]. split; [ | exact Frame].
    split; [apply alloc_empmem_mapstoval | reflexivity]. }
  split; [exact Allocated | ]. split.
  - eapply stmt_step; [reflexivity | ]. eapply salloclv_step; eauto.
  - split; [exact Owned | ].
    change (load (Tptr V293_tcb_type) (getmem (ge,le',M',ir,aux,O,op)) (bc,0%Z) = Some Vundef).
    eapply V293_record_star_load_l; [ | exact Owned].
    intros st Slot. eapply V293_tick_raw_pointer_load; [left; reflexivity | exact Slot].
Qed.

Definition V293_tick_storage_owned bn tick bu run bh head bc scan tasks idle bg br g lo hi R : asrt :=
  V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 tick) **
  (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
    (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr head) **
      (Amapsto (bc,0%Z) (Tptr V293_tcb_type) true scan **
        (V293_owned_record_cells (V293_tick_chain_cells tasks idle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) ** R)))))).

Theorem V293_tick_uninitialized_suffix_execution :
  forall tasks P ks ge le M ir enabled si ci O op ptcb rows group now running head
    bc bn bu bh idle bg br tick run g lo hi R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  get le now = None -> get ge now = Some (bn,Tint32) ->
  get le running = None -> get ge running = Some (bu,Tint8) ->
  get le head = None -> get ge head = Some (bh,Tptr V293_tcb_type) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_task_valid tasks -> run<256 -> g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_storage_owned bn tick bu run bh (V293_tick_head tasks idle)
      bc Vundef tasks idle bg br g lo hi R ->
  let bitmap := if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)) in
  exists Mf,
  V293_local_steps P (curs (V293_tick_post_hook ptcb rows group now running head),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Mf (bn,0%Z) = Some (Vint32 (Int.add tick Int.one)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vundef) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_tick_storage_owned bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
      bc (if Nat.eqb run 1 then Vptr idle else Vundef)
      (if Nat.eqb run 1 then map V293_tick_task_after tasks else tasks)
      idle bg br (fst bitmap) (fst (snd bitmap)) (snd (snd bitmap)) R.
Proof.
  intros tasks P ks ge le M ir enabled si ci O op ptcb rows group now running head
    bc bn bu bh idle bg br tick run g lo hi R
    Bc Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Run G Lo Hi Owned.
  assert (ReadTime : load Tint32 M (bn,0%Z) = Some (Vint32 tick)).
  { change (load Tint32 (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bn,0%Z) = Some (Vint32 tick)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned]. }
  unfold V293_tick_storage_owned in Owned.
  destruct (V293_owned_record_cell_update (bn,0%Z) Tint32 _ (Vint32 (Int.add tick Int.one))
    _ _ _ _ _ _ _ _ eq_refl Owned) as (M1 & StoreTime & Mid).
  assert (Increment : forall tail, cstepstar P
    (curs (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one))),(kenil,tail))
    (ge,le,M) (curs (sskip None),(kenil,tail)) (ge,le,M1)).
  { intro tail. eapply V293_tick_assign32_execution with (b:=bn) (off:=0%Z); try exact StoreTime.
    - cbn [evaltype get_lenv get_genv]. rewrite Nn,Gn. reflexivity.
    - cbn [evaltype get_lenv get_genv]. rewrite Nn,Gn. reflexivity.
    - cbn [evaladdr get_lenv get_genv]. rewrite Nn,Gn. reflexivity.
    - cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nn,Gn. cbn -[load]. rewrite ReadTime. reflexivity.
    - change (0<=0<=4294967295)%Z. lia. }
  assert (ReadRun : load Tint8 M1 (bu,0%Z) = Some (V293_byteval run)).
  { change (load Tint8 (getmem (ge,le,M1,ir,(enabled,si,ci),O,op)) (bu,0%Z) = Some (V293_byteval run)).
    eapply V293_record_star_load_r; [ | exact Mid].
    eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
  pose proof (V293_success_global_byte_eq ge le M1 running bu run 1 Run ltac:(lia) Nu Gu ReadRun) as Guard.
  change (evalval (V293_tick_eq (ecast (evar running) Tint32) 1) (ge,le,M1) =
    Some (Vint32 (if Nat.eqb run 1 then Int.one else Int.zero))) in Guard.
  assert (Branch : exists Mf,
    V293_local_steps P
      (curs (sifthen (V293_tick_eq (ecast (evar running) Tint32) 1)
        (sseq (sassign (evar ptcb) (evar head))
          (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)))),(kenil,ks))
      ((ge,le,M1),ir,(enabled,si,ci))
      (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
    (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
      V293_tick_storage_owned bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
        bc (if Nat.eqb run 1 then Vptr idle else Vundef)
        (if Nat.eqb run 1 then map V293_tick_task_after tasks else tasks) idle bg br
        (fst (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi))))
        (fst (snd (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)))))
        (snd (snd (if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi))))) R).
  { destruct (Nat.eqb run 1) eqn:Active.
    - assert (ReadHead : load (Tptr V293_tcb_type) M1 (bh,0%Z) = Some (Vptr (V293_tick_head tasks idle))).
      { change (load (Tptr V293_tcb_type) (getmem (ge,le,M1,ir,(enabled,si,ci),O,op)) (bh,0%Z) = Some (Vptr (V293_tick_head tasks idle))).
        eapply V293_record_star_load_r; [ | exact Mid]. eapply V293_record_star_load_r.
        eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
      assert (ToWrite : (ge,le,M1,ir,(enabled,si,ci),O,op) |=
        Amapsto (bc,0%Z) (Tptr V293_tcb_type) true Vundef **
        (V293_owned_record_cells (V293_tick_chain_cells tasks idle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) **
              (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add tick Int.one)) **
                (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
                  (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head tasks idle)) ** R))))))).
      { unfold V293_tick_storage_owned in Mid. clear -Mid. sep auto. }
      destruct (V293_tick_raw_slot_update (bc,0%Z) (Tptr V293_tcb_type) _
        (Vptr (V293_tick_head tasks idle)) _ _ _ _ _ _ _ _ eq_refl ToWrite) as (M2 & StoreHead & Entry).
      assert (AssignHead : forall tail, cstepstar P
        (curs (sassign (evar ptcb) (evar head)),(kenil,tail)) (ge,le,M1)
        (curs (sskip None),(kenil,tail)) (ge,le,M2)).
      { intro tail. eapply V293_assign_pointer_execution with (tp:=V293_tcb_type)
          (tr:=Tptr V293_tcb_type) (b:=bc) (off:=0%Z); try exact StoreHead.
        - cbn [evaltype get_lenv]. rewrite Bc. reflexivity.
        - cbn [evaltype get_lenv get_genv]. rewrite Nh,Gh. reflexivity.
        - apply eq_vptr; eauto.
        - cbn [evaladdr get_lenv]. rewrite Bc. reflexivity.
        - cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite Nh,Gh. exact ReadHead.
        - change (0<=0<=4294967295)%Z. lia. }
      change ((ge,le,M2,ir,(enabled,si,ci),O,op) |=
        V293_tick_loop_owned bc (V293_tick_head tasks idle) tasks idle bg br g lo hi
          (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add tick Int.one)) **
            (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
              (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head tasks idle)) ** R)))) in Entry.
      pose proof (V293_tick_while_owned_execution tasks P ks ge le M2 ir enabled si ci O op
        ptcb rows group bc idle bg br g lo hi _ Bc Nr Gr Ng Gg IdleLimit Valid G Lo Hi Entry) as Loop.
      destruct (V293_tick_chain_bitmap tasks g lo hi) as [gf [lof hif]] eqn:Bitmap.
      destruct Loop as (Mf & LoopExec & Pointer & Returned).
      exists Mf. split.
      + eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sifthen_step]. }
        eapply V293_local_trans.
        { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Guard. }
        eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply svift_step;reflexivity]. }
        eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
        eapply V293_local_trans. { apply V293_csteps_local. apply AssignHead. }
        eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
        exact LoopExec.
      + unfold V293_tick_storage_owned,V293_tick_loop_owned in *. cbn beta iota in *.
        assert (Raw : forall st, st |= V293_owned_record_cell (V293_tick_pointer_cell bc idle) ->
          st |= Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (Vptr idle)).
        { intros st Cell. apply astar_l_apure_elim in Cell. exact (proj2 Cell). }
        eapply astar_mono in Returned; [ | exact Raw | intros st H;exact H].
        clear -Returned. sep auto.
    - exists M1. split.
      + eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sifthen_step]. }
        eapply V293_local_trans.
        { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact Guard. }
        eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sviff_step;reflexivity]. }
        apply V293_local_refl.
      + exact Mid. }
  destruct Branch as (Mf & BranchExec & Returned).
  assert (FinalTime : load Tint32 Mf (bn,0%Z) = Some (Vint32 (Int.add tick Int.one))).
  { change (load Tint32 (getmem (ge,le,Mf,ir,(enabled,si,ci),O,op)) (bn,0%Z) = Some (Vint32 (Int.add tick Int.one))).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Returned]. }
  assert (FinalPointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vundef)).
  { change (load (Tptr V293_tcb_type) (getmem (ge,le,Mf,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vundef)).
    eapply V293_record_star_load_r; [ | exact Returned]. eapply V293_record_star_load_r.
    eapply V293_record_star_load_r. eapply V293_record_star_load_l.
    intros st Slot. eapply V293_tick_raw_pointer_load; [ | exact Slot].
    destruct (Nat.eqb run 1); [right; eexists; reflexivity | left; reflexivity]. }
  exists Mf. split.
  - unfold V293_tick_post_hook.
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply encrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_trans. { apply V293_csteps_local. apply Increment. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sseq_step]. }
    eapply V293_local_cons. { apply excrit_step;reflexivity. }
    eapply V293_local_cons. { apply ostc_step. eapply stmt_step; [reflexivity|apply sskip_step]. }
    exact BranchExec.
  - split; [exact FinalTime | ]. split; [exact FinalPointer | exact Returned].
Qed.


Print Assumptions V293_tick_uninitialized_suffix_execution.

Print Assumptions V293_tick_scan_allocation.
