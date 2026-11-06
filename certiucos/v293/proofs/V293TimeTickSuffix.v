(* Exact post-hook suffix of the frozen OSTimeTick body. The CPU hook remains
   an open boundary; no invented hook body or successful-execution premise. *)
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

Definition V293_tick_post_hook ptcb rows group now running head : stmts :=
  sseq (sprim encrit)
    (sseq (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
      (sseq (sprim excrit)
        (sifthen (V293_tick_eq (ecast (evar running) Tint32) 1)
          (sseq (sassign (evar ptcb) (evar head))
            (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)))))).

Theorem V293_tick_post_hook_exact : forall ptcb rows group saved now running head hook,
  V293_tick_body ptcb rows group saved now running head hook =
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (scall hook nil) (V293_tick_post_hook ptcb rows group now running head)).
Proof. reflexivity. Qed.

Definition V293_tick_suffix_owned bn tick bu run bh head bc scan tasks idle bg br g lo hi R : asrt :=
  V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 tick) **
  (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
    (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr head) **
      V293_tick_loop_owned bc scan tasks idle bg br g lo hi R)).

Theorem V293_tick_post_hook_owned_execution :
  forall tasks P ks ge le M ir enabled si ci O op ptcb rows group now running head
    bc bn bu bh scan idle bg br tick run g lo hi R,
  get le ptcb = Some (bc,Tptr V293_tcb_type) ->
  get le rows = None -> get ge rows = Some (br,Tarray Tint8 2) ->
  get le group = None -> get ge group = Some (bg,Tint8) ->
  get le now = None -> get ge now = Some (bn,Tint32) ->
  get le running = None -> get ge running = Some (bu,Tint8) ->
  get le head = None -> get ge head = Some (bh,Tptr V293_tcb_type) ->
  (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
  Forall V293_tick_task_valid tasks -> run<256 -> g<256 -> lo<256 -> hi<256 ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |=
    V293_tick_suffix_owned bn tick bu run bh (V293_tick_head tasks idle)
      bc scan tasks idle bg br g lo hi R ->
  let bitmap := if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)) in
  exists Mf,
  V293_local_steps P (curs (V293_tick_post_hook ptcb rows group now running head),(kenil,ks))
    ((ge,le,M),ir,(enabled,si,ci))
    (curs (sskip None),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
  load Tint32 Mf (bn,0%Z) = Some (Vint32 (Int.add tick Int.one)) /\
  load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (if Nat.eqb run 1 then idle else scan)) /\
  (ge,le,Mf,ir,(enabled,si,ci),O,op) |=
    V293_tick_suffix_owned bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
      bc (if Nat.eqb run 1 then idle else scan)
      (if Nat.eqb run 1 then map V293_tick_task_after tasks else tasks)
      idle bg br (fst bitmap) (fst (snd bitmap)) (snd (snd bitmap)) R.
Proof.
  intros tasks P ks ge le M ir enabled si ci O op ptcb rows group now running head
    bc bn bu bh scan idle bg br tick run g lo hi R
    Bc Nr Gr Ng Gg Nn Gn Nu Gu Nh Gh IdleLimit Valid Run G Lo Hi Owned.
  assert (ReadTime : load Tint32 M (bn,0%Z) = Some (Vint32 tick)).
  { change (load Tint32 (getmem (ge,le,M,ir,(enabled,si,ci),O,op)) (bn,0%Z) = Some (Vint32 tick)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Owned]. }
  unfold V293_tick_suffix_owned in Owned.
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
      V293_tick_suffix_owned bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
        bc (if Nat.eqb run 1 then idle else scan)
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
        V293_owned_record_cell (V293_tick_pointer_cell bc scan) **
        (V293_owned_record_cells (V293_tick_chain_cells tasks idle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells bg br g lo hi) **
            (V293_owned_record_cell (V293_tick_idle_cell idle) **
              (V293_owned_record_cell ((bn,0%Z),Tint32,Vint32 (Int.add tick Int.one)) **
                (V293_owned_record_cell ((bu,0%Z),Tint8,V293_byteval run) **
                  (V293_owned_record_cell ((bh,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head tasks idle)) ** R))))))).
      { unfold V293_tick_loop_owned in Mid. clear -Mid. sep auto. }
      destruct (V293_owned_record_cell_update (bc,0%Z) (Tptr V293_tcb_type) _
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
      + unfold V293_tick_suffix_owned,V293_tick_loop_owned in *. cbn beta iota in *.
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
  assert (FinalPointer : load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (if Nat.eqb run 1 then idle else scan))).
  { change (load (Tptr V293_tcb_type) (getmem (ge,le,Mf,ir,(enabled,si,ci),O,op)) (bc,0%Z) = Some (Vptr (if Nat.eqb run 1 then idle else scan))).
    eapply V293_record_star_load_r; [ | exact Returned]. eapply V293_record_star_load_r.
    eapply V293_record_star_load_r. eapply V293_record_star_load_l. apply V293_owned_record_cell_load. }
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

Print Assumptions V293_tick_post_hook_exact.
Print Assumptions V293_tick_post_hook_owned_execution.
