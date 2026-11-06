(* OS_SchedNew called before there is a current task. Real allocation,
   two source assignments, void return/free; no CurTid or CurLINV premise. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Lemma V293_start_alloc_reads : forall M b bt bg br lo hi g,
  b<>bt -> b<>bg -> b<>br -> V293_sched_read_memory M bt bg br lo hi g ->
  V293_sched_read_memory (allocb M b 0%Z 1) bt bg br lo hi g.
Proof.
  intros M b bt bg br lo hi g Dt Dg Dr [G [T [L H]]].
  unfold V293_sched_read_memory,load,loadm in *; cbn [typelen loadbytes] in *.
  repeat split; try (rewrite V293_success_allocb_outside by (left;congruence);assumption).
  intros n Bound. rewrite V293_success_allocb_outside by (left;congruence). apply T;exact Bound.
Qed.

Lemma V293_start_byte_owned : forall before b old after n R ge le M ir aux O op,
  n<256 ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells (before++((b,0%Z),Tint8,old)::after) R ->
  (ge,le,V293_write_byte M b n,ir,aux,O,op) |=
    V293_rdy_raw_cells (before++((b,0%Z),Tint8,V293_byteval n)::after) R.
Proof.
  intros before b old after n R ge le M ir aux O op Bound Owned.
  apply V293_rdy_cell_out in Owned.
  destruct (V293_tick_raw_slot_update _ _ _ _ _ _ _ _ _ _ _ _
    (V293_byte_type n Bound) Owned) as (Mf&Store&Updated).
  assert (Same : Mf=V293_write_byte M b n).
  { unfold store in Store. cbn [V293_byteval encode_val inj_bytes encode_int List.map storebytes] in Store.
    unfold addr,offset in *. destruct (get M (b,0%Z)) as [[permission previous]| ] eqn:E;try discriminate.
    destruct permission;try discriminate. inversion Store;reflexivity. }
  subst Mf. apply V293_rdy_cell_in. unfold V293_owned_record_cell in Updated.
  apply astar_assoc_elim in Updated. apply astar_l_apure_elim in Updated.
  destruct Updated as [_ Updated]. exact Updated.
Qed.

Theorem V293_OSSchedNew_startup_call : forall survivors P ks ge caller M ir aux O op
    f unmap group rows high y bt bg br bh byblock lo hi g oldhigh,
  P f=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bt,Tarray Tint8 256) ->
  get ge group=Some (bg,Tint8) -> get ge rows=Some (br,Tarray Tint8 2) ->
  get ge high=Some (bh,Tint8) ->
  fresh M byblock -> byblock<>bt -> byblock<>bg -> byblock<>br -> byblock<>bh ->
  (forall a tp v, In (a,tp,v) survivors -> fst a<>byblock) ->
  lo<256 -> hi<256 -> g=V293_ready_group lo hi -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_sched_read_memory M bt bg br lo hi g ->
  (ge,caller,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (((bh,0%Z),Tint8,oldhigh)::survivors) Atrue ->
  exists Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi g))::survivors) Atrue /\
    get Mf (byblock,0%Z)=None.
Proof.
  intros survivors P ks ge caller M ir aux O op f unmap group rows high y bt bg br bh byblock
    lo hi g oldhigh Program Nt Ng Nr Nh Gt Gg Gr Gh Fresh Dt Dg Dr Dh Away
    Lo Hi Group Nonempty Reads Owned.
  set (le:=set (emp:env) y (byblock,Tint8)).
  set (Ma:=allocb M byblock 0%Z 1).
  assert (Env : V293_sched_read_env ge le unmap group rows bt bg br).
  { unfold V293_sched_read_env,le. repeat split;try assumption;
    rewrite map_get_set' by congruence;apply map_emp_get. }
  assert (Y : get le y=Some (byblock,Tint8)) by (unfold le;apply map_get_set).
  assert (H : get le high=None).
  { unfold le. rewrite map_get_set' by congruence. apply map_emp_get. }
  assert (ReadA : V293_sched_read_memory Ma bt bg br lo hi g).
  { unfold Ma. apply V293_start_alloc_reads;assumption. }
  assert (Input : (ge,le,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (((bh,0%Z),Tint8,oldhigh)::survivors) Atrue).
  { eapply V293_raw_cells_environment;[right;reflexivity | exact Owned]. }
  pose proof (V293_tick_allocate_frame ge le M ir aux O op byblock Tint8 _ Fresh Input) as Alloc.
  change ((ge,le,Ma,ir,aux,O,op) |= V293_rdy_raw_cells
    (((byblock,0%Z),Tint8,Vundef)::((bh,0%Z),Tint8,oldhigh)::survivors) Atrue) in Alloc.
  assert (Gb : g<256).
  { subst g. unfold V293_ready_group. destruct (lo=?0);destruct (hi=?0);lia. }
  destruct (V293_OSSchedNew_row_eval ge le Ma unmap group rows bt bg br lo hi g Env ReadA Gb)
    as [RowVal RowTy].
  assert (Ybound : V293_ready_lookup g<256).
  { pose proof (proj1 (V293_ready_row_spec g Gb));lia. }
  assert (Pbound : V293_ready_select lo hi g<256).
  { pose proof (V293_ready_selection_range lo hi g Lo Hi Group Nonempty);lia. }
  pose proof (V293_start_byte_owned nil byblock Vundef
    (((bh,0%Z),Tint8,oldhigh)::survivors) (V293_ready_lookup g) Atrue
    ge le Ma ir aux O op Ybound Alloc) as One.
  set (M1:=V293_write_byte Ma byblock (V293_ready_lookup g)).
  change ((ge,le,M1,ir,aux,O,op) |= V293_rdy_raw_cells
    (((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup g))::
     ((bh,0%Z),Tint8,oldhigh)::survivors) Atrue) in One.
  pose proof (V293_start_byte_owned
    (cons ((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup g)) nil)
    bh oldhigh survivors (V293_ready_select lo hi g) Atrue
    ge le M1 ir aux O op Pbound One) as Two.
  set (Ms:=V293_write_byte M1 bh (V293_ready_select lo hi g)).
  change ((ge,le,Ms,ir,aux,O,op) |= V293_rdy_raw_cells
    (((byblock,0%Z),Tint8,V293_byteval (V293_ready_lookup g))::
     ((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi g))::survivors) Atrue) in Two.
  assert (Layout : getaddr le=(cons (byblock,Tint8) nil)).
  { unfold le. reflexivity. }
  destruct (V293_tick_raw_owned_writable bh Tint8 oldhigh _ _ _ _ _ _ _ _ Input 0 ltac:(cbn;lia)) as [oldbyte HighByte].
  set (body:=V293_OSSchedNew_body unmap group rows high y).
  destruct (V293_tick_void_return P (kcall f body caller ks) ge le caller Ms f body ks)
    as (Mf&Return&Preserve&Removed).
  - reflexivity.
  - rewrite Layout. repeat constructor;cbn;tauto.
  - intros b t Member. rewrite Layout in Member. destruct Member as [E|E];[inversion E;subst|contradiction].
    eapply V293_tick_raw_owned_writable. exact Two.
  - exists Mf. split.
    + eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply snpcall_step]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity| ]. eapply sfexec_step with (d1:=dnil) (d2:=dcons y Tint8 dnil);
        [reflexivity|reflexivity|exact Program|exact I|reflexivity]. }
      eapply c_stepstarn.
      { eapply stmt_step;[reflexivity| ]. eapply salloclv_step;[reflexivity|reflexivity| ].
        exists byblock. repeat split;try assumption;try reflexivity.
        intros [v E]. rewrite map_emp_get in E;discriminate. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity|apply sallocend_step]. }
      unfold V293_OSSchedNew_body.
      eapply c_stepstarn. { eapply stmt_step;[reflexivity|constructor]. }
      eapply V293_cstepstar_trans.
      { eapply V293_OSSchedNew_updates_execution;
          try eassumption;try reflexivity.
        - unfold Ma. cbn [allocb]. apply map_get_set.
        - unfold Ma. rewrite V293_success_allocb_outside by (left;congruence). exact HighByte. }
      eapply c_stepstarn. { eapply stmt_step;[reflexivity|constructor]. }
      exact Return.
    + split.
      * eapply V293_raw_cells_return_many with (M:=Ms) (le:=le) (R:=Atrue) (freed:=cons byblock nil).
        -- intros a tp v Member. cbn in Member. destruct Member as [E|Member].
           ++ inversion E;subst. cbn. intro Bad. destruct Bad as [Bad|Bad];[apply Dh;congruence|contradiction].
           ++ cbn. intros [Bad|Bad];[apply (Away a tp v Member);symmetry;exact Bad|contradiction].
        -- intros c i Outside. apply Preserve. rewrite Layout. exact Outside.
        -- change ((ge,le,Ms,ir,aux,O,op) |=
             Amapsto (byblock,0%Z) Tint8 true (V293_byteval (V293_ready_lookup g)) **
             V293_rdy_raw_cells (((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi g))::survivors) Atrue) in Two.
           apply V293_raw_cells_absorb in Two. exact Two.
      * apply (Removed byblock Tint8 0);[rewrite Layout;left;reflexivity|cbn;lia].
Qed.
Print Assumptions V293_OSSchedNew_startup_call.

(* The fresh block is chosen from the actual bounded memory, not supplied by
   a caller or predicted before the preceding initialization call. *)
Theorem V293_OSSchedNew_startup_fresh_call : forall survivors P ks ge caller M ir aux O op
    f unmap group rows high y bt bg br bh lo hi g oldhigh,
  P f=Some (V293_OSSchedNew_function unmap group rows high y) ->
  y<>unmap -> y<>group -> y<>rows -> y<>high ->
  get ge unmap=Some (bt,Tarray Tint8 256) ->
  get ge group=Some (bg,Tint8) -> get ge rows=Some (br,Tarray Tint8 2) ->
  get ge high=Some (bh,Tint8) ->
  lo<256 -> hi<256 -> g=V293_ready_group lo hi -> (exists p,V293_bitmap_ready lo hi p) ->
  V293_sched_read_memory M bt bg br lo hi g ->
  (ge,caller,M,ir,aux,O,op) |=
    V293_rdy_raw_cells (((bh,0%Z),Tint8,oldhigh)::survivors) Atrue ->
  exists Mf,
    cstepstar P (curs (scall f nil),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |= V293_rdy_raw_cells
      (((bh,0%Z),Tint8,V293_byteval (V293_ready_select lo hi g))::survivors) Atrue.
Proof.
  intros survivors P ks ge caller M ir aux O op f unmap group rows high y bt bg br bh lo hi g oldhigh
    Program Nt Ng Nr Nh Gt Gg Gr Gh Lo Hi Group Nonempty Reads Owned.
  destruct (V293_init_fresh_four M
    (((bt,0%Z),Tint8,Vundef)::((bg,0%Z),Tint8,Vundef)::
     ((br,0%Z),Tint8,Vundef)::((bh,0%Z),Tint8,Vundef)::survivors))
    as (b&bn&b1&b2&ND&Fresh&Fn&F1&F2&Away).
  assert (Different : b<>bt /\ b<>bg /\ b<>br /\ b<>bh).
  { repeat split;intro E;subst b.
    - apply (Away (bt,0%Z) Tint8 Vundef);cbn;tauto.
    - apply (Away (bg,0%Z) Tint8 Vundef);cbn;tauto.
    - apply (Away (br,0%Z) Tint8 Vundef);cbn;tauto.
    - apply (Away (bh,0%Z) Tint8 Vundef);cbn;tauto. }
  destruct Different as (Dt&Dg&Dr&Dh).
  destruct (V293_OSSchedNew_startup_call survivors P ks ge caller M ir aux O op
    f unmap group rows high y bt bg br bh b lo hi g oldhigh)
    as (Mf&Exec&Final&Removed);try assumption.
  - intros a tp v Member E. apply (Away a tp v);[cbn;tauto| ].
    unfold V293_tcb_call_blocks. cbn. left. symmetry;exact E.
  - exists Mf. split;assumption.
Qed.
Print Assumptions V293_OSSchedNew_startup_fresh_call.
