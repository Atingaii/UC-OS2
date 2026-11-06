(* Actual nonempty OS_TCBInit path, with an explicit OPEN Hoare obligation
   for the unchanged real success suffix. No port implementation or WFIFun. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_success_extra bg bu :=
 Alvarenv 109%Z Tint32 (bu,0%Z) //\\
 Agvarenv 91%Z (Tptr V293_tcb_type) (bg,0%Z) //\\ A_notin_lenv 91%Z.
Definition V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo :=
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo **
 V293_tcb_success_extra bg bu.
Definition V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next :=
 ((bu,0%Z),Tint32,cpu)::
 (fields ++ V293_tcb_prefix_inputs bc bp bs bb bi bz be bo pc p top bottom identity size ext options ++
 V293_tcb_prefix_links bg bt base head next).
Definition V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields pc cpu head next R aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells
 (V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base
  p top bottom identity size ext options fields pc cpu head next)
 (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R)).

Lemma V293_raw_cells_unmove_frame : forall cells A B,
 A ** V293_rdy_raw_cells cells B ==> V293_rdy_raw_cells cells (A ** B).
Proof.
 induction cells as [ | [[a tp] v] cells IH];intros A B s HS;cbn [V293_rdy_raw_cells] in *.
 - exact HS.
 - eapply astar_mono;[intros st H;exact H|apply IH| ]. clear -HS. sep auto.
Qed.
Lemma V293_raw_cells_good_frame : forall cells R,
 GoodFrm R -> GoodFrm (V293_rdy_raw_cells cells R).
Proof.
 induction cells as [ | [[a tp] v] cells IH];intros R HR;cbn [V293_rdy_raw_cells GoodFrm].
 - exact HR.
 - split;[exact I|apply IH;exact HR].
Qed.
Lemma V293_tcb_success_bindings_good : forall bg bu bc bp bs bb bi bz be bo,
 GoodFrm (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo).
Proof. intros. cbn [V293_tcb_success_bindings V293_tcb_success_extra V293_tcb_fields_bindings GoodFrm]. tauto. Qed.
Lemma V293_tcb_success_raw_env : forall cells bg bu bc bp bs bb bi bz be bo R isr is cs s,
 s |= V293_rdy_raw_cells cells
 (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R)) ->
 V293_tcb_init_env (getlenv s) 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo /\ get (getlenv s) 109%Z=Some(bu,Tint32) /\ get (getlenv s) 91%Z=None /\ get (getgenv s) 91%Z=Some(bg,Tptr V293_tcb_type).
Proof.
 intros cells bg bu bc bp bs bb bi bz be bo R isr is cs s HS.
 eapply V293_raw_cells_frame_env with (E:=fun ge le =>
 V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo /\ get le 109%Z=Some(bu,Tint32) /\ get le 91%Z=None /\ get ge 91%Z=Some(bg,Tptr V293_tcb_type));[ |exact HS].
 intros st H.
 refine (V293_star_env_r _ _ (fun ge le =>
 V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo /\ get le 109%Z=Some(bu,Tint32) /\ get le 91%Z=None /\ get ge 91%Z=Some(bg,Tptr V293_tcb_type)) _ st H).
 intros st1 H1.
 refine (V293_star_env_l _ _ (fun ge le =>
 V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo /\ get le 109%Z=Some(bu,Tint32) /\ get le 91%Z=None /\ get ge 91%Z=Some(bg,Tptr V293_tcb_type)) _ st1 H1).
 intros st2 H2. unfold V293_tcb_success_bindings in H2. split.
 - refine (V293_star_env_l _ _ (fun ge le => V293_tcb_init_env le 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo) _ st2 H2).
   intros st3 H3. apply V293_tcb_fields_bindings_env;exact H3.
 - refine (V293_star_env_r _ _ (fun ge le => get le 109%Z=Some(bu,Tint32) /\ get le 91%Z=None /\ get ge 91%Z=Some(bg,Tptr V293_tcb_type)) _ st2 H2).
   intros st3 H3. unfold V293_tcb_success_extra in H3. destruct H3 as [CPU [Global [NotLocal Empty]]].
   destruct CPU as [b [E [B _]]]. inversion B;subst b.
   destruct Global as [g [G [BG _]]]. inversion BG;subst g.
   repeat split;try assumption.
   destruct (get (getlenv st3) 91%Z) eqn:N;[ |reflexivity]. exfalso. apply NotLocal. exists p. exact N.
Qed.

Lemma V293_tcb_success_enter : forall Spec sd li I r ri tid aop cells bg bu bc bp bs bb bi bz be bo R isr is cs,
 GoodFrm R ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells cells
  (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R)))
 (sprim encrit)
 (<||aop||> ** V293_rdy_raw_cells cells
  (OS[isr,false,is,false::cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R))) tid.
Proof.
 intros. eapply conseq_rule.
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_unmove_frame].
 - apply encrit2_rule. apply V293_raw_cells_good_frame.
   cbn [GoodFrm]. split;[apply V293_tcb_success_bindings_good|assumption].
Qed.
Lemma V293_tcb_success_exit : forall Spec sd li I r ri tid aop cells bg bu bc bp bs bb bi bz be bo R isr is cs,
 GoodFrm R ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells cells
  (OS[isr,false,is,false::cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R)))
 (sprim excrit)
 (<||aop||> ** V293_rdy_raw_cells cells
  (OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** R))) tid.
Proof.
 intros. eapply conseq_rule.
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_move_frame].
 - apply astar_mono;[intros s HS;exact HS|apply V293_raw_cells_unmove_frame].
 - apply excrit2_rule. apply V293_raw_cells_good_frame.
   cbn [GoodFrm]. split;[apply V293_tcb_success_bindings_good|assumption].
Qed.

Ltac V293_success_store n rt value :=
 lazymatch goal with
 | |- InfRules ?Spec ?sd ?li ?I ?r ?ri (<||?aop||> ** V293_rdy_raw_cells ?cells ?R) ?stmt ?q ?tid =>
   let before := eval cbn in (firstn n cells) in
   let cell := eval cbn in (nth n cells ((1%positive,0%Z),Tint8,Vundef)) in
   let after := eval cbn in (skipn (S n) cells) in
   lazymatch cell with (?a,?tp,?old) =>
    eapply (V293_raw_assign_hoare Spec sd li I r ri tid aop before a tp old after value _ _ rt R);
    [reflexivity |
     first [solve [apply eq_int;auto] | solve [apply eq_vptr;do 2 eexists;split;reflexivity] |
       solve [apply eq_vcomptr;split;left;eexists;reflexivity]] |
     |repeat apply V293_star_CurLINV_r;assumption]
   end
 end.
Ltac V293_success_env Owned :=
 pose proof (V293_tcb_success_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Owned) as Env;
 destruct Env as ((Bc&Bp&Bs&Bb&Bi&Bz&Be&Bo)&Bu&N&G);
 cbn [getlenv getgenv get_smem get_lenv get_genv] in *.

Lemma V293_tcb_success_cpu_hoare : forall Spec sd li I r ri tid aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu head next isr is cs,
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) pc cpu head next R aop isr is cs)
 (sassign (evar 109%Z) (econst32 Int.zero))
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) pc (Vint32 Int.zero) head next R aop isr is cs) tid.
Proof.
 intros. unfold V293_tcb_success_state,V293_tcb_success_cells,V293_tcb_init_old_fields,
 V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links. cbn [app tl].
 V293_success_store 0 Tint32 (Vint32 Int.zero).
 intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_success_env Owned.
 cbn [sat getsmem evaladdr evaltype evalval get_smem get_lenv].
 cbv delta [env var memory.ident Modules.ident] in *. rewrite Bu.
 repeat split;try reflexivity;discriminate.
Qed.
Lemma V293_tcb_success_pointer_hoare : forall Spec sd li I r ri tid aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu next isr is cs,
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next R aop isr is cs)
 (sassign (evar 108%Z) (evar 91%Z))
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu (Vptr(bt,Int.repr base)) next R aop isr is cs) tid.
Proof.
 intros. unfold V293_tcb_success_state,V293_tcb_success_cells,V293_tcb_init_old_fields,
 V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links. cbn [app tl].
 V293_success_store 19 (Tptr V293_tcb_type) (Vptr(bt,Int.repr base)).
 intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_success_env Owned.
 V293_tcb_init_read Owned 27 HeadRead.
 split.
 - cbn [sat getsmem evaladdr evaltype get_smem get_lenv].
   cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc. auto.
 - cbn [sat getsmem get_smem]. repeat split;first [solve [V293_rdy_eval]|discriminate].
Qed.
Lemma V293_tcb_success_pop_hoare : forall Spec sd li I r ri tid aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu next isr is cs,
 (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 rule_type_val_match (Tptr V293_tcb_type) next=true -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu (Vptr(bt,Int.repr base)) next R aop isr is cs)
 (V293_TCBInit_pop 91%Z 108%Z)
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu next next R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid aop R bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu next isr is cs Base Bound Next HR.
 unfold V293_tcb_success_state,V293_tcb_success_cells,V293_tcb_init_old_fields,
 V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links,V293_TCBInit_pop. cbn [app tl].
 V293_success_store 27 (Tcom_ptr 410%Z) next.
 intros s Owned. destruct s as [[[[[[ge le] M] ir] aux] O] op]. V293_success_env Owned.
 V293_tcb_init_read Owned 19 PRead.
 V293_tcb_init_read Owned 28 NextRead.
 destruct (V293_tcb_init_field_address ge le M 108%Z bc bt base 7%Z 20%Z (Tcom_ptr 410%Z)
 Bc PRead ltac:(reflexivity) ltac:(reflexivity) Base ltac:(lia) ltac:(lia)) as [NT NA].
 split.
 - cbn [sat getsmem evaladdr evaltype get_smem get_lenv get_genv].
   cbv delta [env var memory.ident Modules.ident] in *. rewrite N,G. auto.
 - cbn [sat getsmem get_smem]. split.
   + cbn [evaladdr evalval evaltype get_lenv get_genv get_mem].
     cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
     cbn beta iota. rewrite PRead. unfold getoff.
     cbn [evaltype get_lenv get_genv]. cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc.
     cbn [V293_tcb_type V293_tcb_fields field_offset addrval_to_addr].
     rewrite Int.repr_unsigned. unfold Int.add. rewrite (Int.unsigned_repr base) by lia.
     change (load (Tcom_ptr 410%Z) M (bt,Int.unsigned(Int.repr(base+20)))=Some next).
     rewrite Int.unsigned_repr by lia. exact NextRead.
   + split;[exact NT|eapply V293_typed_not_undef;exact Next].
Qed.

Definition V293_tcb_success_fields_frame bg bu bt base cpu head next R isr is cs :=
 Amapsto (bu,0%Z) Tint32 true cpu **
 V293_rdy_raw_cells (V293_tcb_prefix_links bg bt base head next)
 (OS[isr,false,is,cs] ** (V293_tcb_success_extra bg bu ** R)).
Lemma V293_tcb_success_fields_view : forall bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options fields cpu head next R aop isr is cs s,
 (s |= V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  fields (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) <->
 (s |= <||aop||> ** V293_rdy_raw_cells
  (fields++V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
  (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bc bp bs bb bi bz be bo **
   V293_tcb_success_fields_frame bg bu bt base cpu head next R isr is cs)).
Proof.
 intros. unfold V293_tcb_success_state,V293_tcb_success_cells.
 change (V293_tcb_prefix_inputs bc bp bs bb bi bz be bo (Vptr(bt,Int.repr base)) p top bottom identity size ext options)
 with (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options).
 rewrite app_assoc. cbn [V293_rdy_raw_cells]. rewrite V293_raw_cells_append.
 split;intro HS.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   intros st H. apply V293_raw_cells_unmove_frame in H.
   eapply V293_raw_cells_mono;[ |exact H]. intros st0 H0.
   unfold V293_tcb_success_fields_frame,V293_tcb_success_bindings,V293_tcb_prefix_links in *.
   cbn [V293_rdy_raw_cells] in *. clear -H0. sep auto.
 - eapply astar_mono;[intros st H;exact H| |exact HS].
   intros st H. apply V293_raw_cells_move_frame.
   eapply V293_raw_cells_mono;[ |exact H]. intros st0 H0.
   unfold V293_tcb_success_fields_frame,V293_tcb_success_bindings,V293_tcb_prefix_links in *.
   cbn [V293_rdy_raw_cells] in *. clear -H0. sep auto.
Qed.
Lemma V293_tcb_success_fields_hoare : forall Spec sd li I r ri tid aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu head next isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs)
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid aop R bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu head next isr is cs Range Base Bound Valid HR.
 eapply conseq_rule.
 - intros s HS. exact (proj1 (V293_tcb_success_fields_view bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options (V293_tcb_init_old_fields bt base old) cpu head next R aop isr is cs s) HS).
 - intros s HS. exact (proj2 (V293_tcb_success_fields_view bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options (V293_tcb_init_final_fields bt base p top bottom identity size ext options) cpu head next R aop isr is cs s) HS).
 - apply V293_OS_TCBInit_fields_hoare;try assumption.
   unfold V293_tcb_success_fields_frame. apply V293_star_CurLINV_r.
   apply V293_raw_cells_CurLINV. repeat apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_tcb_success_guard_eval : forall bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options old cpu head next R aop isr is cs s,
 s |= V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu head next R aop isr is cs ->
 evalval (eunop oppsite (V293_task_prio_null_test(evar 108%Z))) (getsmem s)=Some(Vint32 Int.one) /\
 evaltype (eunop oppsite (V293_task_prio_null_test(evar 108%Z))) (getsmem s)=Some Tint32.
Proof.
 intros bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu head next R aop isr is cs s HS.
 unfold V293_tcb_success_state in HS.
 assert (Bc:get (getlenv s) 108%Z=Some(bc,Tptr V293_tcb_type)).
 { refine (V293_star_env_r _ _ (fun ge le => get le 108%Z=Some(bc,Tptr V293_tcb_type)) _ s HS).
   intros st H. pose proof (V293_tcb_success_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as ((Bc&_)&_). exact Bc. }
 assert (PRead:load (Tptr V293_tcb_type) (getmem s) (bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { eapply V293_star_load_r;[ |exact HS]. intros st Owned.
   destruct st as [[[[[[ge le] M] ir] aux] O] op].
   unfold V293_tcb_success_cells,V293_tcb_init_old_fields,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,V293_tcb_prefix_links in Owned. cbn [app tl] in Owned.
   V293_tcb_init_read Owned 19 L. exact L. }
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getlenv getmem getsmem get_smem get_lenv get_genv get_mem] in *.
 cbn [V293_task_prio_null_test evalval evaltype get_lenv get_genv get_mem].
 cbv delta [env var memory.ident Modules.ident] in *. rewrite Bc,PRead. split;reflexivity.
Qed.

Theorem V293_OS_TCBInit_pop_fields_hoare : forall Spec sd li I r ri tid aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old cpu next isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) (Vptr(bt,Int.repr base)) cpu (Vptr(bt,Int.repr base)) next R aop isr is (false::cs))
 (sseq (V293_TCBInit_pop 91%Z 108%Z)
  (sseq (sprim excrit) (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)))
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) cpu next next R aop isr is cs) tid.
Proof.
 intros. eapply seq_rule;[apply V293_tcb_success_pop_hoare;assumption| ].
 eapply seq_rule;[unfold V293_tcb_success_state;apply V293_tcb_success_exit;assumption| ].
 apply V293_tcb_success_fields_hoare;assumption.
Qed.

Theorem V293_OS_TCBInit_nonempty_body_with_suffix_hoare : forall Spec sd li I r ri tid hi hc aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu next isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (* OPEN: the two real CPU Hook calls, priority table, publication and return. *)
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
  (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs)
 (V293_TCBInit_success_suffix hi hc) Afalse tid ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next R aop isr is cs)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I r ri tid hi hc aop R bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu next isr is cs Range Base Bound Valid Next Frame HR Suffix.
 unfold V293_TCBInit_function_body. eapply seq_rule;[apply V293_tcb_success_cpu_hoare;exact HR| ].
 unfold V293_TCBInit_prefix. eapply seq_rule.
 - unfold V293_tcb_success_state. apply V293_tcb_success_enter;exact Frame.
 - eapply seq_rule;[apply V293_tcb_success_pointer_hoare;exact HR| ].
   eapply seq_rule with (p':=Afalse).
   + eapply ift_rule with (tp:=Tint32).
     * intros s HS. exists(Vint32 Int.one).
       destruct (V293_tcb_success_guard_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS) as [V T].
       cbn [sat]. split;[exact V| ]. split;[exact T|discriminate].
     * intros s [HS [v [V B]]].
       destruct (V293_tcb_success_guard_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS) as [One _].
       rewrite One in V. inversion V;subst v. discriminate B.
     * eapply conseq_rule.
       -- intros s [HS _]. exact HS.
       -- intros s HS. exact HS.
       -- eapply seq_rule;[apply V293_tcb_success_pop_hoare;assumption| ].
          eapply seq_rule;[unfold V293_tcb_success_state;apply V293_tcb_success_exit;exact Frame| ].
          eapply seq_rule;[apply V293_tcb_success_fields_hoare;assumption|exact Suffix].
   + apply pfalse_rule.
Qed.
Theorem V293_OS_TCBInit_nonempty_body_with_suffix_semantics : forall Spec sd li I r ri tid hi hc aop R
 bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old pc cpu next isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
  (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next R aop isr is cs)
 (V293_TCBInit_success_suffix hi hc) Afalse tid ->
 simulation.RuleSem Spec sd li I r ri
 (V293_tcb_success_state bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
  (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next R aop isr is cs)
 (V293_TCBInit_function_body hi hc) Afalse tid.
Proof. intros. apply RuleSound. apply V293_OS_TCBInit_nonempty_body_with_suffix_hoare;assumption. Qed.
