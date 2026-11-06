(* Direct Hoare proof of the unchanged normalized tick while. The caller
   owns the fields; production IRQ-invariant transfer is not established here. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickIterationHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Both bitmap rows and the untouched priority field are retained. *)
Theorem V293_tick_node_iteration_hoare :
 forall Spec sd li I r ri tid aop R ptcb rows group bc t next bg br g lo hi enabled ir si ci,
 V293_tick_task_valid t -> g<256 -> lo<256 -> hi<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
   (V293_tick_pointer_cell bc (V293_tick_task_pointer t)::
    (V293_tick_task_cells t next ++ V293_tick_bitmap_cells bg br g lo hi)) R)
 (V293_tick_iteration ptcb rows group)
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
   (V293_tick_pointer_cell bc next::
    (V293_tick_task_cells (V293_tick_task_after t) next ++
     V293_tick_bitmap_cells bg br (V293_tick_next_group t g)
       (V293_tick_next_lo t lo) (V293_tick_next_hi t hi))) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc t next bg br g lo hi enabled ir si ci
 Valid G Lo Hi Env HR GF Bound.
 destruct t as [b off d s p y x prio].
 destruct Valid as ([Base Limit] & D & S & Pend & Y & X & Prio & Nonidle).
 cbn in Base,Limit,D,S,Pend,Y,X,Prio,Nonidle.
 assert (Rows:y=0 \/ y=1) by lia. destruct Rows as [Row|Row];subst y.
 - eapply conseq_rule with
    (p:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_expiry_cells bc b off (b,Int.repr off) (Int.repr d) next s p 0 x bg g br lo)
      (Amapsto (b,(off+50)%Z) Tint8 true (V293_byteval prio) **
       (Amapsto (br,1%Z) Tint8 true (V293_byteval hi) ** R)))
    (q:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_expiry_cells bc b off next (Int.repr (V293_tick_after_delay d)) next
       (V293_tick_after_stat d s) (V293_tick_after_pend d p s) 0 x bg
       (V293_tick_after_group d s g 0) br (V293_tick_after_row d s lo x))
      (Amapsto (b,(off+50)%Z) Tint8 true (V293_byteval prio) **
       (Amapsto (br,1%Z) Tint8 true (V293_byteval hi) ** R))).
   + intros st H. cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells
       V293_tick_bitmap_cells V293_tick_expiry_cells V293_rdy_raw_cells app] in H |- *.
     clear -H. sep auto.
   + intros st H. cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells V293_tick_task_after
       V293_tick_bitmap_cells V293_tick_next_group V293_tick_next_lo V293_tick_next_hi
       V293_tick_expiry_cells V293_rdy_raw_cells app].
     cbn [V293_tick_expiry_cells V293_rdy_raw_cells] in H. clear -H. sep auto.
   + apply V293_tick_iteration_hoare;try assumption;try lia.
     * intros st H. eapply V293_star_env_r;[ |exact H]. intros st0 H0.
       eapply V293_star_env_r;[exact Env|exact H0].
     * apply V293_star_CurLINV_r. apply V293_star_CurLINV_r;exact HR.
     * cbn [GoodFrm]. tauto.
 - eapply conseq_rule with
    (p:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_expiry_cells bc b off (b,Int.repr off) (Int.repr d) next s p 1 x bg g br hi)
      (Amapsto (b,(off+50)%Z) Tint8 true (V293_byteval prio) **
       (Amapsto (br,0%Z) Tint8 true (V293_byteval lo) ** R)))
    (q:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
      (V293_tick_expiry_cells bc b off next (Int.repr (V293_tick_after_delay d)) next
       (V293_tick_after_stat d s) (V293_tick_after_pend d p s) 1 x bg
       (V293_tick_after_group d s g 1) br (V293_tick_after_row d s hi x))
      (Amapsto (b,(off+50)%Z) Tint8 true (V293_byteval prio) **
       (Amapsto (br,0%Z) Tint8 true (V293_byteval lo) ** R))).
   + intros st H. cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells
       V293_tick_bitmap_cells V293_tick_expiry_cells V293_rdy_raw_cells app] in H |- *.
     clear -H. sep auto.
   + intros st H. cbn [V293_tick_pointer_cell V293_tick_task_pointer V293_tick_task_cells V293_tick_task_after
       V293_tick_bitmap_cells V293_tick_next_group V293_tick_next_lo V293_tick_next_hi
       V293_tick_expiry_cells V293_rdy_raw_cells app].
     cbn [V293_tick_expiry_cells V293_rdy_raw_cells] in H. clear -H. sep auto.
   + apply V293_tick_iteration_hoare;try assumption;try lia.
     * intros st H. eapply V293_star_env_r;[ |exact H]. intros st0 H0.
       eapply V293_star_env_r;[exact Env|exact H0].
     * apply V293_star_CurLINV_r. apply V293_star_CurLINV_r;exact HR.
     * cbn [GoodFrm]. tauto.
Qed.

Definition V293_tick_while_cells bc processed remaining idle bg br g lo hi :=
 V293_tick_pointer_cell bc (V293_tick_head remaining idle)::
 (processed ++ (V293_tick_chain_cells remaining idle ++
  (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle]))).

(* Guard evaluation is obtained from owned pointer/priority bytes, not supplied
   as a premise. A non-idle valid node is true; the actual idle byte is false. *)
Lemma V293_tick_while_guard_owned : forall processed remaining idle bc bg br g lo hi R ptcb rows group st,
 (forall s, s |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv s) (getlenv s)) ->
 (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid remaining ->
 st |= V293_rdy_raw_cells (V293_tick_while_cells bc processed remaining idle bg br g lo hi) R ->
 st |= Rv (V293_tick_guard ptcb) @ Tint32 ==
  Vint32 (match remaining with []=>Int.zero | _::_=>Int.one end).
Proof.
 intros processed remaining idle bc bg br g lo hi R ptcb rows group st Env IdleLimit Valid Owned.
 destruct st as [[[[[[ge le] M] ir] aux] O] op].
 pose proof (V293_raw_cells_frame_env _ R _ Env _ Owned) as Bindings.
 change (V293_tick_delay_env ptcb rows group bc br bg ge le) in Bindings.
 destruct Bindings as (Bind & Nr & Gr & Ng & Gg).
 assert (Pointer : load (Tptr V293_tcb_type) M (bc,0%Z)=Some(Vptr(V293_tick_head remaining idle))).
 { eapply (V293_rdy_raw_load (V293_tick_while_cells bc processed remaining idle bg br g lo hi) R _ _ _ (ge,le,M,ir,aux,O,op));
   [left;reflexivity|reflexivity|exact Owned]. }
 destruct remaining as [ |t rest].
 - assert (Read:load Tint8 M (fst idle,(Int.unsigned(snd idle)+50)%Z)=Some(V293_byteval 12)).
   { eapply (V293_rdy_raw_load (V293_tick_while_cells bc processed [] idle bg br g lo hi) R _ _ _ (ge,le,M,ir,aux,O,op));
     [unfold V293_tick_while_cells;right;apply in_or_app;right;apply in_or_app;right;
      apply in_or_app;right;left;reflexivity|reflexivity|exact Owned]. }
   cbn [V293_tick_head] in Pointer.
   assert (Normalized:load (Tptr V293_tcb_type) M (bc,0%Z)=
    Some(Vptr(fst idle,Int.repr(Int.unsigned(snd idle))))).
   { rewrite Int.repr_unsigned. destruct idle;exact Pointer. }
   destruct (V293_tick_field_eval ge le M ptcb bc (fst idle) (Int.unsigned(snd idle)) 16%Z 50%Z
     Tint8 (V293_byteval 12) Bind Normalized eq_refl eq_refl (proj1(Int.unsigned_range _))
     ltac:(lia) IdleLimit Read) as [Tp Vp].
   split.
   + exact (V293_tick_guard_eval ge le M ptcb bc (fst idle) (Int.unsigned(snd idle)) 12
       Bind Normalized (proj1(Int.unsigned_range _)) IdleLimit ltac:(lia) Read).
   + split;[ |discriminate]. change(evaltype (V293_tick_guard ptcb) (ge,le,M)=Some Tint32).
     unfold V293_tick_guard,V293_tick_ne,V293_tick_eq. cbn [evaltype]. rewrite Tp. reflexivity.
 - inversion Valid as [ | t0 rest0 Head Tail];subst t0 rest0.
   destruct Head as ([Base Limit] & D & S & Pend & Y & X & Prio & Nonidle).
   assert (Read:load Tint8 M (V293_tick_block t,(V293_tick_base t+50)%Z)=Some(V293_byteval(V293_tick_prio t))).
   { eapply (V293_rdy_raw_load (V293_tick_while_cells bc processed (t::rest) idle bg br g lo hi) R _ _ _ (ge,le,M,ir,aux,O,op));
     [unfold V293_tick_while_cells;right;apply in_or_app;right;apply in_or_app;left;
      cbn [V293_tick_chain_cells];apply in_or_app;left;unfold V293_tick_task_cells;cbn;tauto|
      apply V293_byte_type;exact Prio|exact Owned]. }
   cbn [V293_tick_head V293_tick_task_pointer] in Pointer.
   destruct (V293_tick_field_eval ge le M ptcb bc (V293_tick_block t) (V293_tick_base t) 16%Z 50%Z
     Tint8 _ Bind Pointer eq_refl eq_refl Base ltac:(lia) ltac:(lia) Read) as [Tp Vp].
   pose proof (V293_tick_guard_eval ge le M ptcb bc (V293_tick_block t) (V293_tick_base t)
     (V293_tick_prio t) Bind Pointer Base ltac:(lia) Prio Read) as Guard.
   rewrite (proj2(Nat.eqb_neq _ _) Nonidle) in Guard.
   split;[exact Guard| ].
   split;[ |discriminate]. change(evaltype (V293_tick_guard ptcb) (ge,le,M)=Some Tint32).
     unfold V293_tick_guard,V293_tick_ne,V293_tick_eq. cbn [evaltype]. rewrite Tp. reflexivity.
Qed.

Local Lemma tick_focus_order : forall (a b c d e:list V293_record_cell),
 Permutation (a++b++c++d++e) (b++d++a++c++e).
Proof.
 intros a b c d e.
 eapply Permutation_trans with (l':=b++a++c++d++e).
 - apply Permutation_app_swap_app.
 - apply Permutation_app_head.
   eapply Permutation_trans with (l':=a++d++c++e).
   + apply Permutation_app_head. apply Permutation_app_swap_app.
   + apply Permutation_app_swap_app.
Qed.

(* One step of the loop invariant, retaining the exact processed prefix. *)
Lemma V293_tick_while_step_hoare :
 forall Spec sd li I r ri tid aop R ptcb rows group bc processed t rest idle bg br g lo hi enabled ir si ci,
 V293_tick_task_valid t -> g<256 -> lo<256 -> hi<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 InfRules Spec sd li I r ri
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
   (V293_tick_while_cells bc processed (t::rest) idle bg br g lo hi) R)
 (V293_tick_iteration ptcb rows group)
 (<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
   (V293_tick_while_cells bc (processed++V293_tick_task_cells (V293_tick_task_after t)
      (V293_tick_head rest idle)) rest idle bg br (V293_tick_next_group t g)
      (V293_tick_next_lo t lo) (V293_tick_next_hi t hi)) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc processed t rest idle bg br g lo hi enabled ir si ci
 Valid G Lo Hi Env HR GF Bound.
 set (frame:=V293_rdy_raw_cells (processed++V293_tick_chain_cells rest idle++[V293_tick_idle_cell idle]) R).
 eapply conseq_rule with
  (p:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
    (V293_tick_pointer_cell bc (V293_tick_task_pointer t)::
     (V293_tick_task_cells t (V293_tick_head rest idle) ++ V293_tick_bitmap_cells bg br g lo hi)) frame)
  (q:=<||aop||> ** OS[ir,enabled,si,ci] ** V293_rdy_raw_cells
    (V293_tick_pointer_cell bc (V293_tick_head rest idle)::
     (V293_tick_task_cells (V293_tick_task_after t) (V293_tick_head rest idle) ++
      V293_tick_bitmap_cells bg br (V293_tick_next_group t g)
        (V293_tick_next_lo t lo) (V293_tick_next_hi t hi))) frame).
 - apply astar_mono;[intros st H;exact H| ]. apply astar_mono;[intros st H;exact H| ].
   unfold frame,V293_tick_while_cells. cbn [V293_tick_chain_cells V293_tick_head].
   rewrite <-V293_raw_cells_append. cbn [V293_rdy_raw_cells].
   apply astar_mono;[intros st H;exact H| ].
   repeat rewrite <-V293_raw_cells_append. apply V293_raw_cells_permutation. repeat rewrite <-app_assoc. apply tick_focus_order.
 - apply astar_mono;[intros st H;exact H| ]. apply astar_mono;[intros st H;exact H| ].
   unfold frame,V293_tick_while_cells.
   repeat rewrite <-V293_raw_cells_append. cbn [V293_rdy_raw_cells].
   apply astar_mono;[intros st H;exact H| ].
   repeat rewrite <-app_assoc. apply V293_raw_cells_permutation. apply Permutation_sym. apply tick_focus_order.
 - apply V293_tick_node_iteration_hoare;try assumption.
   + intros st H. eapply V293_raw_cells_frame_env;[exact Env|exact H].
   + apply V293_raw_cells_CurLINV;exact HR.
   + apply V293_raw_cells_good_frame;exact GF.
Qed.

Definition V293_tick_while_resource aop ir enabled si ci bc processed remaining idle bg br g lo hi R :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 V293_rdy_raw_cells (V293_tick_while_cells bc processed remaining idle bg br g lo hi) R.

Lemma V293_tick_while_guard_resource : forall aop ir enabled si ci bc processed remaining idle bg br g lo hi R ptcb rows group,
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid remaining ->
 V293_tick_while_resource aop ir enabled si ci bc processed remaining idle bg br g lo hi R ==>
 Rv (V293_tick_guard ptcb) @ Tint32 == Vint32 (match remaining with []=>Int.zero|_::_=>Int.one end).
Proof.
 intros aop ir enabled si ci bc processed remaining idle bg br g lo hi R ptcb rows group Env Limit Valid st H.
 assert(Work:st |= V293_rdy_raw_cells (V293_tick_while_cells bc processed remaining idle bg br g lo hi)
   ((<||aop||> ** OS[ir,enabled,si,ci]) ** R)).
 { apply V293_raw_cells_unmove_frame. unfold V293_tick_while_resource in H. clear -H. sep auto. }
 eapply V293_tick_while_guard_owned;[ |exact Limit|exact Valid|exact Work].
 intros s HS. eapply V293_star_env_r;[exact Env|exact HS].
Qed.

(* Exact end-state equations replace an independent execution oracle. The
   remaining fold and updated-chain suffix are already-defined functions. *)
Definition V293_tick_while_invariant finalcells finalbitmap aop ir enabled si ci bc idle bg br R :=
 EX processed:list V293_record_cell, EX remaining:list V293_tick_task,
 EX g:nat, EX lo:nat, EX hi:nat,
 V293_tick_while_resource aop ir enabled si ci bc processed remaining idle bg br g lo hi R **
 [| Forall V293_tick_task_valid remaining /\ g<256 /\ lo<256 /\ hi<256 /\
    finalcells=processed++V293_tick_chain_cells (map V293_tick_task_after remaining) idle /\
    finalbitmap=V293_tick_chain_bitmap remaining g lo hi |].

Theorem V293_tick_while_hoare :
 forall Spec sd li I r ri tid aop R ptcb rows group bc tasks idle bg br g lo hi enabled ir si ci,
 (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid tasks -> g<256 -> lo<256 -> hi<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 let '(gf,(lof,hif)):=V293_tick_chain_bitmap tasks g lo hi in
 InfRules Spec sd li I r ri
 (V293_tick_while_resource aop ir enabled si ci bc [] tasks idle bg br g lo hi R)
 (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group))
 (V293_tick_while_resource aop ir enabled si ci bc
    (V293_tick_chain_cells (map V293_tick_task_after tasks) idle) [] idle bg br gf lof hif R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group bc tasks idle bg br g lo hi enabled ir si ci
 IdleLimit Valid G Lo Hi Env HR GF Bound.
 destruct (V293_tick_chain_bitmap tasks g lo hi) as [gf [lof hif]] eqn:FinalBitmap.
 set (finalcells:=V293_tick_chain_cells (map V293_tick_task_after tasks) idle).
 set (inv:=V293_tick_while_invariant finalcells (gf,(lof,hif)) aop ir enabled si ci bc idle bg br R).
 assert(Guard:forall processed remaining g0 lo0 hi0,
  Forall V293_tick_task_valid remaining ->
  V293_tick_while_resource aop ir enabled si ci bc processed remaining idle bg br g0 lo0 hi0 R ==>
  Rv (V293_tick_guard ptcb) @ Tint32 == Vint32 (match remaining with []=>Int.zero|_::_=>Int.one end)).
 { intros. eapply V293_tick_while_guard_resource;eassumption. }
 eapply conseq_rule with (p:=inv) (q:=inv //\\ Aisfalse (V293_tick_guard ptcb)).
 - intros st H. unfold inv,V293_tick_while_invariant.
   exists (@nil V293_record_cell). exists tasks. exists g. exists lo. exists hi.
   apply astar_comm. apply astar_l_apure_intro;[exact H| ].
   repeat split;try assumption. symmetry;exact FinalBitmap.
 - intros st [InvH [v [Eval FalseGuard]]].
   unfold inv,V293_tick_while_invariant in InvH.
   destruct InvH as (processed & remaining & g0 & lo0 & hi0 & Owned).
   apply astar_comm in Owned. apply astar_l_apure_elim in Owned.
   destruct Owned as [[V [G0 [Lo0 [Hi0 [Cells Bitmap]]]]] Owned].
   destruct (Guard processed remaining g0 lo0 hi0 V st Owned) as [E _].
   destruct remaining as [ |t rest].
   + cbn [V293_tick_chain_bitmap] in Bitmap. inversion Bitmap;subst g0 lo0 hi0.
     cbn [map V293_tick_chain_cells app_nil_r] in Cells. rewrite app_nil_r in Cells. subst processed.
     exact Owned.
   + rewrite E in Eval. inversion Eval;subst v. discriminate FalseGuard.
 - apply while_rule with (tp:=Tint32).
   + intros st H. unfold inv,V293_tick_while_invariant in H.
     destruct H as (processed & remaining & g0 & lo0 & hi0 & Owned).
     apply astar_comm in Owned. apply astar_l_apure_elim in Owned.
     destruct Owned as [[V Rest] Owned].
     exists (Vint32 (match remaining with []=>Int.zero|_::_=>Int.one end)).
     exact (Guard processed remaining g0 lo0 hi0 V st Owned).
   + eapply conseq_rule with
      (p:=EX processed:list V293_record_cell, EX remaining:list V293_tick_task,
       EX g0:nat, EX lo0:nat, EX hi0:nat,
       (V293_tick_while_resource aop ir enabled si ci bc processed remaining idle bg br g0 lo0 hi0 R
        //\\ Aistrue (V293_tick_guard ptcb)) **
       [| Forall V293_tick_task_valid remaining /\ g0<256 /\ lo0<256 /\ hi0<256 /\
         finalcells=processed++V293_tick_chain_cells (map V293_tick_task_after remaining) idle /\
         (gf,(lof,hif))=V293_tick_chain_bitmap remaining g0 lo0 hi0 |]) (q:=inv).
     * intros st [H TrueGuard]. unfold inv,V293_tick_while_invariant in H.
       destruct H as (processed & remaining & g0 & lo0 & hi0 & Owned).
       apply astar_comm in Owned. apply astar_l_apure_elim in Owned. destruct Owned as [WF Owned].
       exists processed. exists remaining. exists g0. exists lo0. exists hi0.
       apply astar_comm. apply astar_l_apure_intro;[split;assumption|exact WF].
     * intros st H;exact H.
     * apply ex_intro_rule. intros processed. apply ex_intro_rule. intros remaining.
       apply ex_intro_rule. intros g0. apply ex_intro_rule. intros lo0. apply ex_intro_rule. intros hi0.
       apply pure_split_rule. intros (V & G0 & Lo0 & Hi0 & Cells & Bitmap).
       destruct remaining as [ |t rest].
       -- eapply conseq_rule with (p:=Afalse);[ |intros st H;exact H|apply pfalse_rule].
          intros st [Owned [v [Eval TrueGuard]]].
          destruct (Guard processed [] g0 lo0 hi0 V st Owned) as [E _].
          rewrite E in Eval. inversion Eval;subst v. discriminate TrueGuard.
       -- inversion V as [ |t0 rest0 Head Tail];subst t0 rest0.
          eapply conseq_rule with
           (p:=V293_tick_while_resource aop ir enabled si ci bc processed (t::rest) idle bg br g0 lo0 hi0 R)
           (q:=V293_tick_while_resource aop ir enabled si ci bc
              (processed++V293_tick_task_cells (V293_tick_task_after t) (V293_tick_head rest idle))
              rest idle bg br (V293_tick_next_group t g0) (V293_tick_next_lo t lo0) (V293_tick_next_hi t hi0) R).
          ++ intros st [H _];exact H.
          ++ intros st H. unfold inv,V293_tick_while_invariant.
             exists (processed++V293_tick_task_cells (V293_tick_task_after t) (V293_tick_head rest idle)).
             exists rest. exists (V293_tick_next_group t g0).
             exists (V293_tick_next_lo t lo0). exists (V293_tick_next_hi t hi0).
             apply astar_comm. apply astar_l_apure_intro;[exact H| ].
             destruct (V293_tick_next_bitmap_bounds t g0 lo0 hi0 Head G0 Lo0 Hi0) as [GN [LN HN]].
             repeat split;try assumption.
             ** cbn [map V293_tick_chain_cells] in Cells. rewrite V293_tick_head_after in Cells.
                rewrite <-app_assoc. exact Cells.
          ++ unfold V293_tick_while_resource. apply V293_tick_while_step_hoare;assumption.
Qed.

Theorem V293_tick_while_semantics :
 forall Spec sd li I r ri tid aop R ptcb rows group bc tasks idle bg br g lo hi enabled ir si ci,
 (Int.unsigned (snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid tasks -> g<256 -> lo<256 -> hi<256 ->
 (forall st, st |= R -> V293_tick_delay_env ptcb rows group bc br bg (getgenv st) (getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 let '(gf,(lof,hif)):=V293_tick_chain_bitmap tasks g lo hi in
 simulation.RuleSem Spec sd li I r ri
 (V293_tick_while_resource aop ir enabled si ci bc [] tasks idle bg br g lo hi R)
 (swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group))
 (V293_tick_while_resource aop ir enabled si ci bc
   (V293_tick_chain_cells (map V293_tick_task_after tasks) idle) [] idle bg br gf lof hif R) tid.
Proof.
 intros. destruct (V293_tick_chain_bitmap tasks g lo hi) as [gf [lof hif]] eqn:Bitmap.
 apply RuleSound. pose proof (V293_tick_while_hoare Spec sd li I r ri tid aop R ptcb rows group
   bc tasks idle bg br g lo hi enabled ir si ci H H0 H1 H2 H3 H4 H5 H6 H7) as Rules.
 rewrite Bitmap in Rules. exact Rules.
Qed.

Print Assumptions V293_tick_node_iteration_hoare.
Print Assumptions V293_tick_while_guard_owned.
Print Assumptions V293_tick_while_step_hoare.
Print Assumptions V293_tick_while_guard_resource.
Print Assumptions V293_tick_while_hoare.
Print Assumptions V293_tick_while_semantics.
