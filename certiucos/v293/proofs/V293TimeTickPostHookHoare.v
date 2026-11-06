(* Direct Hoare connection for the unchanged post-hook suffix. The caller owns
   all raw fields; hook execution and production IRQ ownership remain open. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
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

Definition V293_tick_post_globals bn tick bu run bh head : list V293_record_cell :=
 [((bn,0%Z),Tint32,Vint32 tick);((bu,0%Z),Tint8,V293_byteval run);
  ((bh,0%Z),Tptr V293_tcb_type,Vptr head)].
Definition V293_tick_post_cells bn tick bu run bh head bc scan tasks idle bg br g lo hi :=
 V293_tick_post_globals bn tick bu run bh head ++
 (V293_tick_pointer_cell bc scan ::
  (V293_tick_chain_cells tasks idle ++ (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle]))).
Definition V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh ge le :=
 V293_tick_delay_env ptcb rows group bc br bg ge le /\
 (get le now=None /\ get ge now=Some(bn,Tint32)) /\
 (get le running=None /\ get ge running=Some(bu,Tint8)) /\
 (get le head=None /\ get ge head=Some(bh,Tptr V293_tcb_type)).

Lemma V293_tick_clock_assign_hoare : forall Spec sd li I r ri tid aop R before after now bn tick,
 (forall st, st |= R -> get (getlenv st) now=None /\ get (getgenv st) now=Some(bn,Tint32)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells (before++((bn,0%Z),Tint32,Vint32 tick)::after) R)
 (sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one)))
 (<||aop||> ** V293_rdy_raw_cells (before++((bn,0%Z),Tint32,Vint32(Int.add tick Int.one))::after) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R before after now bn tick Env HR.
 eapply V293_raw_assign_hoare with (rt:=Tint32);[reflexivity|apply eq_int;tauto| |exact HR].
 intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
 pose proof (V293_raw_cells_frame_env _ R (fun ge le=>get le now=None /\ get ge now=Some(bn,Tint32)) Env _ Owned) as Bindings.
 change (get le now=None /\ get ge now=Some(bn,Tint32)) in Bindings.
 destruct Bindings as [N B].
 assert(Read:load Tint32 M (bn,0%Z)=Some(Vint32 tick)).
 { eapply (V293_rdy_raw_load (before++((bn,0%Z),Tint32,Vint32 tick)::after) R
     (bn,0%Z) Tint32 (Vint32 tick) (ge,le,M,ir,aux,O,op));
   [apply in_or_app;right;left;reflexivity|reflexivity|exact Owned]. }
 cbn [sat getsmem get_smem evaltype evaladdr get_lenv get_genv]. rewrite N,B.
 repeat split;try reflexivity;try discriminate.
 cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite N,B.
 cbn -[load]. rewrite Read. reflexivity.
Qed.

Lemma V293_tick_head_assign_hoare : forall Spec sd li I r ri tid aop R prefix rest ptcb head bc bh scan first,
 In ((bh,0%Z),Tptr V293_tcb_type,Vptr first) (prefix++rest) ->
 (forall st, st |= R -> get (getlenv st) ptcb=Some(bc,Tptr V293_tcb_type) /\
  get (getlenv st) head=None /\ get (getgenv st) head=Some(bh,Tptr V293_tcb_type)) ->
 (R ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (<||aop||> ** V293_rdy_raw_cells (prefix++V293_tick_pointer_cell bc scan::rest) R)
 (sassign (evar ptcb) (evar head))
 (<||aop||> ** V293_rdy_raw_cells (prefix++V293_tick_pointer_cell bc first::rest) R) tid.
Proof.
 intros Spec sd li I r ri tid aop R prefix rest ptcb head bc bh scan first Member Env HR.
 unfold V293_tick_pointer_cell.
 eapply V293_raw_assign_hoare with (rt:=Tptr V293_tcb_type);
 [reflexivity|apply eq_vptr;exists V293_tcb_type;exists V293_tcb_type;auto| |exact HR].
 intros st Owned. destruct st as [[[[[[ge le] M] ir] aux] O] op].
 pose proof (V293_raw_cells_frame_env _ R (fun ge le=>get le ptcb=Some(bc,Tptr V293_tcb_type) /\ get le head=None /\ get ge head=Some(bh,Tptr V293_tcb_type)) Env _ Owned) as Bindings.
 change (get le ptcb=Some(bc,Tptr V293_tcb_type) /\ get le head=None /\
   get ge head=Some(bh,Tptr V293_tcb_type)) in Bindings.
 destruct Bindings as [B [N H]].
 assert(Read:load (Tptr V293_tcb_type) M (bh,0%Z)=Some(Vptr first)).
 { eapply (V293_rdy_raw_load (prefix++((bc,0%Z),Tptr V293_tcb_type,Vptr scan)::rest) R
   (bh,0%Z) (Tptr V293_tcb_type) (Vptr first) (ge,le,M,ir,aux,O,op));
   [apply in_app_or in Member;apply in_or_app;destruct Member;[left|right;right];assumption|
    reflexivity|exact Owned]. }
 cbn [sat getsmem get_smem evaltype evaladdr get_lenv get_genv]. rewrite B,N,H.
 repeat split;try reflexivity;try discriminate.
 cbn [evalval evaltype get_lenv get_genv get_mem]. rewrite N,H. exact Read.
Qed.

Lemma V293_tick_running_guard_owned : forall cells R running bu run,
 In ((bu,0%Z),Tint8,V293_byteval run) cells -> run<256 ->
 (forall st, st |= R -> get (getlenv st) running=None /\ get (getgenv st) running=Some(bu,Tint8)) ->
 V293_rdy_raw_cells cells R ==>
 Rv (V293_tick_eq (ecast (evar running) Tint32) 1) @ Tint32 ==
 Vint32 (if Nat.eqb run 1 then Int.one else Int.zero).
Proof.
 intros cells R running bu run Member Run Env st Owned.
 destruct st as [[[[[[ge le] M] ir] aux] O] op].
 pose proof (V293_raw_cells_frame_env _ R (fun ge le=>get le running=None /\ get ge running=Some(bu,Tint8)) Env _ Owned) as Bindings.
 change (get le running=None /\ get ge running=Some(bu,Tint8)) in Bindings.
 destruct Bindings as [N B].
 assert(Read:load Tint8 M (bu,0%Z)=Some(V293_byteval run)).
 { eapply (V293_rdy_raw_load cells R (bu,0%Z) Tint8 (V293_byteval run) (ge,le,M,ir,aux,O,op));
   [exact Member|apply V293_byte_type;exact Run|exact Owned]. }
 pose proof (V293_success_global_byte_eq ge le M running bu run 1 Run ltac:(lia) N B Read) as Eval.
 cbn [sat getsmem get_smem]. split;[exact Eval| ]. split.
 - unfold V293_tick_eq. cbn [evaltype get_lenv get_genv]. rewrite N,B. reflexivity.
 - discriminate.
Qed.

(* The global cells are an untouched frame of the real while. *)
Local Lemma tick_post_swap : forall globals cells R,
 V293_rdy_raw_cells (globals++cells) R ==>
 V293_rdy_raw_cells cells (V293_rdy_raw_cells globals R).
Proof.
 intros globals cells R st H. rewrite <- V293_raw_cells_append.
 exact (V293_raw_cells_permutation (globals++cells) (cells++globals)
   (Permutation_app_comm globals cells) R st H).
Qed.
Local Lemma tick_post_unswap : forall globals cells R,
 V293_rdy_raw_cells cells (V293_rdy_raw_cells globals R) ==>
 V293_rdy_raw_cells (globals++cells) R.
Proof.
 intros globals cells R st H. rewrite <- V293_raw_cells_append in H.
 exact (V293_raw_cells_permutation (cells++globals) (globals++cells)
   (Permutation_app_comm cells globals) R st H).
Qed.

Definition V293_tick_post_resource aop ir enabled si ci bn tick bu run bh head bc scan tasks idle bg br g lo hi R :=
 <||aop||> ** OS[ir,enabled,si,ci] **
 V293_rdy_raw_cells (V293_tick_post_cells bn tick bu run bh head bc scan tasks idle bg br g lo hi) R.
Definition V293_tick_post_result aop ir enabled si ci bn tick bu run bh head bc scan tasks idle bg br g lo hi R :=
 let bitmap:=if Nat.eqb run 1 then V293_tick_chain_bitmap tasks g lo hi else (g,(lo,hi)) in
 V293_tick_post_resource aop ir enabled si ci bn tick bu run bh head bc
  (if Nat.eqb run 1 then idle else scan)
  (if Nat.eqb run 1 then map V293_tick_task_after tasks else tasks) idle bg br
  (fst bitmap) (fst(snd bitmap)) (snd(snd bitmap)) R.

Theorem V293_tick_running_branch_hoare :
 forall Spec sd li I r ri tid aop R ptcb rows group now running head
 bc bn bu bh scan tasks idle bg br tick run g lo hi enabled ir si ci,
 (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid tasks -> run<256 -> g<256 ->lo<256 ->hi<256 ->
 (forall st, st |= R -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh (getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 InfRules Spec sd li I r ri
 (V293_tick_post_resource aop ir enabled si ci bn tick bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R)
 (sifthen (V293_tick_eq (ecast(evar running)Tint32)1)
   (sseq (sassign(evar ptcb)(evar head))
    (swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))))
 (V293_tick_post_result aop ir enabled si ci bn tick bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group now running head
 bc bn bu bh scan tasks idle bg br tick run g lo hi enabled ir si ci
 IdleLimit Valid Run G Lo Hi Env HR GF Bound.
 eapply V293_tick_known_ift_hoare with (flag:=Nat.eqb run 1).
 - intros st H.
   assert(Owned:st |= V293_rdy_raw_cells
     (V293_tick_post_cells bn tick bu run bh (V293_tick_head tasks idle) bc scan tasks idle bg br g lo hi)
     ((<||aop||> ** OS[ir,enabled,si,ci]) ** R)).
   { apply V293_raw_cells_unmove_frame. unfold V293_tick_post_resource in H. clear -H. sep auto. }
   eapply V293_tick_running_guard_owned;[ |exact Run| |exact Owned].
   + unfold V293_tick_post_cells,V293_tick_post_globals;cbn [app In];tauto.
   + intros s HS. eapply V293_star_env_r;[ |exact HS].
     intros s0 H0;exact (proj1 (proj2 (proj2 (Env s0 H0)))).
 - destruct (Nat.eqb run 1) eqn:Running.
   + unfold V293_tick_post_result. rewrite Running.
     destruct (V293_tick_chain_bitmap tasks g lo hi) as [gf [lof hif]] eqn:Bitmap.
     eapply seq_rule with
       (p':=V293_tick_post_resource aop ir enabled si ci bn tick bu run bh (V293_tick_head tasks idle)
          bc (V293_tick_head tasks idle) tasks idle bg br g lo hi R).
     * unfold V293_tick_post_resource,V293_tick_post_cells.
       eapply conseq_rule with
        (p:=<||aop||> ** V293_rdy_raw_cells
          (V293_tick_post_globals bn tick bu run bh (V293_tick_head tasks idle) ++
           V293_tick_pointer_cell bc scan :: (V293_tick_chain_cells tasks idle ++
             (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle])))
          (OS[ir,enabled,si,ci] ** R))
        (q:=<||aop||> ** V293_rdy_raw_cells
          (V293_tick_post_globals bn tick bu run bh (V293_tick_head tasks idle) ++
           V293_tick_pointer_cell bc (V293_tick_head tasks idle) :: (V293_tick_chain_cells tasks idle ++
             (V293_tick_bitmap_cells bg br g lo hi ++ [V293_tick_idle_cell idle])))
          (OS[ir,enabled,si,ci] ** R)).
       -- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_unmove_frame].
       -- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_move_frame].
       -- eapply V293_tick_head_assign_hoare.
          ++ unfold V293_tick_post_globals;cbn [app In];tauto.
          ++ intros s HS. eapply V293_star_env_r;[ |exact HS].
             intros s0 H0. destruct (Env s0 H0) as [Delay [_ [_ Head]]].
             exact (conj (proj1 Delay) Head).
          ++ apply V293_star_CurLINV_r;exact HR.
     * set (globals:=V293_tick_post_globals bn tick bu run bh (V293_tick_head tasks idle)).
       eapply conseq_rule with
        (p:=V293_tick_while_resource aop ir enabled si ci bc [] tasks idle bg br g lo hi (V293_rdy_raw_cells globals R))
        (q:=V293_tick_while_resource aop ir enabled si ci bc
          (V293_tick_chain_cells(map V293_tick_task_after tasks)idle) [] idle bg br gf lof hif (V293_rdy_raw_cells globals R)).
       -- unfold V293_tick_post_resource,V293_tick_post_cells,V293_tick_while_resource,V293_tick_while_cells.
          apply astar_mono;[intros s H;exact H| ]. apply astar_mono;[intros s H;exact H| ].
          apply tick_post_swap.
       -- unfold V293_tick_post_resource,V293_tick_post_cells,V293_tick_while_resource,V293_tick_while_cells.
          cbn [V293_tick_head V293_tick_chain_cells app fst snd].
          apply astar_mono;[intros s H;exact H| ]. apply astar_mono;[intros s H;exact H| ].
          apply tick_post_unswap.
       -- pose proof (V293_tick_while_hoare Spec sd li I r ri tid aop (V293_rdy_raw_cells globals R)
          ptcb rows group bc tasks idle bg br g lo hi enabled ir si ci IdleLimit Valid G Lo Hi) as While.
          rewrite Bitmap in While. apply While.
          ++ intros st HS. eapply V293_raw_cells_frame_env;[ |exact HS].
             intros st0 H0;exact (proj1 (Env st0 H0)).
          ++ apply V293_raw_cells_CurLINV;exact HR.
          ++ apply V293_raw_cells_good_frame;exact GF.
          ++ exact Bound.
   + unfold V293_tick_post_result. rewrite Running. intros st H;exact H.
Qed.

Theorem V293_tick_post_hook_hoare :
 forall Spec sd li I r ri tid aop R ptcb rows group now running head
 bc bn bu bh scan tasks idle bg br tick run g lo hi enabled ir si ci,
 (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid tasks -> run<256 ->g<256 ->lo<256 ->hi<256 ->
 (forall st, st |= R -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh (getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 InfRules Spec sd li I r ri
 (V293_tick_post_resource aop ir enabled si ci bn tick bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R)
 (V293_tick_post_hook ptcb rows group now running head)
 (V293_tick_post_result aop ir enabled si ci bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R) tid.
Proof.
 intros Spec sd li I r ri tid aop R ptcb rows group now running head
 bc bn bu bh scan tasks idle bg br tick run g lo hi enabled ir si ci
 IdleLimit Valid Run G Lo Hi Env HR GF Bound.
 set(before:=V293_tick_post_cells bn tick bu run bh (V293_tick_head tasks idle) bc scan tasks idle bg br g lo hi).
 set(after:=V293_tick_post_cells bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle) bc scan tasks idle bg br g lo hi).
 set(P:=V293_rdy_raw_cells before R). set(Q:=V293_rdy_raw_cells after R).
 set(branch:=sifthen (V293_tick_eq (ecast(evar running)Tint32)1)
   (sseq(sassign(evar ptcb)(evar head))(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)))).
 set(target:=V293_tick_post_result aop ir enabled si ci bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R).
 assert(GP:GoodFrm P) by (apply V293_raw_cells_good_frame;exact GF).
 assert(GQ:GoodFrm Q) by (apply V293_raw_cells_good_frame;exact GF).
 assert(IQ:Q ==> CurLINV li tid) by (apply V293_raw_cells_CurLINV;exact HR).
 assert(Branch:InfRules Spec sd li I r ri (<||aop||> ** OS[ir,enabled,si,ci] ** Q) branch target tid).
 { apply V293_tick_running_branch_hoare with (now:=now);assumption. }
 assert(Work:forall extra tail out,
   InfRules Spec sd li I r ri (<||aop||> ** extra ** Q) tail out tid ->
   InfRules Spec sd li I r ri (<||aop||> ** extra ** P)
     (sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))tail) out tid).
 { intros extra tail out Tail.
   eapply seq_rule with (p':=<||aop||> ** extra ** Q);[ |exact Tail].
   eapply conseq_rule with
     (p:=<||aop||> ** V293_rdy_raw_cells before (extra ** R))
     (q:=<||aop||> ** V293_rdy_raw_cells after (extra ** R)).
   - apply astar_mono;[intros st H;exact H|apply V293_raw_cells_unmove_frame].
   - apply astar_mono;[intros st H;exact H|apply V293_raw_cells_move_frame].
   - unfold before,after,V293_tick_post_cells,V293_tick_post_globals.
     eapply V293_tick_clock_assign_hoare with (before:=[]).
     + intros st HS. eapply V293_star_env_r;[ |exact HS].
       intros st0 H0;exact (proj1(proj2(Env st0 H0))).
     + apply V293_star_CurLINV_r;exact HR. }
 change (InfRules Spec sd li I r ri (<||aop||> ** OS[ir,enabled,si,ci] ** P)
   (sseq(sprim encrit)(sseq(sassign(evar now)(ebinop oplus(evar now)(econst32 Int.one)))
      (sseq(sprim excrit)branch))) target tid).
 destruct enabled.
 - eapply seq_rule.
   + eapply conseq_rule with
       (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [| (gettopis si<=INUM)%nat |] ** P)
       (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si) ** P).
     * intros st H. assert(IS:st |= Ais si ** Atrue) by (sep auto).
       pose proof(V293_time_topis si Atrue st IS) as Top.
       apply astar_l_atopis_elim in Top. destruct Top as [Top _].
       pose proof(@astar_l_atopis_intro st (gettopis si) _ H Top) as HT.
       clear H. rename HT into H. sep auto.
     * intros st H;exact H.
     * apply encrit1_rule;exact GP.
   + eapply conseq_rule with
       (p:=<||aop||> ** (OS[ir,false,si,true::ci] ** invlth_isr I 0 (gettopis si)) ** P)
       (q:=target);[ |intros st H;exact H|apply Work].
     * intros st H;sep auto.
     * eapply seq_rule with (p':=<||aop||> ** OS[ir,true,si,ci] ** Q);[ |exact Branch].
       eapply conseq_rule with
         (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0 (gettopis si) ** Q)
         (q:=<||aop||> ** OS[ir,true,si,ci] ** Q).
       -- intros st H. assert(IS:st |= Ais si ** Atrue) by (sep auto).
          pose proof(V293_time_topis si Atrue st IS) as Top.
          apply astar_l_atopis_elim in Top. destruct Top as [Top _].
          pose proof(@astar_l_atopis_intro st (gettopis si) _ H Top) as HT.
          clear H. rename HT into H. sep auto.
       -- intros st H;exact H.
       -- apply excrit1_rule;assumption.
 - eapply seq_rule;[apply encrit2_rule;exact GP| ].
   apply Work. eapply seq_rule;[apply excrit2_rule;exact GQ|exact Branch].
Qed.

Theorem V293_tick_post_hook_semantics :
 forall Spec sd li I r ri tid aop R ptcb rows group now running head
 bc bn bu bh scan tasks idle bg br tick run g lo hi enabled ir si ci,
 (Int.unsigned(snd idle)+50<=Int.max_unsigned)%Z ->
 Forall V293_tick_task_valid tasks -> run<256 ->g<256 ->lo<256 ->hi<256 ->
 (forall st, st |= R -> V293_tick_post_env ptcb rows group now running head bc br bg bn bu bh (getgenv st)(getlenv st)) ->
 (R ==> CurLINV li tid) -> GoodFrm R -> (gettopis si<=INUM)%nat ->
 simulation.RuleSem Spec sd li I r ri
 (V293_tick_post_resource aop ir enabled si ci bn tick bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R)
 (V293_tick_post_hook ptcb rows group now running head)
 (V293_tick_post_result aop ir enabled si ci bn (Int.add tick Int.one) bu run bh (V293_tick_head tasks idle)
    bc scan tasks idle bg br g lo hi R) tid.
Proof. intros. apply RuleSound. apply V293_tick_post_hook_hoare;assumption. Qed.

Print Assumptions V293_tick_clock_assign_hoare.
Print Assumptions V293_tick_head_assign_hoare.
Print Assumptions V293_tick_running_guard_owned.
Print Assumptions V293_tick_running_branch_hoare.
Print Assumptions V293_tick_post_hook_hoare.
Print Assumptions V293_tick_post_hook_semantics.
