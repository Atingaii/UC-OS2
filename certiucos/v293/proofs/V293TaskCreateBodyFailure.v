(* Full original TaskCreateExt body, legal task-context/free-priority entry and
   NULL free-list branch. Disabled IE only; three port Hooks stay external.
   This is not WFIFun, call allocation/free, enabled-IE or whole-kernel GOOD_OS. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_create_global_binding x tp b :=
 Agvarenv x tp (b,0%Z) //\\ A_notin_lenv x.
Definition V293_create_prefix_bindings bp bn bc table nesting reserved br :=
 Alvarenv 101%Z Tint8(bp,0%Z) **
 Alvarenv 109%Z Tint32(bc,0%Z) **
 V293_create_global_binding nesting Tint8 bn **
 V293_create_global_binding reserved Tint8 br ** V293_tcb_table_binding table.
Definition V293_create_prefix_state bp bn bc table nesting reserved br p cpu slot F aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells(V293_create_prefix_cells bp bn bc table p cpu slot)
 (OS[isr,false,is,cs] ** (V293_create_prefix_bindings bp bn bc table nesting reserved br ** F)).
Lemma V293_create_global_binding_env : forall x tp b s,
 s |= V293_create_global_binding x tp b ->
 get(getlenv s)x=None /\ get(getgenv s)x=Some(b,tp).
Proof.
 intros x tp b s [G[N Empty]]. destruct G as[actual[E[B _]]]. inversion B;subst actual.
 split;[ |exact E]. destruct(get(getlenv s)x)eqn:L;[ |reflexivity].
 exfalso. apply N. exists p. exact L.
Qed.
Lemma V293_create_prefix_bindings_env : forall bp bn bc table nesting reserved br s,
 s |= V293_create_prefix_bindings bp bn bc table nesting reserved br ** Atrue ->
 get(getlenv s)101%Z=Some(bp,Tint8) /\
 get(getlenv s)109%Z=Some(bc,Tint32) /\
 get(getlenv s)nesting=None /\ get(getgenv s)nesting=Some(bn,Tint8) /\
 get(getlenv s)reserved=None /\ get(getgenv s)reserved=Some(br,Tint8) /\
 get(getlenv s)92%Z=None /\ get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13).
Proof.
 intros bp bn bc table nesting reserved br s H.
 assert(P:s |= Alvarenv 101%Z Tint8(bp,0%Z) ** Atrue).
 { unfold V293_create_prefix_bindings in H. clear -H. sep auto. }
 assert(C:s |= Alvarenv 109%Z Tint32(bc,0%Z) ** Atrue).
 { unfold V293_create_prefix_bindings in H. clear -H. sep auto. }
 assert(N:s |= V293_create_global_binding nesting Tint8 bn ** Atrue).
 { unfold V293_create_prefix_bindings in H. clear -H. sep auto. }
 assert(B:s |= V293_create_global_binding reserved Tint8 br ** Atrue).
 { unfold V293_create_prefix_bindings in H. clear -H. sep auto. }
 assert(T:s |= V293_tcb_table_binding table ** Atrue).
 { unfold V293_create_prefix_bindings in H. clear -H. sep auto. }
 pose proof(V293_star_env_l _ _ (fun ge le=>get le nesting=None /\ get ge nesting=Some(bn,Tint8))
 (V293_create_global_binding_env nesting Tint8 bn)s N)as[Nl Ng].
 pose proof(V293_star_env_l _ _ (fun ge le=>get le reserved=None /\ get ge reserved=Some(br,Tint8))
 (V293_create_global_binding_env reserved Tint8 br)s B)as[Bl Bg].
 pose proof(V293_star_env_l _ _ (fun ge le=>get le 92%Z=None /\ get ge 92%Z=Some(table,Tarray(Tptr V293_tcb_type)13))
 (V293_tcb_table_binding_env table)s T)as[Tl Tg].
 assert(Pe:get(getlenv s)101%Z=Some(bp,Tint8)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 101%Z=Some(bp,Tint8)) _ s P). intros st[actual[E[B1 _]]]. inversion B1;subst actual. exact E. }
 assert(Ce:get(getlenv s)109%Z=Some(bc,Tint32)).
 { refine(V293_star_env_l _ _ (fun ge le=>get le 109%Z=Some(bc,Tint32)) _ s C). intros st[actual[E[B1 _]]]. inversion B1;subst actual. exact E. }
 repeat split;assumption.
Qed.
Lemma V293_create_prefix_raw_env : forall cells bp bn bc table nesting reserved br F isr is cs s,
 s |= V293_rdy_raw_cells cells(OS[isr,false,is,cs] ** (V293_create_prefix_bindings bp bn bc table nesting reserved br ** F)) ->
 get(getlenv s)101%Z=Some(bp,Tint8) /\ get(getlenv s)109%Z=Some(bc,Tint32) /\
 get(getlenv s)nesting=None /\ get(getgenv s)nesting=Some(bn,Tint8) /\
 get(getlenv s)reserved=None /\ get(getgenv s)reserved=Some(br,Tint8) /\
 get(getlenv s)92%Z=None /\ get(getgenv s)92%Z=Some(table,Tarray(Tptr V293_tcb_type)13).
Proof.
 intros. eapply V293_raw_cells_frame_env;[ |exact H].
 intros st H1. eapply V293_star_env_r;[ |exact H1].
 intros st1 H2. apply V293_create_prefix_bindings_env. clear -H2. sep auto.
Qed.
Lemma V293_create_prefix_good : forall bp bn bc table nesting reserved br p cpu slot F,
 GoodFrm F -> GoodFrm(V293_rdy_raw_cells(V293_create_prefix_cells bp bn bc table p cpu slot)
 (V293_create_prefix_bindings bp bn bc table nesting reserved br ** F)).
Proof.
 intros. cbn [V293_rdy_raw_cells V293_create_prefix_cells V293_create_prefix_bindings
 V293_create_global_binding V293_tcb_table_binding GoodFrm]. tauto.
Qed.
Lemma V293_create_prefix_cpu_hoare : forall Spec sd li I r ri tid
 bp bn bc table nesting reserved br p old slot F aop isr is cs,
 (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_prefix_state bp bn bc table nesting reserved br p old slot F aop isr is cs)
 (sassign(evar 109%Z)(econst32 Int.zero))
 (V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)slot F aop isr is cs)tid.
Proof.
 intros. unfold V293_create_prefix_state,V293_create_prefix_cells.
 eapply V293_raw_assign_hoare with(before:=[((bp,0%Z),Tint8,V293_byteval p);((bn,0%Z),Tint8,V293_byteval 0)])
 (a:=(bc,0%Z))(rt:=Tint32).
 - reflexivity.
 - apply eq_int;auto.
 - intros s Owned.
   destruct(V293_create_prefix_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ Owned)as[Bp[Bc _]].
   destruct s as [[[[[[ge le] M] ir] aux] O] op].
   change(get le 109%Z=Some(bc,Tint32))in Bc.
   cbn [sat getsmem get_smem evaladdr evaltype evalval get_lenv].
   cbv delta [env var memory.ident Modules.ident]in *. rewrite Bc.
   repeat split;try reflexivity;discriminate.
 - apply V293_star_CurLINV_r. apply V293_star_CurLINV_r. exact H.
Qed.

Lemma V293_create_prefix_guards : forall bp bn bc table nesting reserved br p cpu F isr is cs s,
 p<13 ->
 s |= V293_rdy_raw_cells(V293_create_prefix_cells bp bn bc table p cpu Vnull)
 (OS[isr,false,is,cs] ** (V293_create_prefix_bindings bp bn bc table nesting reserved br ** F)) ->
 (evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(getsmem s)=Some Tint32) /\
 (evalval(ebinop olt(econst32 Int.zero)(ecast(evar nesting)Tint32))(getsmem s)=Some(Vint32 Int.zero) /\
 evaltype(ebinop olt(econst32 Int.zero)(ecast(evar nesting)Tint32))(getsmem s)=Some Tint32) /\
 (evalval(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some(Vint32 Int.one) /\
 evaltype(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some Tint32).
Proof.
 intros bp bn bc table nesting reserved br p cpu F isr is cs s Range Owned.
 destruct(V293_create_prefix_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ Owned)
 as(Bp&Bc&Nn&Gn&Nr&Gr&Nt&Gt).
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 cbn [getlenv getgenv get_lenv get_genv get_smem]in *. unfold V293_create_prefix_cells in Owned.
 pose proof(V293_byte_type p ltac:(lia))as PValid.
 V293_tcb_init_read Owned 0%nat PriorityRead.
 V293_tcb_init_read Owned 1%nat NestingRead.
 V293_tcb_init_read Owned 3%nat SlotRead.
 cbn [getsmem get_smem].
 assert(PriorityFalse:evalval(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))(ge,le,M)=Some(Vint32 Int.zero)).
 { cbn [evalval evaltype get_lenv get_genv get_mem].
   cbv delta [env var memory.ident Modules.ident]in *. rewrite Bp.
   cbn beta iota. rewrite PriorityRead.
   cbn [cast_eval V293_byteval is_int_type bop_eval cmp_val cmpu].
   rewrite V293_create_priority_guard_false by exact Range. reflexivity. }
 assert(NestingFalse:evalval(ebinop olt(econst32 Int.zero)(ecast(evar nesting)Tint32))(ge,le,M)=Some(Vint32 Int.zero))by V293_rdy_eval.
 assert(SlotTrue:evalval(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(ge,le,M)=Some(Vint32 Int.one)).
 { cbn [evalval evaltype get_lenv get_genv get_mem].
   cbv delta [env var memory.ident Modules.ident]in *. rewrite Nt,Gt,Bp.
   cbn beta iota. rewrite PriorityRead. cbn [load addr_to_addrval V293_byteval].
   rewrite Int.add_zero_l. unfold Int.mul.
   rewrite(Int.unsigned_repr(Z.of_nat p))by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
   change(match load(Tptr V293_tcb_type)M(table,Int.unsigned(Int.repr(4*Z.of_nat p)))with
    |Some v=>val_eq v Vnull|_=>None end=Some(Vint32 Int.one)).
   rewrite Int.unsigned_repr by(change(0<=4*Z.of_nat p<=4294967295)%Z;lia).
   change(load(Tptr V293_tcb_type)M(table,(4*Z.of_nat p)%Z)=Some Vnull)in SlotRead.
   rewrite SlotRead. reflexivity. }
 repeat split;try assumption;V293_rdy_eval.
Qed.

Lemma V293_create_prefix_reserve_hoare : forall Spec sd li I r ri tid
 bp bn bc table nesting reserved br p cpu F aop isr is cs,
 p<13 -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_prefix_state bp bn bc table nesting reserved br p cpu Vnull F aop isr is cs)
 (sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr reserved))
 (V293_create_prefix_state bp bn bc table nesting reserved br p cpu(Vptr(br,Int.zero))F aop isr is cs)tid.
Proof.
 intros Spec sd li I r ri tid bp bn bc table nesting reserved br p cpu F aop isr is cs Range HR.
 unfold V293_create_prefix_state,V293_create_prefix_cells.
 eapply V293_raw_assign_hoare with
 (before:=[((bp,0%Z),Tint8,V293_byteval p);((bn,0%Z),Tint8,V293_byteval 0);((bc,0%Z),Tint32,cpu)])
 (a:=(table,(4*Z.of_nat p)%Z))(rt:=Tptr V293_tcb_type).
 - cbn [snd]. apply Int.unsigned_repr. change(0<=4*Z.of_nat p<=4294967295)%Z;lia.
 - apply eq_vptr. do 2 eexists;split;reflexivity.
 - intros s Owned.
   destruct(V293_create_prefix_raw_env _ _ _ _ _ _ _ _ _ _ _ _ _ Owned)as(Bp&Bc&Nn&Gn&Nr&Gr&Nt&Gt).
   destruct s as [[[[[[ge le] M] ir] aux] O] op]. cbn [getlenv getgenv get_lenv get_genv get_smem]in *.
   pose proof(V293_byte_type p ltac:(lia))as PValid.
   V293_tcb_init_read Owned 0%nat PriorityRead.
   destruct(V293_rekey_array_address ge le M 92%Z 101%Z V293_tcb_type table bp p
    Nt Gt Bp PriorityRead Range)as[Kind Address].
   destruct(V293_reserved_symbol_eval ge le M reserved br Nr Gr)as[TK TV].
   cbn [sat getsmem get_smem fst snd]. split;[split;assumption| ].
   repeat split;try assumption;discriminate.
 - apply V293_star_CurLINV_r. apply V293_star_CurLINV_r. exact HR.
Qed.

(* Internal continuation lemma. The public full-body theorem below discharges
   its suffix premise with the actual two-call/failure theorem, not an oracle. *)
Theorem V293_OSTaskCreateExt_prefix_hoare : forall Spec sd li I r ri tid
 bp bn bc table nesting reserved br p old F aop isr is cs suffix,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li I r ri
 (V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)(Vptr(br,Int.zero))F aop isr is cs)
 suffix Afalse tid ->
 InfRules Spec sd li I r ri
 (V293_create_prefix_state bp bn bc table nesting reserved br p old Vnull F aop isr is cs)
 (V293_TaskCreateExt_prefix 92%Z 101%Z nesting 109%Z reserved suffix)Afalse tid.
Proof.
 intros Spec sd li I r ri tid bp bn bc table nesting reserved br p old F aop isr is cs suffix Range Frame HR Suffix.
 unfold V293_TaskCreateExt_prefix. eapply seq_rule.
 - apply V293_create_prefix_cpu_hoare. exact HR.
 - eapply seq_rule.
   + eapply ift_rule with(tp:=Tint32).
     * intros s H. exists(Vint32 Int.zero).
       unfold V293_create_prefix_state in H.
       apply astar_l_aop'_elim in H. destruct H as[_ H].
       destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
        H)as[[Value Kind] _].
       cbn [sat]. repeat split;try assumption;discriminate.
     * intros s[H _]. exact H.
     * eapply conseq_rule with(p:=Afalse)(q:=Afalse).
       -- intros s[H[v[Value Bool]]]. unfold V293_create_prefix_state in H.
          apply astar_l_aop'_elim in H. destruct H as[_ H].
          destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
           H)as[[Zero _] _].
          rewrite Zero in Value. inversion Value;subst v. discriminate Bool.
       -- intros s H. contradiction.
       -- apply pfalse_rule.
   + eapply seq_rule with(p':=V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)Vnull F aop isr is (false::cs)).
     * unfold V293_create_prefix_state. eapply conseq_rule.
       -- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_move_frame].
       -- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_unmove_frame].
       -- apply encrit2_rule. apply V293_create_prefix_good. exact Frame.
     * eapply seq_rule.
       -- eapply ift_rule with(tp:=Tint32).
          ++ intros s H. exists(Vint32 Int.zero).
             unfold V293_create_prefix_state in H.
             (* Keep the memory containing guards; only the aop is separated. *)
             apply astar_l_aop'_elim in H. destruct H as[_ H].
             destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
              H)as[_[[Value Kind] _]].
             cbn [sat]. repeat split;try assumption;discriminate.
          ++ intros s[H _]. exact H.
          ++ eapply conseq_rule with(p:=Afalse)(q:=Afalse).
             ** intros s[H[v[Value Bool]]]. unfold V293_create_prefix_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
                destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
                 H)as[_[[Zero _] _]].
                rewrite Zero in Value. inversion Value;subst v. discriminate Bool.
             ** intros s H. contradiction.
             ** apply pfalse_rule.
       -- eapply seq_rule with(p':=Afalse).
          ++ eapply ift_rule with(tp:=Tint32).
             ** intros s H. exists(Vint32 Int.one). unfold V293_create_prefix_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
                destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
                 H)as[_[_[Value Kind]]].
                cbn [sat]. repeat split;try assumption;discriminate.
             ** intros s[H[v[Value Bool]]]. unfold V293_create_prefix_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
                destruct(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range
                 H)as[_[_[One _]]].
                rewrite One in Value. inversion Value;subst v. discriminate Bool.
             ** eapply conseq_rule.
                --- intros s[H _]. exact H.
                --- intros s H. exact H.
                --- eapply seq_rule.
                    +++ apply V293_create_prefix_reserve_hoare;assumption.
                    +++ eapply seq_rule with(p':=V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)(Vptr(br,Int.zero))F aop isr is cs).
                        *** unfold V293_create_prefix_state. eapply conseq_rule.
                            ---- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_move_frame].
                            ---- apply astar_mono;[intros s H;exact H|apply V293_raw_cells_unmove_frame].
                            ---- apply excrit2_rule. apply V293_create_prefix_good. exact Frame.
                        *** exact Suffix.
          ++ apply pfalse_rule.
Qed.

(* Residual resources introduced by the actual entry prefix. Priority and
   table binding move into the existing call interface; no bytes duplicate. *)
Definition V293_create_prefix_kept bn bc nesting reserved br F :=
 V293_rdy_raw_cells (((bn,0%Z),Tint8,V293_byteval 0)::
                     ((bc,0%Z),Tint32,Vint32 Int.zero)::nil)
 (Alvarenv 109%Z Tint32(bc,0%Z) **
  V293_create_global_binding nesting Tint8 bn **
  V293_create_global_binding reserved Tint8 br ** F).
Definition V293_create_body_frame bg Rbefore oldpsp target argv inputtop options olderr
 bottom identity size ext F :=
 Agvarenv 91%Z(Tptr V293_tcb_type)(bg,0%Z) **
 Amapsto(bg,0%Z)(Tptr V293_tcb_type)false Vnull ** Rbefore **
 LV 108%Z @ (Tptr Tint32) |-> oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |-> olderr **
  LV 205%Z @ (Tptr Tint32) |-> bottom **
  LV 206%Z @ Tint16 |-> identity **
  LV 207%Z @ Tint32 |-> size **
  LV 208%Z @ (Tptr Tvoid) |-> ext ** F).
Lemma V293_create_prefix_kept_good : forall bn bc nesting reserved br F,
 GoodFrm F -> GoodFrm(V293_create_prefix_kept bn bc nesting reserved br F).
Proof.
 intros. unfold V293_create_prefix_kept,V293_create_global_binding.
 cbn [V293_rdy_raw_cells GoodFrm]. tauto.
Qed.
Lemma V293_create_body_frame_good : forall bg Rbefore oldpsp target argv inputtop options olderr
 bottom identity size ext F,
 GoodFrm Rbefore -> GoodFrm F ->
 GoodFrm(V293_create_body_frame bg Rbefore oldpsp target argv inputtop options olderr bottom identity size ext F).
Proof.
 intros. unfold V293_create_body_frame,V293_create_stack_arguments,Alvarmapsto,Alvarenv',Aptrmapsto.
 cbn [GoodFrm]. tauto.
Qed.
Lemma V293_create_raw_local : forall x tp b v,
 Alvarenv x tp(b,0%Z) ** Amapsto(b,0%Z)tp true v ==> LV x @ tp |->v.
Proof.
 intros x tp b v s H. exists b. unfold Alvarenv',Aptrmapsto.
 cbn [addrval_to_addr Int.unsigned Int.zero]. exact H.
Qed.
Lemma V293_create_body_to_calls : forall bp bn bc table nesting reserved br p bg Rbefore
 oldpsp target argv inputtop options olderr bottom identity size ext F aop isr is cs,
 V293_create_prefix_state bp bn bc table nesting reserved br p(Vint32 Int.zero)(Vptr(br,Int.zero))
 (V293_create_body_frame bg Rbefore oldpsp target argv inputtop options olderr bottom identity size ext F)
 aop isr is cs ==>
 V293_tcb_empty_external bg Rbefore aop isr is cs **
 LV 108%Z @ (Tptr Tint32) |->oldpsp **
 V293_create_stack_arguments target argv inputtop options
 (LV 209%Z @ Tint8 |->olderr ** LV 101%Z @ Tint8 |->V293_byteval p **
  LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
  LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
  (V293_tcb_table_binding table **
   (Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr(br,Int.zero)) **
    V293_create_prefix_kept bn bc nesting reserved br F))).
Proof.
 intros bp bn bc table nesting reserved br p bg Rbefore oldpsp target argv inputtop options olderr bottom identity size ext F aop isr is cs s H.
 unfold V293_create_prefix_state,V293_create_prefix_cells,
 V293_create_prefix_bindings,V293_create_body_frame,V293_create_prefix_kept,
 V293_create_stack_arguments,V293_tcb_empty_external in *.
 cbn [V293_rdy_raw_cells]in *.
 assert(K:s |= (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
  (<||aop||> ** OS[isr,false,is,cs] **
  Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
  Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero) **
  Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr(br,Int.zero)) **
  Alvarenv 109%Z Tint32(bc,0%Z) ** V293_create_global_binding nesting Tint8 bn **
  V293_create_global_binding reserved Tint8 br ** V293_tcb_table_binding table **
  Agvarenv 91%Z(Tptr V293_tcb_type)(bg,0%Z) **
  Amapsto(bg,0%Z)(Tptr V293_tcb_type)false Vnull ** Rbefore **
  LV 108%Z @ (Tptr Tint32) |->oldpsp **
  LV 201%Z @ Tint32 |->V293_task_selector target **
  LV 202%Z @ (Tptr Tvoid) |->argv ** LV 203%Z @ (Tptr Tint32) |->inputtop **
  LV 204%Z @ Tint16 |->options ** LV 209%Z @ Tint8 |->olderr **
  LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
  LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext ** F)).
 { clear -H. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_raw_local|intros st HS;exact HS].
 clear -K. sep auto.
Qed.
Theorem V293_OSTaskCreateExt_empty_body_hoare : forall Spec sd li I tid f hook
 bp bnest bcpu table nesting reserved breserved cpuold slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 (good:GoodFunAsrt R) Rbefore (gb:GoodFunAsrt Rbefore) F olderr oldpsp target argv inputtop running sched,
 GoodFrm Rbefore -> GoodFrm R -> GoodFrm F -> p<13 ->
 V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 (R ==> CurLINV li tid) ->
 let fp:=V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpre bg R aop isr is cs good)
   (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good) in
 let fq:=V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base))
   (V293_tcb_empty_fpost bg R aop isr is cs good)
   (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next
      bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good) in
 Spec hook=Some(
 V293_create_stack_fpre bg Rbefore aop isr is cs gb(V293_create_stack_values target argv inputtop options),
 V293_create_stack_fpost bg R aop isr is cs good(V293_create_stack_values target argv inputtop options)top,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_failure_return table p
  (V293_create_failure_kept bg top bottom identity size ext options R
  (V293_create_stack_kept target argv inputtop
   (V293_create_prefix_kept bnest bcpu nesting reserved breserved F))) aop isr is cs) Afalse
 (V293_create_prefix_state bp bnest bcpu table nesting reserved breserved p cpuold Vnull
  (V293_create_body_frame bg Rbefore oldpsp target argv inputtop options olderr bottom identity size ext F)
  aop isr is cs)
 (V293_CreateExt_body 92%Z nesting reserved running sched hook f) Afalse tid.
Proof.
 intros Spec sd li I tid f hook bp bnest bcpu table nesting reserved breserved cpuold slot bg bt base old p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good Rbefore gb
 F olderr oldpsp target argv inputtop running sched BeforeFrame RFrame Frame Range StackValid HBefore Valid HR fp fq Hook TCB.
 unfold V293_CreateExt_body,V293_TaskCreateExt_body.
 apply V293_OSTaskCreateExt_prefix_hoare.
 - exact Range.
 - apply V293_create_body_frame_good;assumption.
 - unfold V293_create_body_frame. do 2 apply V293_star_CurLINV_r.
   apply V293_star_CurLINV_l. exact HBefore.
 - eapply conseq_rule with(q:=Afalse).
   + apply V293_create_body_to_calls.
   + intros s H;exact H.
   + eapply V293_OSTaskCreateExt_stack_empty_failure_hoare with
      (good:=good)(gb:=gb)(slot:=slot)(bt:=bt)(base:=base)(old:=old)(next:=next)
      (bh:=bh)(bgrp:=bgrp)(br:=br)(bn:=bn)(oldblock:=oldblock)(oldbase:=oldbase)
      (present:=present)(oldprev:=oldprev)(g:=g)(row:=row)(n:=n)(oldback:=oldback).
     * exact RFrame.
     * apply V293_create_prefix_kept_good. exact Frame.
     * exact Range.
     * exact StackValid.
     * exact HBefore.
     * exact Valid.
     * exact HR.
     * exact Hook.
     * exact TCB.
Qed.
