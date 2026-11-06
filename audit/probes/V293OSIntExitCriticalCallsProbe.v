(* Independent physical saved cells. These snapshots instantiate contracts;
   they are not a port implementation, interrupt trace or production invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Definition SCtid : tid := (754%positive,Int.zero).
Definition SCge : env := sig OSTCBCur(753%positive,Tptr Tvoid).
Definition SCle b : env := sig 9301%Z(b,Tint32).
Definition SCcell b value := V293_encoded_memory b 0 true(encode_val Tint32 value).
Definition SCcurrent := V293_encoded_memory 753%positive 0 false(encode_val(Tptr Tvoid)(Vptr SCtid)).
Definition SCmemory value := merge(SCcell 751%positive value)
 (merge(SCcell 752%positive(Vint32 Int.zero))SCcurrent).
Definition SCstate le M enabled : RstateOP :=
 (SCge,le,M,(fun _=>false),(enabled,[],[]),(emp:osabst),spec_done None).
Definition SCshared enabled := CurLINV V293_witness_li SCtid ** Aie enabled.
Definition SCresource value enabled :=
 V293_saved_pointer_resource(spec_done None)value(SCshared enabled).
Definition SCcaller bs bo other := Alvarenv 9301%Z Tint32(bs,0%Z) **
 PV(bo,Int.zero)@Tint32|->other.

Lemma SCstar : forall le enabled m1 m2 m p q,
 join m1 m2 m -> SCstate le m1 enabled |= p -> SCstate le m2 enabled |= q ->
 SCstate le m enabled |= p ** q.
Proof.
 intros. exists m1. exists m2. exists m. exists(emp:osabst). exists(emp:osabst). exists(emp:osabst).
 split;[reflexivity| ]. split;[assumption| ]. split;[reflexivity| ].
 split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma SCcurrent_owned : forall le enabled,
 SCstate le SCcurrent enabled |= CurLINV V293_witness_li SCtid.
Proof.
 intros le enabled.
 assert(C:SCstate le SCcurrent enabled |= CurTid SCtid).
 { exists Tvoid. exists 753%positive. eapply SCstar with(m1:=emp)(m2:=SCcurrent).
   - apply map_join_comm;apply map_join_emp.
   - exists 753%positive. split;[vm_compute;reflexivity|repeat split;reflexivity].
   - split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 exists([]:list logicvar). unfold LINV,V293_witness_li.
 pose proof V293_witness_li_good as Good. clear -C Good;sep auto.
Qed.
Ltac SCapart block :=
 apply map_join_merge;apply map_disjoint;intros[b i];
 destruct(Pos.eq_dec b block);[subst b;right;left|left];
 unfold SCcell,SCcurrent;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma SCphysical : forall le value enabled,
 SCstate le(SCmemory value)enabled |=
 PV(751%positive,Int.zero)@Tint32|->value **
 (PV(752%positive,Int.zero)@Tint32|->Vint32 Int.zero ** SCshared enabled).
Proof.
 intros. unfold SCmemory.
 eapply SCstar;[SCapart 751%positive| | ].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply SCstar;[SCapart 752%positive| | ].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + unfold SCshared. apply astar_comm;apply astar_l_aie_intro;
     [apply SCcurrent_owned|reflexivity].
Qed.
Lemma SCnonempty : forall value enabled,
 SCstate(SCle 751%positive)(SCmemory value)enabled |=
 SCresource value enabled(751%positive,Int.zero) **
 SCcaller 751%positive 752%positive(Vint32 Int.zero).
Proof.
 intros value enabled.
 pose proof(SCphysical(SCle 751%positive)value enabled)as P.
 assert(H:SCstate(SCle 751%positive)(SCmemory value)enabled |=
 Alvarenv 9301%Z Tint32(751%positive,0%Z) **
 (PV(751%positive,Int.zero)@Tint32|->value **
 (PV(752%positive,Int.zero)@Tint32|->Vint32 Int.zero ** SCshared enabled))).
 { apply astar_l_alvarenv_intro;[exact P|split;vm_compute;reflexivity]. }
 unfold SCresource,V293_saved_pointer_resource,SCcaller.
 apply astar_l_aop'_intro with(aop:=spec_done None)in H;[ |reflexivity]. clear -H;sep auto.
Qed.
Lemma SCalternate_nonempty : forall value enabled,
 SCstate(SCle 752%positive)(SCmemory value)enabled |=
 SCresource(Vint32 Int.zero)enabled(752%positive,Int.zero) **
 SCcaller 752%positive 751%positive value.
Proof.
 intros value enabled.
 pose proof(SCphysical(SCle 752%positive)value enabled)as P.
 assert(H:SCstate(SCle 752%positive)(SCmemory value)enabled |=
 Alvarenv 9301%Z Tint32(752%positive,0%Z) **
 (PV(751%positive,Int.zero)@Tint32|->value **
 (PV(752%positive,Int.zero)@Tint32|->Vint32 Int.zero ** SCshared enabled))).
 { apply astar_l_alvarenv_intro;[exact P|split;vm_compute;reflexivity]. }
 unfold SCresource,V293_saved_pointer_resource,SCcaller.
 apply astar_l_aop'_intro with(aop:=spec_done None)in H;[ |reflexivity]. clear -H;sep auto.
Qed.
Lemma SCgood : forall value enabled address,GoodFunAsrt(SCresource value enabled address).
Proof.
 intros value enabled. apply V293_saved_pointer_resource_good.
 unfold SCshared. split;[ |exact I].
 apply V293_CurLINV_function_assertion;exact V293_witness_li_good.
Qed.
Lemma SClocal : forall value enabled address,
 SCresource value enabled address ==> CurLINV V293_witness_li SCtid.
Proof.
 intros value enabled address. unfold SCresource.
 apply V293_saved_pointer_resource_local.
 unfold SCshared. apply V293_star_CurLINV_l. intros s H;exact H.
Qed.
Lemma SCdomain : forall bs,
 eq_dom_env(SCle bs)[(9301%Z,Tint32)].
Proof.
 intros bs x tp. cbn[In]. split.
 - intros[E|F];[inversion E;subst x tp;exists bs;vm_compute;reflexivity|contradiction].
 - intros[b H]. unfold SCle in H.
   destruct(Z.eq_dec 9301%Z x)as[E|N].
   + subst x. rewrite map_get_sig in H. inversion H;subst tp;left;reflexivity.
   + rewrite map_get_sig' in H by exact N. discriminate.
Qed.
Lemma SCarguments : forall bs bo other value enabled M,
 SCstate(SCle bs)M enabled |= SCresource value enabled(bs,Int.zero) ** SCcaller bs bo other ->
 (SCstate(SCle bs)M enabled |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(bs,Int.zero)]).
Proof.
 intros bs bo other value enabled M H. eapply V293_saved_pointer_argument.
 unfold SCcaller in H;clear -H;sep auto.
Qed.
Theorem SCbinding_control :
 eq_dom_env(SCle 751%positive)[(9301%Z,Tint32)] /\
 eq_dom_env(SCle 752%positive)[(9301%Z,Tint32)] /\
 (SCstate(SCle 751%positive)(SCmemory(Vint32 Int.zero))true |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(751%positive,Int.zero)]) /\
 (SCstate(SCle 752%positive)(SCmemory(Vint32 Int.zero))true |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(752%positive,Int.zero)]) /\
 ~(SCstate(SCle 752%positive)(SCmemory(Vint32 Int.zero))true |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(751%positive,Int.zero)]).
Proof.
 split;[apply SCdomain| ]. split;[apply SCdomain| ].
 assert(A:SCstate(SCle 751%positive)(SCmemory(Vint32 Int.zero))true |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(751%positive,Int.zero)]).
 { eapply SCarguments;apply SCnonempty. }
 assert(B:SCstate(SCle 752%positive)(SCmemory(Vint32 Int.zero))true |=
 Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(752%positive,Int.zero)]).
 { eapply SCarguments;apply SCalternate_nonempty. }
 split;[exact A| ]. split;[exact B| ].
 intros[Wrong _]. destruct B as[Actual _]. rewrite Actual in Wrong;discriminate.
Qed.
Lemma SCsaved_load : forall c enabled bs bo other M,
 SCstate(SCle bs)M enabled |= SCresource(Vint32 c)enabled(bs,Int.zero) ** SCcaller bs bo other ->
 load Tint32 M(bs,0%Z)=Some(Vint32 c).
Proof.
 intros c enabled bs bo other M H.
 change(load Tint32(getmem(SCstate(SCle bs)M enabled))(bs,0%Z)=Some(Vint32 c)).
 eapply V293_star_load_l;[ |exact H].
 unfold SCresource,V293_saved_pointer_resource.
 eapply V293_star_load_r. eapply V293_star_load_l.
 intros s[Held _];eapply mapstoval_load;[reflexivity|exact Held].
Qed.
Theorem SCsaved_value_control :
 (SCstate(SCle 751%positive)(SCmemory(Vint32 Int.one))false |=
  SCresource(Vint32 Int.one)false(751%positive,Int.zero) ** SCcaller 751%positive 752%positive(Vint32 Int.zero)) /\
 (SCstate(SCle 751%positive)(SCmemory(Vint32 Int.one))false |=
  Rvl[eaddrof(evar 9301%Z)]@[Tptr Tint32]==[Vptr(751%positive,Int.zero)]) /\
 ~(SCstate(SCle 751%positive)(SCmemory(Vint32 Int.one))false |=
  SCresource(Vint32 Int.zero)false(751%positive,Int.zero) ** SCcaller 751%positive 752%positive(Vint32 Int.zero)).
Proof.
 split;[apply SCnonempty| ]. split;[eapply SCarguments;apply SCnonempty| ].
 intro H. pose proof(SCsaved_load _ _ _ _ _ _ H)as Wrong.
 pose proof(SCsaved_load _ _ _ _ _ _(SCnonempty(Vint32 Int.one)false))as Actual.
 rewrite Actual in Wrong;discriminate.
Qed.
Theorem SCsaved_frame : forall v w b i,b<>751%positive ->
 get(SCmemory v)(b,i)=get(SCmemory w)(b,i).
Proof.
 intros v w b i Ne.
 assert(Absent:forall value,get(SCcell 751%positive value)(b,i)=None).
 { intros value;unfold SCcell;apply V293_encoded_memory_outside;left;exact Ne. }
 unfold SCmemory.
 rewrite (map_merge_semp (SCcell 751%positive v)
  (merge(SCcell 752%positive(Vint32 Int.zero))SCcurrent)(b,i)) by reflexivity.
 rewrite(Absent v).
 rewrite (map_merge_semp (SCcell 751%positive w)
  (merge(SCcell 752%positive(Vint32 Int.zero))SCcurrent)(b,i)) by reflexivity.
 rewrite(Absent w). reflexivity.
Qed.
Definition SCpre := V293_saved_pointer_fpre SCtid(SCresource(Vint32 Int.zero)true)(SCgood(Vint32 Int.zero)true).
Definition SCpost := V293_saved_pointer_fpost SCtid(SCresource(Vint32 Int.one)false)(SCgood(Vint32 Int.one)false).
Definition SCspec : funspec := fun f=>if Z.eq_dec f 9401%Z then Some(SCpre,SCpost,(Tvoid,[Tptr Tint32]))else None.
Theorem SCcallee_snapshots_nonempty :
 (SCstate(SCle 751%positive)(SCmemory(Vint32 Int.zero))true |=
  getasrt(SCpre (Vptr(751%positive,Int.zero)::nil) nil SCtid) ** SCcaller 751%positive 752%positive(Vint32 Int.zero)) /\
 (SCstate(SCle 751%positive)(SCmemory(Vint32 Int.one))false |=
  getasrt(SCpost (Vptr(751%positive,Int.zero)::nil) None nil SCtid) ** SCcaller 751%positive 752%positive(Vint32 Int.zero)).
Proof.
 split;cbn[SCpre SCpost V293_saved_pointer_fpre V293_saved_pointer_fpost getasrt].
 - pose proof(SCnonempty(Vint32 Int.zero)true)as H;clear -H;sep auto.
 - pose proof(SCnonempty(Vint32 Int.one)false)as H;clear -H;sep auto.
Qed.
Theorem SCcall_checked : forall sd I r ri,
 InfRules SCspec sd V293_witness_li I r ri
 (SCresource(Vint32 Int.zero)true(751%positive,Int.zero) ** SCcaller 751%positive 752%positive(Vint32 Int.zero))
 (scall 9401%Z[eaddrof(evar 9301%Z)])
 (SCresource(Vint32 Int.one)false(751%positive,Int.zero) ** SCcaller 751%positive 752%positive(Vint32 Int.zero))SCtid.
Proof.
 intros. apply V293_saved_pointer_call with(before_good:=SCgood(Vint32 Int.zero)true)
 (after_good:=SCgood(Vint32 Int.one)false).
 - constructor.
 - apply SClocal.
 - apply SClocal.
 - unfold SCspec. destruct(Z.eq_dec 9401%Z 9401%Z);[reflexivity|contradiction].
Qed.
Theorem SClookup_ablation :
 SCspec 9401%Z=Some(SCpre,SCpost,(Tvoid,[Tptr Tint32])) /\
 (fun _:fid=>@None(fpre*fpost*(type*typelist)))9401%Z=None.
Proof. split;[unfold SCspec;destruct(Z.eq_dec 9401%Z 9401%Z);[reflexivity|contradiction]|reflexivity]. Qed.
Theorem SClocal_boundary :
 GoodFrm(Alvarenv 9301%Z Tint32(751%positive,0%Z)) /\
 ~GoodFunAsrt(Alvarenv 9301%Z Tint32(751%positive,0%Z)).
Proof. split;[exact I|apply V293_saved_pointer_local_excluded]. Qed.

Theorem SCinitialize_checked : forall Spec sd I r ri value enabled,
 InfRules Spec sd V293_witness_li I r ri
 (<||spec_done None||> ** (V293_time_cell true 9301%Z 751%positive value **
  (SCshared enabled ** PV(752%positive,Int.zero)@Tint32|->Vint32 Int.zero)))
 (sassign(evar 9301%Z)(econst32 Int.zero))
 (SCresource(Vint32 Int.zero)enabled(751%positive,Int.zero) **
  SCcaller 751%positive 752%positive(Vint32 Int.zero))SCtid.
Proof.
 intros. unfold SCresource,SCcaller. apply V293_OSIntExit_saved_initialize.
 unfold SCshared. apply V293_star_CurLINV_l;intros s H;exact H.
Qed.
