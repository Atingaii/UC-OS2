(* Three independent byte blocks plus a real current-task pointer. The empty
   local invariant is a test fixture, not the production ISR invariant. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition XEge : env := set(set(set(sig OSTCBCur (703%positive,Tptr Tvoid))
 9101%Z (701%positive,Tint8))9102%Z (702%positive,Tint8))9103%Z (705%positive,Tint8).
Definition XEtid : tid := (704%positive,Int.zero).
Definition XEbyte b n := V293_encoded_memory b 0 true(encode_val Tint8(V293_byteval n)).
Definition XEcurrent := V293_encoded_memory 703%positive 0 false(encode_val(Tptr Tvoid)(Vptr XEtid)).
Definition XEmemory run nest locked := merge(XEbyte 701%positive nest)
 (merge(XEbyte 702%positive locked)(merge(XEbyte 705%positive run)XEcurrent)).
Definition XEstate M := V293_wstate XEge emp M.
Definition XEbase :=
 (V293_interrupt_globals 9101%Z 9102%Z 701%positive 702%positive **
   (CurLINV V293_witness_li XEtid ** Aie false)) ** A_dom_lenv nil.
Definition XEframe run := V293_rdy_raw_cells (((705%positive,0%Z),Tint8,V293_byteval run)::nil) XEbase.
Definition XEowned run nest locked :=
 V293_rdy_raw_cells(V293_exit_cells 701%positive 702%positive nest locked)(XEframe run).
Definition XEpre run nest locked := <||spec_done None||> ** XEowned run nest locked.
Lemma XEdomain : forall M,eq_dom_env(getlenv(XEstate M))nil.
Proof.
 intros M x tp;change(False <-> exists b,get(emp:env)x=Some(b,tp));split;
 [contradiction|intros[b H];rewrite map_emp_get in H;discriminate].
Qed.
Lemma XEcurrent_owned : XEstate XEcurrent |= CurTid XEtid.
Proof.
 exists Tvoid. exists 703%positive.
 eapply V293_wstate_star with(m1:=emp)(m2:=XEcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 703%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma XElocal : CurTid XEtid ==> CurLINV V293_witness_li XEtid.
Proof.
 intros s HS. exists([]:list logicvar). unfold LINV,V293_witness_li.
 pose proof V293_witness_li_good as Good. clear -HS Good;sep auto.
Qed.
Lemma XEglobals : XEstate emp |= V293_interrupt_globals 9101%Z 9102%Z 701%positive 702%positive.
Proof.
 unfold V293_interrupt_globals. split.
 - exists 701%positive. split;[vm_compute;reflexivity|repeat split;reflexivity].
 - exists 702%positive. split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Lemma XEbase_owned : XEstate XEcurrent |= XEbase.
Proof.
 unfold XEbase. apply astar_comm. apply astar_l_adomlenv_intro;[ |apply XEdomain].
 eapply V293_wstate_star with(m1:=emp)(m2:=XEcurrent).
 - apply map_join_comm;apply map_join_emp.
 - apply XEglobals.
 - apply astar_comm. apply astar_l_aie_intro;[apply XElocal;apply XEcurrent_owned|reflexivity].
Qed.
Ltac XEapart b :=
 apply map_join_merge;apply map_disjoint;intros[other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold XEbyte,XEcurrent;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma XEowned_actual : forall run nest locked,XEstate(XEmemory run nest locked) |= XEowned run nest locked.
Proof.
 intros. unfold XEowned,V293_exit_cells,V293_interrupt_cells,XEframe.
 cbn[V293_rdy_raw_cells].
 eapply V293_wstate_star with(m1:=XEbyte 701%positive nest)
  (m2:=merge(XEbyte 702%positive locked)(merge(XEbyte 705%positive run)XEcurrent)).
 - XEapart 701%positive.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply V293_wstate_star with(m1:=XEbyte 702%positive locked)(m2:=merge(XEbyte 705%positive run)XEcurrent).
   + XEapart 702%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + eapply V293_wstate_star with(m1:=XEbyte 705%positive run)(m2:=XEcurrent).
     * XEapart 705%positive.
     * split;[apply V293_encoded_memory_mapsto|reflexivity].
     * apply XEbase_owned.
Qed.
Theorem XEnonempty : forall run nest locked,XEstate(XEmemory run nest locked) |= XEpre run nest locked.
Proof.
 intros. unfold XEpre. apply astar_l_aop'_intro;[apply XEowned_actual|reflexivity].
Qed.
Lemma XEenv : forall run st,st |= XEframe run ->
 V293_interrupt_env 9101%Z 9102%Z 701%positive 702%positive(getgenv st)(getlenv st).
Proof.
 intros run. apply V293_raw_cells_frame_env.
 exact(V293_interrupt_builder_env 9101%Z 9102%Z 701%positive 702%positive V293_witness_li XEtid).
Qed.
Lemma XEframe_local : forall run,XEframe run ==> CurLINV V293_witness_li XEtid.
Proof.
 intros run. unfold XEframe,XEbase;cbn[V293_rdy_raw_cells].
 apply V293_star_CurLINV_r. apply V293_star_CurLINV_l.
 apply V293_star_CurLINV_r. apply V293_CurLINV_extend.
Qed.
Theorem XEfragment_checked : forall Spec sd I r ri run nest locked dispatch q,
 nest<256 -> locked<256 ->
 (V293_exit_depth nest=0 -> locked=0 ->
  InfRules Spec sd V293_witness_li I r ri(XEpre run(V293_exit_depth nest)locked)dispatch q XEtid) ->
 InfRules Spec sd V293_witness_li I r ri(XEpre run nest locked)
 (V293_OSIntExit_nesting_dispatch 9101%Z 9102%Z dispatch)
 (if V293_exit_enabled nest locked then q else XEpre run(V293_exit_depth nest)locked)XEtid.
Proof.
 intros. eapply V293_OSIntExit_nesting_dispatch_hoare;try eassumption;[apply XEenv|apply XEframe_local].
Qed.
Theorem XEdisabled_checked : forall Spec sd I r ri run nest locked dispatch,
 nest<256 -> locked<256 -> (2<=nest \/ 0<locked) ->
 InfRules Spec sd V293_witness_li I r ri(XEpre run nest locked)
 (V293_OSIntExit_nesting_dispatch 9101%Z 9102%Z dispatch)
 (XEpre run(V293_exit_depth nest)locked)XEtid.
Proof.
 intros. eapply V293_OSIntExit_disabled_hoare;try eassumption;[apply XEenv|apply XEframe_local].
Qed.
Theorem XEactual_eval : forall run nest locked,nest<256 -> locked<256 ->
 evalval(V293_OSIntExit_positive 9101%Z)(getsmem(XEstate(XEmemory run nest locked)))=
 Some(Vint32(if negb(Nat.eqb nest 0)then Int.one else Int.zero)) /\
 (0<nest -> evalval(V293_OSIntExit_previous 9101%Z)(getsmem(XEstate(XEmemory run nest locked)))=
 Some(V293_byteval(V293_exit_depth nest))) /\
 evalval(V293_OSSched_zero 9101%Z)(getsmem(XEstate(XEmemory run nest locked)))=
 Some(Vint32(if Nat.eqb nest 0 then Int.one else Int.zero)) /\
 evalval(V293_OSSched_zero 9102%Z)(getsmem(XEstate(XEmemory run nest locked)))=
 Some(Vint32(if Nat.eqb locked 0 then Int.one else Int.zero)).
Proof.
 intros run nest locked Hn Hl.
 pose proof(V293_exit_owned_eval _ _ _ _ _ _ _ _ Hn Hl(XEenv run)(XEowned_actual run nest locked))as E.
 tauto.
Qed.
Lemma XEnest_load : forall run nest locked M,nest<256 -> XEstate M |= XEpre run nest locked ->
 load Tint8 M(701%positive,0%Z)=Some(V293_byteval nest).
Proof.
 intros run nest locked M B H. apply astar_l_aop'_elim in H as[_ H].
 eapply(V293_rdy_raw_load(V293_exit_cells 701%positive 702%positive nest locked)(XEframe run)
  _ _ _ (XEstate M));[cbn[V293_exit_cells V293_interrupt_cells In];tauto|apply V293_byte_type;exact B|exact H].
Qed.
Theorem XEwrong_post_control :
 eq_dom_env(getlenv(XEstate(XEmemory 1 1 0)))nil /\
 XEstate(XEmemory 1 1 0) |= XEpre 1(V293_exit_depth 2)0 /\
 ~(XEstate(XEmemory 1 1 0) |= XEpre 1 2 0).
Proof.
 split;[apply XEdomain| ]. split;[exact(XEnonempty 1 1 0)| ].
 intro Bad. pose proof(XEnest_load 1 2 0(XEmemory 1 1 0)ltac:(lia)Bad)as Wrong.
 pose proof(XEnest_load 1 1 0(XEmemory 1 1 0)ltac:(lia)(XEnonempty 1 1 0))as Actual.
 rewrite Actual in Wrong. vm_compute in Wrong;discriminate.
Qed.
Theorem XEnesting_control :
 evalval(V293_OSIntExit_positive 9101%Z)(getsmem(XEstate(XEmemory 1 0 0)))=Some(Vint32 Int.zero) /\
 evalval(V293_OSIntExit_previous 9101%Z)(getsmem(XEstate(XEmemory 1 1 0)))=Some(V293_byteval 0) /\
 evalval(V293_OSIntExit_previous 9101%Z)(getsmem(XEstate(XEmemory 1 2 0)))=Some(V293_byteval 1) /\
 evalval(V293_OSIntExit_previous 9101%Z)(getsmem(XEstate(XEmemory 1 255 0)))=Some(V293_byteval 254) /\
 V293_exit_depth 0=0 /\ V293_exit_enabled 0 0=true /\ V293_exit_enabled 1 0=true /\
 V293_exit_enabled 2 0=false /\ V293_exit_enabled 255 0=false.
Proof.
 split;[exact(proj1(XEactual_eval 1 0 0 ltac:(lia)ltac:(lia)))| ].
 split;[exact(proj1(proj2(XEactual_eval 1 1 0 ltac:(lia)ltac:(lia)))ltac:(lia))| ].
 split;[exact(proj1(proj2(XEactual_eval 1 2 0 ltac:(lia)ltac:(lia)))ltac:(lia))| ].
 split;[exact(proj1(proj2(XEactual_eval 1 255 0 ltac:(lia)ltac:(lia)))ltac:(lia))| ].
 repeat split;reflexivity.
Qed.
Theorem XElock_control :
 evalval(V293_OSSched_zero 9102%Z)(getsmem(XEstate(XEmemory 1 0 0)))=Some(Vint32 Int.one) /\
 evalval(V293_OSSched_zero 9102%Z)(getsmem(XEstate(XEmemory 1 0 1)))=Some(Vint32 Int.zero) /\
 V293_exit_enabled 1 0=true /\ V293_exit_enabled 1 1=false.
Proof.
 split;[exact(proj2(proj2(proj2(XEactual_eval 1 0 0 ltac:(lia)ltac:(lia)))))| ].
 split;[exact(proj2(proj2(proj2(XEactual_eval 1 0 1 ltac:(lia)ltac:(lia)))))| ].
 split;reflexivity.
Qed.
(* Removing only the decrement changes the actual subsequent guard at depth1.
   These are independently owned before/after byte fixtures, not a CPU trace. *)
Theorem XEdecrement_ablation :
 evalval(V293_OSSched_zero 9101%Z)(getsmem(XEstate(XEmemory 1 1 0)))=Some(Vint32 Int.zero) /\
 evalval(V293_OSSched_zero 9101%Z)(getsmem(XEstate(XEmemory 1 0 0)))=Some(Vint32 Int.one).
Proof.
 split;[exact(proj1(proj2(proj2(XEactual_eval 1 1 0 ltac:(lia)ltac:(lia)))))|
 exact(proj1(proj2(proj2(XEactual_eval 1 0 0 ltac:(lia)ltac:(lia)))))].
Qed.
Lemma XErun_eval : forall run nest locked,run<256 ->
 evalval(V293_OSIntEnter_running 9103%Z)(getsmem(XEstate(XEmemory run nest locked)))=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)).
Proof.
 intros run nest locked B.
 assert(L:load Tint8(XEmemory run nest locked)(705%positive,0%Z)=Some(V293_byteval run)).
 { eapply(V293_rdy_raw_load(V293_exit_cells 701%positive 702%positive nest locked++
   [((705%positive,0%Z),Tint8,V293_byteval run)])XEbase _ _ _ (XEstate(XEmemory run nest locked))).
   - cbn[V293_exit_cells V293_interrupt_cells app In];tauto.
   - apply V293_byte_type;exact B.
   - exact(XEowned_actual run nest locked). }
 remember(XEmemory run nest locked)as M eqn:HM in L |- *.
 assert(N:@get var (block*type) env EnvMap emp 9103%Z=None)by(apply map_emp_get).
 assert(G:@get var (block*type) env EnvMap XEge 9103%Z=Some(705%positive,Tint8))by(vm_compute;reflexivity).
 change(evalval(V293_OSIntEnter_running 9103%Z)(XEge,emp,M)=
  Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero))).
 unfold V293_OSIntEnter_running.
 cbn[evalval evaltype get_lenv get_genv]. rewrite N,G. cbn -[load].
 change((match (match load Tint8 M(705%positive,0%Z) with
  | Some(Vint32 x)=>Some(Vint32 x) | _=>None end) with
  | Some v=>val_eq v(Vint32 Int.one) | None=>None end)=
  Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero))).
 rewrite L. unfold V293_byteval. cbn[cast_eval bop_eval val_eq].
 rewrite V293_interrupt_eq_one by exact B. destruct(Nat.eqb run 1);reflexivity.
Qed.
Theorem XErun_control :
 evalval(V293_OSIntEnter_running 9103%Z)(getsmem(XEstate(XEmemory 1 1 0)))=Some(Vint32 Int.one) /\
 evalval(V293_OSIntEnter_running 9103%Z)(getsmem(XEstate(XEmemory 0 1 0)))=Some(Vint32 Int.zero) /\
 evalval(V293_OSIntEnter_running 9103%Z)(getsmem(XEstate(XEmemory 2 1 0)))=Some(Vint32 Int.zero).
Proof.
 split;[exact(XErun_eval 1 1 0 ltac:(lia))| ].
 split;[exact(XErun_eval 0 1 0 ltac:(lia))|exact(XErun_eval 2 1 0 ltac:(lia))].
Qed.

(* Single-factor controls preserve every byte outside the changed block. *)
Theorem XErun_frame : forall r1 r2 nest locked b off,b<>705%positive ->
 get(XEmemory r1 nest locked)(b,off)=get(XEmemory r2 nest locked)(b,off).
Proof.
 intros r1 r2 nest locked b off B.
 assert(N:forall n,get(XEbyte 705%positive n)(b,off)=None).
 { intros n. apply V293_encoded_memory_outside. left;exact B. }
 unfold XEmemory. repeat rewrite map_merge_semp by reflexivity. rewrite !N. reflexivity.
Qed.
Theorem XEnest_frame : forall run n1 n2 locked b off,b<>701%positive ->
 get(XEmemory run n1 locked)(b,off)=get(XEmemory run n2 locked)(b,off).
Proof.
 intros run n1 n2 locked b off B.
 assert(N:forall n,get(XEbyte 701%positive n)(b,off)=None).
 { intros n. apply V293_encoded_memory_outside. left;exact B. }
 unfold XEmemory. repeat rewrite map_merge_semp by reflexivity. rewrite !N. reflexivity.
Qed.
Theorem XElock_frame : forall run nest l1 l2 b off,b<>702%positive ->
 get(XEmemory run nest l1)(b,off)=get(XEmemory run nest l2)(b,off).
Proof.
 intros run nest l1 l2 b off B.
 assert(N:forall n,get(XEbyte 702%positive n)(b,off)=None).
 { intros n. apply V293_encoded_memory_outside. left;exact B. }
 unfold XEmemory. repeat rewrite map_merge_semp by reflexivity. rewrite !N. reflexivity.
Qed.
