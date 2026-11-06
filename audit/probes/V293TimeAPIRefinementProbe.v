(* Same old heap and program as the real-call checkpoint, now to return.
   Only a finite path without interrupt interleaving is claimed. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPIRefinement.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPILifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.audit.probes.V293TimeAPILifecycleProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.audit.probes.V293TimeAPICallProbe.
Require Import CertiOS.audit.probes.V293TimeReadyEntryProbe.
Require Import CertiOS.audit.probes.V293TimeReadySharedProbe.
Require Import CertiOS.audit.probes.V293TimeReadyAPIProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

(* The call frame contains exact spatial ownership, not an arbitrary remainder.
   Empty builder facts are added separately on the same actual call endpoint. *)
Lemma Rjoint : forall op ct clock lg tmp M,
  Jstate op M(TRabstract ct clock) |= Amapsto(161%positive,0%Z) Tint32 true Vundef **
    (Amapsto(160%positive,0%Z) Tint32 true tmp ** (Ccore ** CurTid ct)) ->
  Jstate op M(TRabstract ct clock) |= Amapsto(161%positive,0%Z) Tint32 true Vundef **
    (Amapsto(160%positive,0%Z) Tint32 true tmp ** Cframe op ct lg).
Proof.
  intros op ct clock lg tmp M Held.
  pose proof(Linsert _ _ _ _ _ Held(Jempty op ct lg))as Packed.
  unfold Cframe. clear -Packed. sep auto.
Qed.
Lemma Rnamed : forall op ct clock M tmp,
  Jstate op M(TRabstract ct clock) |= Amapsto(161%positive,0%Z) Tint32 true Vundef **
    (Amapsto(160%positive,0%Z) Tint32 true tmp ** (Ccore ** CurTid ct)) ->
  Jstate op M(TRabstract ct clock) |= V293_time_cell true 1003%Z 161%positive Vundef **
    (V293_time_cell true 1002%Z 160%positive tmp **
      (V293_time_cell false 1001%Z 150%positive(Vint32 clock) **
        (V293_time_ready_fields 80%positive 81%positive 82%positive clock ** CurTid ct))).
Proof.
  intros op ct clock M tmp Held.
  unfold Ccore,V293_time_ready_core in Held. sep normal in Held. sep destruct Held.
  assert(Slot:get(TRabstract ct clock)ostmid=Some(ostm x)).
  { change(get(getabst(Jstate op M(TRabstract ct clock)))ostmid=Some(ostm x)).
    eapply V293_star_abst_get_l with(p:=V293_time_ready_fields 80%positive 81%positive 82%positive x)(q:=Atrue).
    - apply V293_time_ready_fields_clock.
    - clear -Held. sep auto. }
  unfold TRabstract in Slot. rewrite map_get_set in Slot. inversion Slot;subst x.
  pose proof(Linsert _ _ _ _ _ Held(Lnames op))as Named.
  unfold V293_time_cell,Aptrmapsto. clear -Named. sep auto.
Qed.
Definition Rfinal caller M O op : RstateOP := (JGE,caller,M,empisr,(true,[],[]),O,op).
Definition Rcritical M O op : RstateOP := (JGE,JLE,M,empisr,(false,[],[true]),O,op).
Definition RsetPrefix caller ks Ma Mc :=
  V293_local_steps Cprogram
    (curs(V293_TimeSet_body 1001%Z 1002%Z 1003%Z),
      (kenil,kcall 202%Z(V293_TimeSet_body 1001%Z 1002%Z 1003%Z)caller ks))
    ((JGE,JLE,Ma),empisr,(true,[],[]))
    (curs(sprim excrit),(kenil,kseq sret(kcall 202%Z(V293_TimeSet_body 1001%Z 1002%Z 1003%Z)caller ks)))
    ((JGE,JLE,Mc),empisr,(false,[],[true])).
Lemma Rset_map : forall ct old n, set(TRabstract ct old)ostmid(ostm n)=TRabstract ct n.
Proof.
  intros. apply OSAbstMod.extensionality. intro id.
  change(get(set(TRabstract ct old)ostmid(ostm n))id=get(TRabstract ct n)id).
  unfold TRabstract. destruct id;repeat rewrite map_get_set' by discriminate;
    repeat rewrite map_get_set;reflexivity.
Qed.
Lemma Rcurrent_good : forall ct, GoodFunAsrt(CurTid ct) /\ can_change_aop(CurTid ct).
Proof. intros. unfold CurTid,Agvarmapsto,Aptrmapsto. simpl. auto. Qed.

Theorem Rset_actual_refinement : forall caller ks ct clock lg n,
  exists Ma Mc Mf,
    CsetExec caller ks ct clock n Ma /\
    Jstate(V293_time_set_action n)Ma(TRabstract ct clock) |= Ccore ** JsetPre ct lg n /\
    RsetPrefix caller ks Ma Mc /\
    spec_step V293_scheduler(V293_time_set_action n)(TRabstract ct clock)(END None)(TRabstract ct n) /\
    Rcritical Mc(TRabstract ct n)(END None) |= Ccore ** Atrue /\
    LsetExec caller ks ct clock n Mf /\
    Rfinal caller Mf(TRabstract ct n)(END None) |= Ccore ** CurTid ct /\
    freels(getaddr JLE)Mc Mf.
Proof.
  intros caller ks ct clock lg n.
  pose proof(V293_time_set_call_entry Cprogram ks JGE caller(TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock)(V293_time_set_action n)202%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive n(Ccore ** CurTid ct))as Entry.
  assert(P:Cprogram 202%Z=Some(V293_TimeSet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2 RAactual_entries)). }
  specialize(Entry P ltac:(discriminate)(Cfresh ct clock _ (or_introl eq_refl))
    (Cfresh ct clock _ (or_intror eq_refl))ltac:(discriminate)).
  rewrite Ccallee in Entry. specialize(Entry(Jcore_and_current ct clock(V293_time_set_action n))).
  destruct Entry as(Mp&Ma&ParameterStore&Mem&Call&Owned). subst Ma.
  pose proof(Cpack_set ct clock lg n _ (Rjoint _ ct clock lg _ _ Owned))as Joint.
  pose proof(Rnamed _ ct clock _ _ Owned)as Named.
  assert(Reorder:Jstate(V293_time_set_action n)(allocb Mp 161%positive 0%Z(typelen Tint32))(TRabstract ct clock) |=
    V293_time_cell true 1003%Z 161%positive Vundef **
      (V293_time_cell false 1001%Z 150%positive(Vint32 clock) **
        (V293_time_cell true 1002%Z 160%positive(Vint32 n) **
          (V293_time_ready_fields 80%positive 81%positive 82%positive clock ** CurTid ct)))).
  { clear -Named. sep auto. }
  unfold Jstate in Reorder. rewrite <-Ccallee in Reorder.
  destruct(Rcurrent_good ct)as[Good Free].
  destruct(V293_time_set_body_refinement 80%positive 81%positive 82%positive Cprogram V293_scheduler ks
    JGE caller _ empisr true [] [] (TRabstract ct clock)1001%Z 1002%Z 1003%Z
    150%positive 160%positive 161%positive clock n(CurTid ct)202%Z ltac:(discriminate)Good Free Reorder)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  rewrite Ccallee in Prefix,Closed,Suffix,Freed. rewrite Rset_map in Step,Closed,Final.
  eexists. exists Mc. exists Mf. split;[exact Call | ]. split;[exact Joint | ].
  split;[exact Prefix | ]. split;[exact Step | ]. split;[exact Closed | ]. split.
  - unfold LsetExec. eapply V293_local_trans;[exact Call | ].
    eapply V293_local_trans;[exact Prefix | exact Suffix].
  - split;assumption.
Qed.

Theorem Rget_actual_refinement : forall caller ks ct clock lg,
  exists Ma Mc Mf,
    CgetExec caller ks ct clock Ma /\
    Jstate V293_time_get_action Ma(TRabstract ct clock) |= Ccore ** JgetPre ct lg /\
    spec_step V293_scheduler V293_time_get_action(TRabstract ct clock)(END(Some(Vint32 clock)))(TRabstract ct clock) /\
    Rcritical Mc(TRabstract ct clock)(END(Some(Vint32 clock))) |= Ccore ** Atrue /\
    LgetExec caller ks ct clock Mf /\
    Rfinal caller Mf(TRabstract ct clock)(END(Some(Vint32 clock))) |= Ccore ** CurTid ct /\
    freels(getaddr JLE)Mc Mf.
Proof.
  intros caller ks ct clock lg.
  pose proof(V293_time_get_call_entry Cprogram ks JGE caller(TRmemory ct clock)
    empisr (true,[],[]) (TRabstract ct clock)V293_time_get_action 203%Z 1001%Z 1002%Z 1003%Z
    160%positive 161%positive(Ccore ** CurTid ct))as Entry.
  assert(P:Cprogram 203%Z=Some(V293_TimeGet_function 1001%Z 1002%Z 1003%Z)).
  { exact(proj1(proj2(proj2 RAactual_entries))). }
  specialize(Entry P ltac:(discriminate)(Cfresh ct clock _ (or_introl eq_refl))
    (V293_time_fresh_after_alloc(TRmemory ct clock)160%positive 161%positive ltac:(discriminate)
      (Cfresh ct clock _ (or_intror eq_refl)))).
  rewrite Ccallee in Entry. specialize(Entry(Jcore_and_current ct clock V293_time_get_action)).
  cbn zeta in Entry. destruct Entry as[Call Owned].
  pose proof(Cpack_get ct clock lg _ (Rjoint _ ct clock lg _ _ Owned))as Joint.
  pose proof(Rnamed _ ct clock _ _ Owned)as Named.
  unfold Jstate in Named. rewrite <-Ccallee in Named.
  destruct(Rcurrent_good ct)as[Good Free].
  destruct(V293_time_get_body_refinement 80%positive 81%positive 82%positive Cprogram V293_scheduler ks
    JGE caller _ empisr true [] [] (TRabstract ct clock)1001%Z 1002%Z 1003%Z
    150%positive 160%positive 161%positive clock Vundef(CurTid ct)203%Z ltac:(discriminate)Good Free Named)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  rewrite Ccallee in Prefix,Closed,Suffix,Freed.
  eexists. exists Mc. exists Mf. split;[exact Call | ]. split;[exact Joint | ].
  split;[exact Step | ]. split;[exact Closed | ]. split.
  - unfold LgetExec. eapply V293_local_trans;[exact Call | ].
    eapply V293_local_trans;[exact Prefix | exact Suffix].
  - split;assumption.
Qed.

Lemma Rclock : forall le M ct clock op ir aux R,
  (JGE,le,M,ir,aux,TRabstract ct clock,op) |= Ccore ** R ->
  load Tint32 M(150%positive,0%Z)=Some(Vint32 clock).
Proof.
  intros le M ct clock op ir aux R Held.
  destruct(V293_time_ready_clock_agreement 80%positive 81%positive 82%positive 150%positive R _ Held)
    as(actual&Slot&Load).
  change(get(TRabstract ct clock)ostmid=Some(ostm actual))in Slot.
  unfold TRabstract in Slot. rewrite map_get_set in Slot. inversion Slot;subst actual. exact Load.
Qed.

Lemma Rlocals_removed : forall Mc Mf,
  freels(getaddr JLE)Mc Mf ->
  forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None.
Proof.
  intros Mc Mf Fs k K.
  change(freels((160%positive,Tint32)::(161%positive,Tint32)::nil)Mc Mf)in Fs.
  inversion Fs as [ | b1 t1 ls1 M0 M1 M2 F1 Fs1];subst.
  inversion Fs1 as [ | b2 t2 ls2 M3 M4 M5 F2 Fs2];subst.
  inversion Fs2;subst. unfold free in F1,F2. split.
  - erewrite V293_freeb_outside;[ | exact F2 | left;discriminate].
    replace(Z.of_nat k)with(0+Z.of_nat k)%Z by reflexivity.
    eapply V293_freeb_removed;[exact F1 | exact K].
  - replace(Z.of_nat k)with(0+Z.of_nat k)%Z by reflexivity.
    eapply V293_freeb_removed;[exact F2 | exact K].
Qed.

(* Same actual critical heap, same code/IRQ/action. Only the abstract clock
   slot changes. The rejection therefore cannot be an action-guard shortcut. *)
Theorem Rset_ghost_omission_control : forall caller ks ct clock n,
  n<>clock -> exists Ma Mc Mf,
    CsetExec caller ks ct clock n Ma /\ RsetPrefix caller ks Ma Mc /\
    spec_step V293_scheduler(V293_time_set_action n)(TRabstract ct clock)(END None)(TRabstract ct n) /\
    load Tint32 Mc(150%positive,0%Z)=Some(Vint32 n) /\
    Rcritical Mc(TRabstract ct n)(END None) |= Ccore ** Atrue /\
    ~ Rcritical Mc(TRabstract ct clock)(END None) |= Ccore ** Atrue /\
    LsetExec caller ks ct clock n Mf /\
    Rfinal caller Mf(TRabstract ct n)(END None) |= Ccore ** CurTid ct /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None).
Proof.
  intros caller ks ct clock n Different.
  destruct(Rset_actual_refinement caller ks ct clock nil n)as(Ma&Mc&Mf&Call&Joint&Prefix&Step&Closed&Exec&Final&Freed).
  pose proof(Rclock _ _ ct n _ _ _ _ Closed)as Load.
  exists Ma. exists Mc. exists Mf. split;[exact Call | ]. split;[exact Prefix | ].
  split;[exact Step | ]. split;[exact Load | ]. split;[exact Closed | ]. split.
  - intro Wrong. pose proof(Rclock _ _ ct clock _ _ _ _ Wrong)as Old. congruence.
  - split;[exact Exec | ]. split;[exact Final | ]. apply Rlocals_removed with Mc. exact Freed.
Qed.

Theorem Rset_two_argument_control : forall caller ks ct clock n bad,
  bad<>n -> exists Mn Mb,
    LsetExec caller ks ct clock n Mn /\ LsetExec caller ks ct clock bad Mb /\
    Rfinal caller Mn(TRabstract ct n)(END None) |= Ccore ** CurTid ct /\
    Rfinal caller Mb(TRabstract ct bad)(END None) |= Ccore ** CurTid ct /\
    load Tint32 Mn(150%positive,0%Z)=Some(Vint32 n) /\
    load Tint32 Mb(150%positive,0%Z)=Some(Vint32 bad) /\
    get(TRabstract ct n)ostmid=Some(ostm n) /\ get(TRabstract ct bad)ostmid=Some(ostm bad) /\
    load Tint32 Mb(150%positive,0%Z)<>Some(Vint32 n).
Proof.
  intros caller ks ct clock n bad Different.
  destruct(Rset_actual_refinement caller ks ct clock nil n)as(An&Cn&Mn&Calln&Jointn&Prefixn&Stepn&Closedn&Execn&Finaln&Freedn).
  destruct(Rset_actual_refinement caller ks ct clock nil bad)as(Ab&Cb&Mb&Callb&Jointb&Prefixb&Stepb&Closedb&Execb&Finalb&Freedb).
  pose proof(Rclock _ _ ct n _ _ _ _ Finaln)as Loadn.
  pose proof(Rclock _ _ ct bad _ _ _ _ Finalb)as Loadb.
  exists Mn. exists Mb. split;[exact Execn | ]. split;[exact Execb | ].
  split;[exact Finaln | ]. split;[exact Finalb | ]. split;[exact Loadn | ]. split;[exact Loadb | ].
  split;[apply map_get_set | ]. split;[apply map_get_set | ]. congruence.
Qed.

Theorem Rget_return_control : forall caller ks ct clock,
  exists Ma Mc Mf,
    CgetExec caller ks ct clock Ma /\
    spec_step V293_scheduler V293_time_get_action(TRabstract ct clock)(END(Some(Vint32 clock)))(TRabstract ct clock) /\
    LgetExec caller ks ct clock Mf /\
    Rfinal caller Mf(TRabstract ct clock)(END(Some(Vint32 clock))) |= Ccore ** CurTid ct /\
    load Tint32 Mf(150%positive,0%Z)=Some(Vint32 clock) /\
    freels(getaddr JLE)Mc Mf /\
    (forall k,k<4 -> get Mf(160%positive,Z.of_nat k)=None /\ get Mf(161%positive,Z.of_nat k)=None).
Proof.
  intros caller ks ct clock.
  destruct(Rget_actual_refinement caller ks ct clock nil)as(Ma&Mc&Mf&Call&Joint&Step&Closed&Exec&Final&Freed).
  exists Ma. exists Mc. exists Mf. split;[exact Call | ]. split;[exact Step | ].
  split;[exact Exec | ]. split;[exact Final | ]. split;[eapply Rclock;exact Final | ].
  split;[exact Freed | ]. apply Rlocals_removed with Mc. exact Freed.
Qed.
