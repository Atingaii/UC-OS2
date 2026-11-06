(* Real void-return/free tail. No hook implementation is supplied here. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCallContext.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickScanSlot.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickPostHookCore.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickChainOpen.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLosslessFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSwitchBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tick_free_owned : forall ge le M ir aux O op b tp v R,
 (ge,le,M,ir,aux,O,op) |= Amapsto(b,0%Z)tp true v ** R ->
 exists Mf, free tp b M=Some Mf /\ (ge,le,Mf,ir,aux,O,op) |= R.
Proof.
 intros ge le M ir aux O op b tp v R Held.
 apply sat_split in Held.
 destruct Held as(mc&mr&oc&orr&JM&JO&[Cell Empty]&Rest).
 change(oc=emp)in Empty;subst oc.
 apply map_join_comm in JO;apply map_join_emp' in JO;subst orr.
 exists mr;split;[ |exact Rest].
 unfold free;destruct Cell as(bytes&Encoding&Points);subst bytes.
 rewrite <- (encode_val_length tp v).
 eapply free_locality2';[exact JM|exact Points].
Qed.

Lemma V293_tick_freels_execution : forall al P ks ge le M Mf,
 freels al M Mf ->
 cstepstar P(curs(sfree al None),(kenil,ks))(ge,le,M)
  (curs(sfree nil None),(kenil,ks))(ge,le,Mf).
Proof.
 intros al P ks ge le M Mf Free;induction Free.
 - apply c_stepstar0.
 - eapply c_stepstarn.
   + eapply stmt_step;[reflexivity| ];eapply sfree_step;[reflexivity|reflexivity|exact H].
   + exact IHFree.
Qed.

(* Ownership yields exact residual memory, independent of variable-name order.
   Environment-dependent local bindings must be removed before this interface. *)
Theorem V293_tick_owned_void_return : forall P ks ge caller M ir aux O op
 ptcb saved bc bs f body scan R,
 ptcb<>saved -> GoodFunAsrt R ->
 (ge,V293_tick_locals ptcb saved bc bs,M,ir,aux,O,op) |=
  Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
  (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) ** R) ->
 exists Mf,
 cstepstar P(curs sret,(kenil,kcall f body caller ks))
  (ge,V293_tick_locals ptcb saved bc bs,M)
  (curs(sskip None),(kenil,ks))(ge,caller,Mf) /\
 (ge,caller,Mf,ir,aux,O,op) |= R /\
 (forall k,k<4 -> get Mf(bc,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
 intros P ks ge caller M ir aux O op ptcb saved bc bs f body scan R Different Good Held.
 pose proof(V293_tick_local_addresses ptcb saved bc bs Different)as Layout.
 apply Permutation_sym in Layout;apply Permutation_length_2_inv in Layout.
 assert(Free:exists Mf,freels(getaddr(V293_tick_locals ptcb saved bc bs))M Mf /\
   (ge,V293_tick_locals ptcb saved bc bs,Mf,ir,aux,O,op) |= R).
 { destruct Layout as[Layout|Layout].
   - destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Held)as(M1&F1&Rest).
     destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Rest)as(Mf&F2&Returned).
     exists Mf;split;[rewrite Layout;econstructor;[exact F1|econstructor;[exact F2|constructor]]|exact Returned].
   - assert(Swapped:(ge,V293_tick_locals ptcb saved bc bs,M,ir,aux,O,op) |=
       Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
       (Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan ** R)).
     { clear -Held;sep auto. }
     destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Swapped)as(M1&F1&Rest).
     destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Rest)as(Mf&F2&Returned).
     exists Mf;split;[rewrite Layout;econstructor;[exact F1|econstructor;[exact F2|constructor]]|exact Returned]. }
 destruct Free as(Mf&Free&Returned).
 assert(Exec:cstepstar P(curs sret,(kenil,kcall f body caller ks))
  (ge,V293_tick_locals ptcb saved bc bs,M)
  (curs(sskip None),(kenil,ks))(ge,caller,Mf)).
 { eapply c_stepstarn.
   - eapply stmt_step;[reflexivity| ];eapply sret_step;reflexivity.
   - eapply V293_cstepstar_trans;[eapply V293_tick_freels_execution;exact Free| ].
     eapply c_stepstarn;[eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity|apply c_stepstar0]. }
 assert(Absent:forall al M0 M1,freels al M0 M1 ->
   forall b i,get M0(b,i)=None -> get M1(b,i)=None).
 { intros al M0 M1 Fs;induction Fs;intros c i Del;[exact Del| ].
   apply IHFs. unfold free in H.
   destruct(Pos.eq_dec c b)as[Same|Other].
   - subst c.
     destruct(Z_lt_dec i 0)as[Before|After].
     + erewrite V293_freeb_outside;[exact Del|exact H|right;left;exact Before].
     + destruct(Z_lt_dec i(Z.of_nat(typelen t)))as[Inside|Outside].
       * replace i with(0+Z.of_nat(Z.to_nat i))%Z by lia.
         eapply V293_freeb_removed;[exact H|lia].
       * erewrite V293_freeb_outside;[exact Del|exact H|right;right;lia].
   - erewrite V293_freeb_outside;[exact Del|exact H|left;exact Other]. }
 assert(Removed:forall al M0 M1,freels al M0 M1 ->
   forall b tp k,In(b,tp)al -> k<typelen tp -> get M1(b,Z.of_nat k)=None).
 { intros al M0 M1 Fs;induction Fs;intros c tp k Member Positive;[contradiction| ].
   destruct Member as[E|Member].
   - inversion E;subst. eapply Absent;[exact Fs| ].
     replace (Z.of_nat k) with(0+Z.of_nat k)%Z by lia.
     eapply V293_freeb_removed;[exact H|exact Positive].
   - eapply IHFs;[exact Member|exact Positive]. }
 exists Mf;split;[exact Exec| ]. split.
 - eapply good_fun_asrt_absop;[exact Good|exact Returned].
 - intros k K;split.
     * eapply Removed with(tp:=Tptr V293_tcb_type);[exact Free| |exact K].
       eapply Permutation_in;[apply Permutation_sym;apply V293_tick_local_addresses;exact Different|left;reflexivity].
     * eapply Removed with(tp:=Tint32);[exact Free| |exact K].
       eapply Permutation_in;[apply Permutation_sym;apply V293_tick_local_addresses;exact Different|right;left;reflexivity].
Qed.

Section ReturnTail.
Variables(bindings:list(V293_tick_task*(taskstatus*val)))(idle:addrval)
 (br bg bp bn bc bs bu bh:block)(run:nat)(R:asrt).
Definition V293_tick_return_resources ir si ci :=
 <||END None||> ** OS[ir,false,si,ci] **
 (SWINV(V293_time_ready_inv br bg bp bn) **
  (if Nat.eqb run 1 then
    EX actual:list(V293_tick_task*(taskstatus*val)),
     (V293_owned_record_cells(V293_tick_chain_residual actual idle) **
      (V293_owned_record_cells(V293_tick_post_hook_core_globals bindings idle bu bh run) ** R)) **
      [|V293_tick_pend_choices bindings actual|]
   else V293_owned_record_cells(V293_tick_chain_missing bindings idle) **
      (V293_owned_record_cells(V293_tick_post_hook_core_globals bindings idle bu bh run) ** R))).

Lemma V293_tick_return_factor : forall ir si ci,
 V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
   (V293_tick_saved_frame bs R)Vundef ir si ci ==>
 EX scan:val,Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan **
  (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) ** V293_tick_return_resources ir si ci).
Proof.
 intros ir si ci s Held.
 unfold V293_tick_scan_switch_result in Held.
 unfold V293_tick_return_resources;destruct(Nat.eqb run 1)eqn:Running.
 - destruct Held as[actual Held]. exists(Vptr idle).
   unfold V293_tick_post_hook_core_frame,V293_tick_saved_frame,V293_owned_record_cell in Held.
   assert(Packed:s |= Amapsto(bc,0%Z)(Tptr V293_tcb_type)true(Vptr idle) **
     (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
      (<||END None||> ** OS[ir,false,si,ci] **
       (SWINV(V293_time_ready_inv br bg bp bn) **
        ((V293_owned_record_cells(V293_tick_chain_residual actual idle) **
          (V293_owned_record_cells(V293_tick_post_hook_core_globals bindings idle bu bh run) ** R)) **
          [|V293_tick_pend_choices bindings actual|]))))).
   { unfold V293_tick_pointer_cell in Held;clear -Held;sep auto. }
   clear -Packed;sep auto.
 - exists Vundef.
   unfold V293_tick_scan_supplement,V293_tick_saved_frame,V293_owned_record_cell in Held;
     clear -Held;sep auto.
Qed.

Lemma V293_tick_return_resources_good : forall ir si ci,
 GoodFunAsrt R -> GoodFunAsrt(V293_tick_return_resources ir si ci).
Proof.
 intros ir si ci Good;unfold V293_tick_return_resources.
 split;[exact I| ]. split;[cbn[GoodFunAsrt];repeat split;exact I| ]. split.
 - exact(proj1(V293_sched_critical_good(V293_time_ready_inv br bg bp bn)nil nil)).
 - destruct(Nat.eqb run 1).
   + intro actual;split;[ |exact I]. split.
     * apply V293_inv_function_assertion;apply V293_owned_cells_good.
     * split;[apply V293_inv_function_assertion;apply V293_owned_cells_good|exact Good].
   + split;[apply V293_inv_function_assertion;apply V293_owned_cells_good| ].
     split;[apply V293_inv_function_assertion;apply V293_owned_cells_good|exact Good].
Qed.

(* Stable interface: the exact existing suffix result enables real return,
   deallocation of both local objects, and caller-environment restoration. *)
Theorem V293_tick_return_tail : forall P ks ge caller M ir si ci O ptcb saved f body,
 ptcb<>saved -> GoodFunAsrt R ->
 (ge,V293_tick_locals ptcb saved bc bs,M,ir,(false,si,ci),O,END None) |=
 V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
   (V293_tick_saved_frame bs R)Vundef ir si ci ->
 exists Mf,
 V293_local_steps P(curs(sskip None),(kenil,kseq sret(kcall f body caller ks)))
  ((ge,V293_tick_locals ptcb saved bc bs,M),ir,(false,si,ci))
  (curs(sskip None),(kenil,ks))((ge,caller,Mf),ir,(false,si,ci)) /\
 (ge,caller,Mf,ir,(false,si,ci),O,END None) |= V293_tick_return_resources ir si ci /\
 (forall k,k<4 -> get Mf(bc,Z.of_nat k)=None /\ get Mf(bs,Z.of_nat k)=None).
Proof.
 intros P ks ge caller M ir si ci O ptcb saved f body Different Good Held.
 apply V293_tick_return_factor in Held;destruct Held as[scan Held].
 destruct(V293_tick_owned_void_return P ks ge caller M ir(false,si,ci)O(END None)
  ptcb saved bc bs f body scan _ Different(V293_tick_return_resources_good ir si ci Good)Held)
  as(Mf&Exec&Returned&Removed).
 exists Mf;split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   apply V293_csteps_local;exact Exec.
 - split;assumption.
Qed.
End ReturnTail.

(* Callee-only bindings own no bytes and are not transported to the caller. *)
Lemma V293_tick_result_forget_bindings : forall bindings idle br bg bp bn bc bs bu bh run B R ir si ci,
 (B ==> Aemp) ->
 V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
  (V293_tick_saved_frame bs(B ** R))Vundef ir si ci ==>
 V293_tick_scan_switch_result bindings idle br bg bp bn bc bu bh run
  (V293_tick_saved_frame bs R)Vundef ir si ci.
Proof.
 intros bindings idle br bg bp bn bc bs bu bh run B R ir si ci Empty.
 assert(Frame:V293_tick_saved_frame bs(B ** R) ==> V293_tick_saved_frame bs R).
 { intros s Held.
   assert(H:s |= B ** V293_tick_saved_frame bs R).
   { unfold V293_tick_saved_frame in *;clear -Held;sep auto. }
   eapply astar_mono in H;[ |exact Empty|intros st Hs;exact Hs].
   clear -H;sep auto. }
 unfold V293_tick_scan_switch_result,V293_tick_post_hook_core_frame,V293_tick_scan_supplement.
 destruct(Nat.eqb run 1).
 - intros s[actual H];exists actual.
   eapply astar_mono;[ |intros st Hs;exact Hs|exact H].
   repeat match goal with |- (?p ** ?q) ==> (?p ** ?r) =>
     apply astar_mono;[intros st Hs;exact Hs| ] end.
   exact Frame.
 - repeat match goal with |- (?p ** ?q) ==> (?p ** ?r) =>
     apply astar_mono;[intros st Hs;exact Hs| ] end.
   exact Frame.
Qed.
