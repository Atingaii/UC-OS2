(* Three real writable bytes and an unrelated sentinel. No initialized-kernel
   reachability or whole-function execution is asserted by this fixture. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlExecution.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition CEge : env := set(set(set emp 801%Z(901%positive,Tint8))
 802%Z(902%positive,Tint8))803%Z(903%positive,Tint8).
Definition CEle : env := emp.
Definition CEmemory r n l :=
 V293_put_byte(V293_put_byte(V293_put_byte(V293_put_byte emp
 (904%positive,7%Z)77)(901%positive,0%Z)r)(903%positive,0%Z)l)(902%positive,0%Z)n.

Lemma CEbindings :
 V293_interrupt_env 801%Z 802%Z 901%positive 902%positive CEge CEle /\
 V293_interrupt_env 802%Z 803%Z 902%positive 903%positive CEge CEle.
Proof. vm_compute;repeat split;reflexivity. Qed.

Lemma CEloads : forall r n l,r<256 ->n<256 ->l<256 ->
 load Tint8(CEmemory r n l)(901%positive,0%Z)=Some(V293_byteval r) /\
 load Tint8(CEmemory r n l)(902%positive,0%Z)=Some(V293_byteval n) /\
 load Tint8(CEmemory r n l)(903%positive,0%Z)=Some(V293_byteval l) /\
 (exists v,get(CEmemory r n l)(902%positive,0%Z)=Some(true,v)).
Proof.
 intros r n l R N L;unfold CEmemory.
 split.
 - repeat rewrite V293_put_byte_other_load by discriminate;apply V293_put_byte_load;exact R.
 - split;[apply V293_put_byte_load;exact N| ];split.
   + repeat rewrite V293_put_byte_other_load by discriminate;apply V293_put_byte_load;exact L.
   + unfold V293_put_byte;rewrite map_get_set;eexists;reflexivity.
Qed.

Theorem CEexit_case : forall P ks sd O n l dispatch,n<256 ->l<256 ->
 exists Mf,
 V293_control_read 901%positive 902%positive 903%positive(CEmemory 1 n l)=Some(V293_control 1 n l) /\
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch 802%Z 803%Z dispatch),(kenil,ks))(CEge,CEle,CEmemory 1 n l)
 (curs(V293_control_exit_residual n l dispatch),(kenil,ks))(CEge,CEle,Mf) /\
 V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control_exit(V293_control 1 n l)) /\
 V293_control_step sd V293_control_Exit(O,V293_control 1 n l)
 (V293_control_Core(V293_control_exit_code(V293_control 1 n l)))(O,V293_control_exit(V293_control 1 n l)) /\
 (forall a,a<>(902%positive,0%Z) ->get Mf a=get(CEmemory 1 n l)a).
Proof.
 intros P ks sd O n l dispatch N L.
 destruct(CEloads 1 n l ltac:(lia)N L)as[Run[Nest[Lock W]]].
 destruct(V293_control_exit_execution_bridge P ks sd O CEge CEle(CEmemory 1 n l)
 802%Z 803%Z 901%positive 902%positive 903%positive n l dispatch N L
 ltac:(discriminate)ltac:(discriminate)(proj2 CEbindings)Run Nest Lock W)
 as[Mf[Trace[Read[Step Frame]]]].
 exists Mf;split;[apply V293_control_read_exact;try assumption;lia| ].
 split;[exact Trace| ];split;[exact Read| ];split;assumption.
Qed.

Theorem CEenter_case : forall P ks sd O r n l,r<256 ->n<256 ->l<256 ->
 exists Mf,
 cstepstar P(curs(V293_OSIntEnter_updates 801%Z 802%Z),(kenil,ks))(CEge,CEle,CEmemory r n l)
 (curs(sskip None),(kenil,ks))(CEge,CEle,Mf) /\
 V293_control_read 901%positive 902%positive 903%positive Mf=Some(V293_control_enter(V293_control r n l)) /\
 V293_control_step sd V293_control_Enter(O,V293_control r n l)
 (V293_control_Core(spec_done None))(O,V293_control_enter(V293_control r n l)) /\
 (forall a,a<>(902%positive,0%Z) ->get Mf a=get(CEmemory r n l)a).
Proof.
 intros P ks sd O r n l R N L.
 destruct(CEloads r n l R N L)as[Run[Nest[Lock W]]].
 eapply V293_control_enter_execution_bridge with(br:=901%positive)(bn:=902%positive)(bl:=903%positive);
 try exact Run;try exact Nest;try exact Lock;try exact W;try discriminate.
 - unfold V293_control_valid;cbn;auto.
 - exact(proj1 CEbindings).
Qed.

(* The very same low-level program and dispatch statement; only the lock
   byte differs. Both runs reach and evaluate the actual depth/lock guards. *)
Theorem CElock_pair : forall P ks n dispatch,n<=1 ->
 exists M0,exists M1,
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch 802%Z 803%Z dispatch),(kenil,ks))(CEge,CEle,CEmemory 1 n 0)
 (curs dispatch,(kenil,ks))(CEge,CEle,M0) /\
 cstepstar P(curs(V293_OSIntExit_nesting_dispatch 802%Z 803%Z dispatch),(kenil,ks))(CEge,CEle,CEmemory 1 n 1)
 (curs(sskip None),(kenil,ks))(CEge,CEle,M1) /\
 V293_control_read 901%positive 902%positive 903%positive M0=Some(V293_control 1 0 0) /\
 V293_control_read 901%positive 902%positive 903%positive M1=Some(V293_control 1 0 1) /\
 (forall a,a<>(903%positive,0%Z) ->get(CEmemory 1 n 1)a=get(CEmemory 1 n 0)a).
Proof.
 intros P ks n dispatch N.
 destruct(CEexit_case P ks(fun _ _=>True)emp n 0 dispatch ltac:(lia)ltac:(lia))
 as[M0[_[T0[R0[_ F0]]]]].
 destruct(CEexit_case P ks(fun _ _=>True)emp n 1 dispatch ltac:(lia)ltac:(lia))
 as[M1[_[T1[R1[_ F1]]]]].
 assert(Depth:Nat.pred n=0)by lia.
 unfold V293_control_exit_residual in T0,T1;rewrite Depth in T0,T1;cbn in T0,T1.
 unfold V293_control_exit in R0,R1;cbn in R0,R1;rewrite Depth in R0,R1.
 exists M0;exists M1;split;[exact T0| ];split;[exact T1| ];split;[exact R0| ];split;[exact R1| ].
 intros a Outside;unfold CEmemory.
 destruct(addr_eq_dec a(902%positive,0%Z))as[E|E].
 - subst a;unfold V293_put_byte;repeat rewrite map_get_set;reflexivity.
 - repeat rewrite(V293_put_byte_other _ (902%positive,0%Z)_ a E).
   repeat rewrite(V293_put_byte_other _ (903%positive,0%Z)_ a Outside);reflexivity.
Qed.

(* Explicit boundary observations accompany generic real execution above. *)
Theorem CEboundaries :
 V293_control_enter_memory 902%positive(V293_control 1 255 0)(CEmemory 1 255 0)=CEmemory 1 255 0 /\
 V293_control_enter_memory 902%positive(V293_control 0 254 0)(CEmemory 0 254 0)=CEmemory 0 254 0 /\
 V293_control_enter_memory 902%positive(V293_control 2 0 0)(CEmemory 2 0 0)=CEmemory 2 0 0 /\
 V293_control_exit_residual 0 0(scall 999%Z nil)=scall 999%Z nil /\
 V293_control_exit_residual 1 0(scall 999%Z nil)=scall 999%Z nil /\
 V293_control_exit_residual 2 0(scall 999%Z nil)=sskip None /\
 V293_control_exit_residual 255 0(scall 999%Z nil)=sskip None /\
 V293_control_exit_residual 1 255(scall 999%Z nil)=sskip None.
Proof. repeat split;reflexivity. Qed.
