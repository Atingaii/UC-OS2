Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Import ListNotations.
Local Open Scope nat_scope.

Definition CFfinal:=V293_write_byte CEM 91%positive 4.
Definition CFstored b:=V293_write_byte(V293_write_byte(CEMb b)b 0)91%positive 4.

(* Same typed original heap as the preceding checkpoint. Loads are derived
   by submemory and spatial ownership, without reducing the whole map. *)
Lemma CFhigh :
 load Tint8 CEM(91%positive,0%Z)=Some(V293_byteval 88) /\
 get CEM(91%positive,0%Z)=Some(true,Byte(Byte.repr 88)).
Proof.
 assert(Cell:CGstate OwnershipWaiting CEM nil |=
   V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) ** Atrue).
 { pose proof(CEtyped_heap nil)as Held;sep auto. }
 assert(Read:load Tint8 CEM(91%positive,0%Z)=Some(V293_byteval 88)).
 { eapply V293_record_star_load_l with(s:=CGstate OwnershipWaiting CEM nil)
   (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88))(Q:=Atrue).
   - intros st Held;apply V293_owned_record_cell_load;exact Held.
   - exact Cell. }
 assert(Cells:CGstate OwnershipWaiting CEM nil |=
   V293_owned_record_cells (((91%positive,0%Z),Tint8,V293_byteval 88)::nil) ** Atrue).
 { cbn[V293_owned_record_cells];sep auto. }
 destruct(V293_owned_cells_byte_writable (((91%positive,0%Z),Tint8,V293_byteval 88)::nil)
   (91%positive,0%Z)(V293_byteval 88)Atrue CGge CGle CEM(fun _=>false)
   (false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)ltac:(simpl;auto)Cells)as[raw Full].
 split;[exact Read| ];exact(V293_full_byte_load_encoding CEM(91%positive,0%Z)88 raw Full Read).
Qed.

Lemma CFinput :
 V293_sched_read_memory CEM 92%positive 81%positive 80%positive 16 0 1 /\
 get CEM(91%positive,0%Z)=Some(true,Byte(Byte.repr 88)).
Proof.
 assert(Ready:V293_ready_loads CEM 80%positive 81%positive 82%positive 16 0 RTentries).
 { eapply V293_ready_loads_sub with(M:=CGwith OwnershipWaiting true 0 0).
   - exists RTdecoder;apply CGdecoder_join.
   - eapply V293_ready_loads_sub with(M:=RTfull OwnershipWaiting).
     + exists(CGoutputs true 0 0);apply CGoutputs_join.
     + apply RTliteral_loads. }
 destruct Ready as[Low[High[Group Table]]].
 split.
 - unfold V293_sched_read_memory;split;[exact Group| ];split.
   + intros n Bound;apply CGlookup;exact Bound.
   + split;assumption.
 - exact(proj2 CFhigh).
Qed.

Theorem CFactual_call : forall enabled ci ip ph Th O,
 get O curtid=Some(oscurt OwnershipWaiting) ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))
 (set HPtasks OwnershipWaiting(SKIP,(kenil,HPpending)))
 (SPS CFfinal enabled ci)ph Th O HPcst OwnershipWaiting ->
 ProgSim(RCprogram,(CGpo,CGempty,ip))
 (set HPtasks OwnershipWaiting(curs(scall 107%Z nil),(kenil,HPpending)))
 (SPS CEM enabled ci)ph Th O HPcst OwnershipWaiting.
Proof.
 intros enabled ci ip ph Th O Cur Post;unfold SPS in *.
 eapply V293_sched_call_progsim with(caller:=CGle)(si:=nil)(cs:=enabled::ci)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(high:=103%Z)(y:=104%Z)
 (bt:=92%positive)(bg:=81%positive)(br:=80%positive)(bh:=91%positive)
 (lo:=16)(hi:=0)(g:=1)(oldhigh:=Byte(Byte.repr 88));try eassumption.
 - exact CEbound.
 - apply map_get_set.
 - apply map_get_set.
 - apply map_get_set.
 - exact HPcontext.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - exact(proj1 CFinput).
 - exact(proj2 CFinput).
 - lia.
 - lia.
 - reflexivity.
 - exists 4;left;repeat split;try lia;reflexivity.
 - rewrite <-set_set_eq;exact Post.
Qed.

Theorem CFall_fresh_storage : forall b,fresh CEM b ->
 free Tint8 b(CFstored b)=Some CFfinal /\ get CFfinal(b,0%Z)=None.
Proof.
 intros b Fresh.
 assert(Different:b<>91%positive).
 { intro E;subst b;assert(Empty:get CEM(91%positive,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh).
   pose proof(proj2 CFinput)as High;congruence. }
 split.
 - unfold CFstored,CFfinal,CEMb;eapply V293_sched_storage;[exact Fresh|exact(proj2 CFinput)].
 - unfold CFfinal;rewrite V293_write_byte_other by congruence;apply V293_success_fresh_none;exact Fresh.
Qed.

Theorem CFfresh_choices_same_return : forall b1 b2,
 fresh CEM b1 ->fresh CEM b2 ->
 free Tint8 b1(CFstored b1)=free Tint8 b2(CFstored b2).
Proof.
 intros b1 b2 F1 F2;rewrite(proj1(CFall_fresh_storage b1 F1)),(proj1(CFall_fresh_storage b2 F2));reflexivity.
Qed.

(* Only the output write is removed; all original entry bytes stay fixed. *)
Theorem CFomit_high_rejected :
 load Tint8 CEM(91%positive,0%Z)=Some(V293_byteval 88) /\
 load Tint8 CFfinal(91%positive,0%Z)=Some(V293_byteval 4) /\ CEM<>CFfinal.
Proof.
 pose proof(proj1 CFhigh)as Before.
 assert(After:load Tint8 CFfinal(91%positive,0%Z)=Some(V293_byteval 4))by(apply V293_write_byte_load;lia).
 split;[exact Before| ];split;[exact After| ].
 intro Same.
 pose proof(f_equal(fun M:mem=>load Tint8 M(91%positive,0%Z))Same)as E.
 assert(Conflict:Some(V293_byteval 88)=Some(V293_byteval 4)).
 { transitivity(load Tint8 CEM(91%positive,0%Z));[symmetry;exact Before| ].
   transitivity(load Tint8 CFfinal(91%positive,0%Z));[exact E|exact After]. }
 discriminate Conflict.
Qed.

(* Only the local free is removed; the selected output is still exactly 4. *)
Theorem CFomit_free_rejected : forall b,fresh CEM b ->
 load Tint8(CFstored b)(91%positive,0%Z)=Some(V293_byteval 4) /\
 get(CFstored b)(b,0%Z)=Some(true,Byte(Byte.repr 0)) /\ CFstored b<>CFfinal.
Proof.
 intros b Fresh.
 assert(Different:b<>91%positive).
 { intro E;subst b;assert(Empty:get CEM(91%positive,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh).
   pose proof(proj2 CFinput)as High;congruence. }
 assert(Local:get(CFstored b)(b,0%Z)=Some(true,Byte(Byte.repr 0))).
 { unfold CFstored;rewrite V293_write_byte_other by congruence;unfold V293_write_byte;apply map_get_set. }
 split;[apply V293_write_byte_load;lia| ];split;[exact Local| ].
 intro Same.
 pose proof(f_equal(fun M:mem=>get M(b,0%Z))Same)as E.
 pose proof(proj2(CFall_fresh_storage b Fresh))as Removed.
 assert(Conflict:Some(true,Byte(Byte.repr 0))=None).
 { transitivity(get(CFstored b)(b,0%Z));[symmetry;exact Local| ].
   transitivity(get CFfinal(b,0%Z));[exact E|exact Removed]. }
 discriminate Conflict.
Qed.

Theorem CFall_fresh_return : forall b,fresh CEM b ->
 cstepstar CGprogram(curs sret,(kenil,CEks))(CGge,CELb b,CFstored b)
 (SKIP,(kenil,HPpending))(CGge,CGle,CFfinal) /\
 get CGle 120%Z=Some(98%positive,Tint32) /\ get CGle 104%Z=None.
Proof.
 intros b Fresh;split.
 - eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sret_step with(al:=((b,Tint8)::nil));[reflexivity|reflexivity| ].
     change(getaddr(EnvMod.set EnvMod.emp 104%Z(b,Tint8))=((b,Tint8)::nil));reflexivity. }
   eapply c_stepstarn.
   { eapply stmt_step;[reflexivity| ];eapply sfree_step;try reflexivity.
     exact(proj1(CFall_fresh_storage b Fresh)). }
   eapply c_stepstarn;[eapply stmt_step;[reflexivity| ];eapply sfreeend_step;reflexivity|apply c_stepstar0].
 - vm_compute;split;reflexivity.
Qed.

Theorem CFall_fresh_complete_execution : forall b,fresh CEM b ->
 cstepstar CGprogram(curs(scall 107%Z nil),(kenil,HPpending))(CGge,CGle,CEM)
 (SKIP,(kenil,HPpending))(CGge,CGle,CFfinal).
Proof.
 intros b Fresh.
 destruct(CEactual_prefix_all_fresh b Fresh)as[Prefix[Local[Caller Raw]]].
 assert(Dt:b<>92%positive).
 { eapply V293_success_load_not_fresh with(n:=V293_ready_lookup 0);[exact Fresh|exact(proj1(proj2(proj1 CFinput))0 ltac:(lia))]. }
 assert(Dg:b<>81%positive)by(eapply V293_success_load_not_fresh;[exact Fresh|exact(proj1(proj1 CFinput))]).
 assert(Dr:b<>80%positive)by(eapply V293_success_load_not_fresh;[exact Fresh|exact(proj1(proj2(proj2(proj1 CFinput))))]).
 assert(Dh:b<>91%positive).
 { intro E;subst b;assert(Empty:get CEM(91%positive,0%Z)=None)by(apply V293_success_fresh_none;exact Fresh).
   pose proof(proj2 CFinput)as High;congruence. }
 assert(Reads:V293_sched_read_memory(CEMb b)92%positive 81%positive 80%positive 16 0 1).
 { unfold CEMb;change(V293_sched_read_memory(set CEM(b,0%Z)(true,Undef))92%positive 81%positive 80%positive 16 0 1).
   destruct(proj1 CFinput)as[RG[RT[RR0 RR1]]];unfold V293_sched_read_memory,load,loadm in *;
   cbn[typelen loadbytes]in *;repeat split;try(intros n N);repeat rewrite map_get_set' by congruence;auto. }
 eapply V293_cstepstar_trans;[exact Prefix| ].
 unfold CEbody,V293_OSSchedNew_body.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_cstepstar_trans.
 { eapply V293_OSSchedNew_updates_execution with(bt:=92%positive)(bg:=81%positive)(br:=80%positive)
   (bh:=91%positive)(byblock:=b)(lo:=16)(hi:=0)(g:=1)(oldy:=Undef)(oldhigh:=Byte(Byte.repr 88));try eassumption.
   - unfold V293_sched_read_env;vm_compute;repeat split;reflexivity.
   - vm_compute;reflexivity.
   - unfold CEMb;rewrite V293_success_allocb_outside by(left;congruence);exact(proj2 CFinput).
   - lia.
   - lia.
   - reflexivity.
   - exists 4;left;repeat split;try lia;reflexivity. }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 exact(proj1(CFall_fresh_return b Fresh)).
Qed.
