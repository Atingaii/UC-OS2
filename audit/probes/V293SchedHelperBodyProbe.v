(* Original helper body witnesses and a single-assignment omission control. *)
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293ReturnClientTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293PendingReturnTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.

Definition HBframe :=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 V293_owned_record_cell((90%positive,0%Z),Tint8,V293_byteval 99).
Definition HBresource v := V293_helper_resource 80%positive 81%positive 82%positive
 92%positive 91%positive OwnershipWaiting HBframe v.
Definition HBpost := CurTid OwnershipWaiting **Atrue.
Definition HBlocal b : env := set emp 104%Z(b,Tint8).
Definition HBbody := V293_OSSchedNew_body 100%Z 101%Z 102%Z 103%Z 104%Z.

Lemma HBframe_good : GoodInvAsrt HBframe.
Proof. unfold HBframe,V293_owned_record_cell;cbn;repeat split;exact I. Qed.
Lemma HBpost_good : GoodInvAsrt HBpost.
Proof. unfold HBpost,CurTid,Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact I. Qed.
Lemma HBbase : RHstate OwnershipWaiting(RHmemory OwnershipWaiting)|=HBresource(V293_byteval 88).
Proof. pose proof(RCentry OwnershipWaiting)as H;unfold HBresource,V293_helper_resource,HBframe,RCframe in H|-*;sep auto. Qed.

Lemma HBloads : V293_ready_loads(RHmemory OwnershipWaiting)
 80%positive 81%positive 82%positive 16 0 RTentries.
Proof.
 eapply V293_ready_loads_sub with(M:=RTexec_memory OwnershipWaiting).
 - exists RHtarget;apply RHjoin.
 - eapply V293_ready_loads_sub with(M:=RTwith_outputs OwnershipWaiting).
   + exists RTdecoder;apply RTdecoder_join.
   + eapply V293_ready_loads_sub with(M:=RTfull OwnershipWaiting).
     * exists RToutputs;apply RToutputs_join.
     * apply RTliteral_loads.
Qed.

Lemma HBoutput : forall b n,
 (b=91%positive /\ n=88) \/ (b=90%positive /\ n=99) ->
 load Tint8(RHmemory OwnershipWaiting)(b,0%Z)=Some(V293_byteval n) /\
 get(RHmemory OwnershipWaiting)(b,0%Z)=Some(true,Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))).
Proof.
 intros b n Choice.
 assert(Cell:RHstate OwnershipWaiting(RHmemory OwnershipWaiting)|=
  V293_owned_record_cell((b,0%Z),Tint8,V293_byteval n) **Atrue).
 { pose proof(HBbase)as Held;unfold HBresource,V293_helper_resource,HBframe in Held.
   destruct Choice as[[B N]|[B N]];subst;sep auto. }
 assert(Read:load Tint8(RHmemory OwnershipWaiting)(b,0%Z)=Some(V293_byteval n)).
 { eapply V293_record_star_load_l with(s:=RHstate OwnershipWaiting(RHmemory OwnershipWaiting))
   (P:=V293_owned_record_cell((b,0%Z),Tint8,V293_byteval n))(Q:=Atrue).
   - intros st Held;apply V293_owned_record_cell_load;exact Held.
   - exact Cell. }
 assert(Cells:RHstate OwnershipWaiting(RHmemory OwnershipWaiting)|=
   V293_owned_record_cells (((b,0%Z),Tint8,V293_byteval n)::nil) **Atrue).
 { cbn[V293_owned_record_cells];sep auto. }
 destruct(V293_owned_cells_byte_writable (((b,0%Z),Tint8,V293_byteval n)::nil)
 (b,0%Z)(V293_byteval n)Atrue RHge RTle(RHmemory OwnershipWaiting)(fun _=>false)
 (false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)ltac:(simpl;auto)Cells)as[raw Full].
 split;[exact Read| ];eapply V293_full_byte_load_encoding;[exact Full|exact Read].
Qed.

(* The original body starts at every fresh raw byte, not an initialized output. *)
Theorem HBall_fresh_body : forall ip A b,
 fresh(RHmemory OwnershipWaiting)b ->
 (RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 Amapsto(b,0%Z)Tint8 true Vundef **HBresource(V293_byteval 88) /\ TaskSim(RCprogram,(RCprogram,(fun _=>None),ip))
 (curs HBbody,(kenil,kcall 107%Z HBbody RTle kstop))
 (RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),(false,nil,nil))
 (RCprogram,A)(SKIP,(kenil,kstop))(RIabstract OwnershipWaiting)V293_shared_li
 (V293_ready_inv 80%positive 81%positive 82%positive)
 (fun st=>satp(fst st)(snd st)HBpost)OwnershipWaiting.
Proof.
 intros ip A b Fresh.
 assert(Own:(RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=
 Amapsto(b,0%Z)Tint8 true Vundef **HBresource(V293_byteval 88)).
 { eapply V293_tick_allocate_frame with(tp:=Tint8);[exact Fresh| ].
   eapply V293_helper_resource_lenv;[exact HBframe_good|exact HBbase]. }
 split;[exact Own| ].
 unfold HBbody,HBlocal.
 eapply V293_helper_body_TaskSim with(R:=HBframe)(op:=spec_done None)
 (br:=80%positive)(bg:=81%positive)(bp:=82%positive)(bt:=92%positive)(bh:=91%positive)
 (oldy:=Vundef)(oldhigh:=V293_byteval 88).
 - unfold RCprogram;destruct(Z.eq_dec 107%Z 107%Z);[reflexivity|contradiction].
 - exact HBframe_good.
 - unfold V293_sched_read_env;repeat split;vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - reflexivity.
 - eapply V293_helper_fresh_byte_distinct;[exact Fresh|exact(RHlookup OwnershipWaiting 0 ltac:(lia))].
 - eapply V293_helper_fresh_byte_distinct with(v:=V293_byteval 1)(off:=0%Z);[exact Fresh|exact(proj1(proj2(proj2 HBloads)))].
 - eapply V293_helper_fresh_byte_distinct with(v:=V293_byteval 16)(off:=0%Z);[exact Fresh|exact(proj1 HBloads)].
 - exact Own.
 - intros tasks lo hi entries next message Mret Map Rel Task Rest.
   assert(Current:(RHge,RTle,Mret,(fun _=>false),(false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=HBpost).
   { eapply V293_helper_resource_current;exact Rest. }
   apply V293_return_client_coinduction.
   + right;right;reflexivity.
   + eapply V293_pending_local with(op:=spec_done None);exact Current.
   + intros ab;eapply good_inv_prop;[exact HBpost_good|exact Current].
Qed.

Theorem HBnonempty_body : forall ip A,exists b,
 fresh(RHmemory OwnershipWaiting)b /\ TaskSim(RCprogram,(RCprogram,(fun _=>None),ip))
 (curs HBbody,(kenil,kcall 107%Z HBbody RTle kstop))
 (RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1,(fun _=>false),(false,nil,nil))
 (RCprogram,A)(SKIP,(kenil,kstop))(RIabstract OwnershipWaiting)V293_shared_li
 (V293_ready_inv 80%positive 81%positive 82%positive)
 (fun st=>satp(fst st)(snd st)HBpost)OwnershipWaiting.
Proof. intros;destruct(memory_has_fresh_block(RHmemory OwnershipWaiting))as[b Fresh].
 exists b;split;[exact Fresh|exact(proj2(HBall_fresh_body ip A b Fresh))]. Qed.

Lemma HBallocation_load : forall M b c off v,
 c<>b ->load Tint8 M(c,off)=Some v ->
 load Tint8(allocb M b 0%Z 1)(c,off)=Some v.
Proof.
 intros M b c off v Different Read.
 unfold load,loadm in *;cbn[typelen loadbytes];unfold addr,offset in *.
 rewrite V293_success_allocb_outside by(left;exact Different);exact Read.
Qed.

(* Only high's original assignment becomes SKIP; the local write and return
   remain present, with exactly the same initial heap and allocation choice. *)
Definition HBwithout_high := sseq
 (sseq(sassign(evar 104%Z)(V293_OSSchedNew_row_expr 100%Z 101%Z))(sskip None))sret.

Lemma HBfree_local_write : forall M b n,
 fresh M b ->free Tint8 b(V293_write_byte(allocb M b 0%Z 1)b n)=Some M.
Proof.
 intros M b n Fresh.
 set(W:=V293_write_byte(allocb M b 0%Z 1)b n).
 assert(Writable:V293_bytes_writable W b 0%Z 1).
 { intros k K;assert(k=0)by lia;subst k.
   exists(Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))).
   change(get W(b,0%Z)=Some(true,Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n)))))).
   unfold W,V293_write_byte;apply map_get_set. }
 destruct(V293_freeb_construct 1 W b 0%Z Writable)as[Mret Free].
 assert(Same:Mret=M).
 { apply HalfPermMap.extensionality;intros[c i];change(get Mret(c,i)=get M(c,i)).
   destruct(Pos.eq_dec c b)as[E|E].
   - subst c;destruct(Z.eq_dec i 0)as[Z0|Z0].
     + subst i;rewrite(V293_success_fresh_none _ _ Fresh).
       change(get Mret(b,(0+Z.of_nat 0)%Z)=None);eapply V293_freeb_removed;[exact Free|lia].
     + rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(right;lia).
       unfold W,V293_write_byte;rewrite map_get_set' by congruence.
       apply V293_success_allocb_outside;right;lia.
   - rewrite(V293_freeb_outside _ _ _ _ _ _ _ Free)by(left;exact E).
     unfold W,V293_write_byte;rewrite map_get_set' by congruence.
     apply V293_success_allocb_outside;left;exact E. }
 subst Mret;exact Free.
Qed.

Theorem HBhigh_omission_control : forall ks,
 exists b,
 fresh(RHmemory OwnershipWaiting)b /\ cstepstar RCprogram(curs HBbody,(kenil,kcall 107%Z HBbody RTle ks))
 (RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1)
 (SKIP,(kenil,ks))(RHge,RTle,V293_write_byte(RHmemory OwnershipWaiting)91%positive 4) /\ cstepstar RCprogram(curs HBwithout_high,(kenil,kcall 107%Z HBbody RTle ks))
 (RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1)
 (SKIP,(kenil,ks))(RHge,RTle,RHmemory OwnershipWaiting) /\ load Tint8(V293_write_byte(RHmemory OwnershipWaiting)91%positive 4)(91%positive,0%Z)=Some(V293_byteval 4) /\ load Tint8(RHmemory OwnershipWaiting)(91%positive,0%Z)=Some(V293_byteval 88) /\ load Tint8(V293_write_byte(RHmemory OwnershipWaiting)91%positive 4)(90%positive,0%Z)=Some(V293_byteval 99) /\ load Tint8(RHmemory OwnershipWaiting)(90%positive,0%Z)=Some(V293_byteval 99) /\ (forall c i,(c,i)<>(91%positive,0%Z) ->
 get(V293_write_byte(RHmemory OwnershipWaiting)91%positive 4)(c,i)=get(RHmemory OwnershipWaiting)(c,i)).
Proof.
 intro ks.
 destruct(V293_ready_fresh_avoiding(RHmemory OwnershipWaiting)[92%positive;81%positive;80%positive;91%positive])as(b&Fresh&Away).
 assert(BT:b<>92%positive)by(intro E;apply Away;subst;simpl;tauto).
 assert(BG:b<>81%positive)by(intro E;apply Away;subst;simpl;tauto).
 assert(BR:b<>80%positive)by(intro E;apply Away;subst;simpl;tauto).
 assert(BH:b<>91%positive)by(intro E;apply Away;subst;simpl;tauto).
 set(M:=RHmemory OwnershipWaiting).
 set(Ma:=allocb M b 0%Z 1).
 set(le:=HBlocal b).
 set(k:=kcall 107%Z HBbody RTle ks).
 assert(Env:V293_sched_read_env RHge le 100%Z 101%Z 102%Z 92%positive 81%positive 80%positive).
 { unfold V293_sched_read_env,le,HBlocal;repeat split;vm_compute;reflexivity. }
 assert(Reads:V293_sched_read_memory Ma 92%positive 81%positive 80%positive 16 0 1).
 { unfold V293_sched_read_memory;repeat split.
   - apply HBallocation_load;[congruence|exact(proj1(proj2(proj2 HBloads)))].
   - intros n N;apply HBallocation_load;[congruence|apply RHlookup;exact N].
   - apply HBallocation_load;[congruence|exact(proj1 HBloads)].
   - apply HBallocation_load;[congruence|exact(proj1(proj2 HBloads))]. }
 assert(Y:get Ma(b,0%Z)=Some(true,Undef)).
 { change(get(set M(b,0%Z)(true,Undef))(b,0%Z)=Some(true,Undef));apply map_get_set. }
 assert(H:get Ma(91%positive,0%Z)=Some(true,Byte(Byte.repr 88))).
 { unfold Ma;rewrite V293_success_allocb_outside by(left;congruence);exact(proj2(HBoutput 91%positive 88 ltac:(left;auto))). }
 assert(Nonempty:exists p,V293_bitmap_ready 16 0 p).
 { exists 4;left;split;[lia|vm_compute;reflexivity]. }
 assert(Normal:cstepstar RCprogram(curs HBbody,(kenil,k))(RHge,le,Ma)
 (SKIP,(kenil,ks))(RHge,RTle,V293_write_byte M 91%positive 4)).
 { unfold HBbody,V293_OSSchedNew_body at 1;eapply c_stepstarn.
   { eapply stmt_step;[reflexivity|apply sseq_step]. }
   eapply V293_cstepstar_trans.
   { eapply V293_OSSchedNew_updates_execution with(bt:=92%positive)(bg:=81%positive)(br:=80%positive)
     (bh:=91%positive)(byblock:=b)(lo:=16)(hi:=0)(g:=1)(oldy:=Undef)(oldhigh:=Byte(Byte.repr 88));
     try eassumption;try reflexivity;try lia;unfold le,HBlocal;vm_compute;reflexivity. }
   apply V293_helper_return_steps;unfold Ma;eapply V293_sched_storage;[exact Fresh|exact(proj2(HBoutput 91%positive 88 ltac:(left;auto)))]. }
 assert(Row:cstepstar RCprogram(curs(sassign(evar 104%Z)(V293_OSSchedNew_row_expr 100%Z 101%Z)),
 (kenil,kseq(sskip None)(kseq sret k)))(RHge,le,Ma)
 (SKIP,(kenil,kseq(sskip None)(kseq sret k)))(RHge,le,V293_write_byte Ma b 0)).
 { destruct(V293_OSSchedNew_row_eval RHge le Ma 100%Z 101%Z 102%Z 92%positive 81%positive 80%positive 16 0 1 Env Reads ltac:(lia))as[Value Ty].
   eapply V293_assign_byte_execution.
   - cbn[evaltype];unfold le,HBlocal;rewrite map_get_set;reflexivity.
   - cbn[evaladdr get_lenv];unfold le,HBlocal;rewrite map_get_set;reflexivity.
   - exact Ty.
   - exact Value.
   - eapply V293_write_byte_store;exact Y. }
 assert(Mutant:cstepstar RCprogram(curs HBwithout_high,(kenil,k))(RHge,le,Ma)
 (SKIP,(kenil,ks))(RHge,RTle,M)).
 { unfold HBwithout_high;eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_cstepstar_trans;[exact Row| ].
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
   change(cstepstar RCprogram(SKIP,(kenil,kseq sret k))(RHge,le,V293_write_byte Ma b 0)
    (SKIP,(kenil,ks))(RHge,RTle,M)).
   apply V293_helper_return_steps;unfold Ma;apply HBfree_local_write;exact Fresh. }
 exists b;split;[exact Fresh| ];split;[exact Normal| ];split;[exact Mutant| ].
 split;[apply V293_write_byte_load;lia| ].
 split;[exact(proj1(HBoutput 91%positive 88 ltac:(left;auto)))| ].
 split;[rewrite V293_write_byte_other_load by discriminate;exact(proj1(HBoutput 90%positive 99 ltac:(right;auto)))| ].
 split;[exact(proj1(HBoutput 90%positive 99 ltac:(right;auto)))| ].
 intros c i Different;unfold V293_write_byte;rewrite map_get_set' by congruence;reflexivity.
Qed.
