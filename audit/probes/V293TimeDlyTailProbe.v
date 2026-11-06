(* Consume actual allocation and first-y execution, then continue once. *)
Require Import CertiOS.audit.probes.V293TimeDlyCallEntryProbe.
Require Import CertiOS.audit.probes.V293TimeDlyTaskBridgeProbe.
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DYframe:=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 V293_owned_record_cells
 ([((70%positive,0%Z),Tint8,V293_byteval 0);((71%positive,0%Z),Tint8,V293_byteval 0);
  ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))]).
Definition DYcells delay lo hi:=V293_dly_cells 10%positive 11%positive 12%positive
 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)delay(V293_byteval 0)lo hi(V293_ready_group lo hi).
Definition DYowned delay lo hi tasks:=V293_owned_record_cells(DYcells delay lo hi) **
 (V293_owned_record_cells DLextra **(V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady tasks(emp:EcbMod.map)(Int.repr 37) **DYframe))).
Definition DYabs:=set DCabs abstcblsid(abstcblist DTblocked).
Definition DYstate M enabled O:RstateOP:=(DCge,DCle,M,(fun _=>false),(enabled,nil,nil),O,spec_done None).

Lemma DYprepare:forall M enabled,DCpost M enabled ->DYstate M enabled DCabs|=DYowned Int.zero 80 0 DLtasks.
Proof.
 intros M enabled Post.
 assert(Typed:forall s,s|=Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) ->
 s|=V293_owned_record_cell((12%positive,0%Z),Tint32,Vint32(Int.repr 3))).
 { intros s Held;unfold V293_owned_record_cell;apply astar_l_apure_intro;[exact Held|reflexivity]. }
 unfold DCpost,DCstate in Post.
 assert(Joint:(DCge,DCle,M,(fun _=>false),(enabled,nil,nil),DCabs,spec_done None)|=
 V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((12%positive,0%Z),Tint32,Vint32(Int.repr 3)) **DCframe))).
 { eapply astar_mono;[intros s H;exact H| |exact Post].
   intros s H;eapply astar_mono;[intros st H';exact H'| |exact H].
   intros st H';eapply astar_mono;[apply Typed|intros st' H'';exact H''|exact H']. }
 clear Post;rename Joint into Post.
 assert(Reordered:DYstate M enabled DCabs|=V293_owned_record_cells DLcells **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DYframe)))).
 { unfold DCframe,DCcells,DCrecords,DCglobals,DLcells,DLextra,DLlow,V293_dly_cells,
   V293_dly_record_extra,V293_record_layout,DYframe in Post|-*.
   cbn[V293_owned_record_cells app fst snd]in Post|-*.
   clear -Post;sep auto. }
 change(DYstate M enabled DCabs|=V293_owned_record_cells DLcells **
 (V293_owned_record_cells DLextra **(V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **DYframe)))).
 eapply astar_mono;[intros s H;exact H| |exact Reordered].
 intros s Held;eapply astar_mono;[intros st H;exact H| |exact Held].
 intros st Held';eapply astar_mono;[apply DTlow_owned|intros st' H;exact H|exact Held'].
Qed.
Lemma DYenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DCge DCle.
Proof. repeat split;reflexivity. Qed.

Theorem DYcall_blocks:forall enabled sd,exists Mf,
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs(scall 112%Z nil),(kenil,kseq sret DCouter))
 ((DCge,DCle,Mf),(fun _=>false),(enabled,nil,nil)) /\
 spec_step sd(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)DCabs(END None)DYabs /\
 V293_task_records Mf DTblocked /\V293_priority_table DLentries DTblocked /\
 V293_bitmap_tasks 64 0 DTblocked /\DYstate Mf enabled DYabs|=DYowned(Int.repr 3)64 0 DTblocked.
Proof.
 intros enabled sd.
 destruct(DCcall_first_y enabled)as(Mp&Mi&My&Param&Init&Raw&Prefix&Post&Records&Rest).
 pose proof(DYprepare My enabled Post)as Owned.
 destruct(V293_dly_after_y_to_sched_refines 103%Z 106%Z 105%Z 400%Z 401%Z 112%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 DCprogram DCouter DCge DCle My(fun _=>false)enabled nil nil DCabs(spec_done None)sd DYframe
 Int.zero 80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DYenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 ltac:(discriminate)DLtable DLbitmap ltac:(reflexivity)Owned)
 as(Mf&Tail&Step&AllRecords&Table&Bitmap&Returned).
 exists Mf;split.
 - eapply V293_local_trans;[exact Prefix|exact Tail].
 - split;[exact Step| ];split;[exact AllRecords| ];split;[exact Table| ];split;[exact Bitmap|exact Returned].
Qed.

Definition DYfacts delay lo hi tasks M O:=
 load Tint32 M(60%positive,44%Z)=Some(Vint32 delay) /\
 load Tint8 M(30%positive,0%Z)=Some(V293_byteval lo) /\
 load Tint8 M(30%positive,1%Z)=Some(V293_byteval hi) /\
 load Tint8 M(31%positive,0%Z)=Some(V293_byteval(V293_ready_group lo hi)) /\
 load Tint8 M(11%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 M(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint32 M(13%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 M(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable M 13%positive 0%Z 4 /\
 get O curtid=Some(oscurt OwnershipReady) /\get O abstcblsid=Some(abstcblist tasks).

Lemma DYobservations:forall M enabled O delay lo hi tasks,
 DYstate M enabled O|=DYowned delay lo hi tasks ->DYfacts delay lo hi tasks M O.
Proof.
 intros M enabled O delay lo hi tasks Owned.
 assert(Cells:DYstate M enabled O|=V293_owned_record_cells(DYcells delay lo hi) **Atrue)
 by(unfold DYowned in Owned;clear -Owned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)(DYcells delay lo hi) ->load tp M a=Some v).
 { intros a tp v Member;change(load tp(getmem(DYstate M enabled O))a=Some v).
   eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Cells]. }
 assert(CPU:DYstate M enabled O|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold DYowned,DYframe in Owned;clear -Owned;sep auto).
 assert(Frame:DYstate M enabled O|=V293_owned_record_cells
 ([((70%positive,0%Z),Tint8,V293_byteval 0);((71%positive,0%Z),Tint8,V293_byteval 0);
   ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))]) **Atrue)
 by(unfold DYowned,DYframe in Owned;clear -Owned;sep auto).
 assert(Fields:DYstate M enabled O|=V293_shared_fields OwnershipReady tasks(emp:EcbMod.map)(Int.repr 37) **Atrue)
 by(unfold DYowned in Owned;clear -Owned;sep auto).
 unfold DYfacts;split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split;[apply Read;cbn[DYcells V293_dly_cells In];tauto| ].
 split.
 - exact(DCraw_load (13%positive,0%Z)Tint32(Vint32 Int.zero)(DYstate M enabled O)eq_refl CPU).
 - split.
   + change(load Tint32(getmem(DYstate M enabled O))(90%positive,0%Z)=Some(Vint32(Int.repr 99))).
     eapply V293_record_star_load_l;[ |exact Frame].
     apply V293_owned_record_cells_load;cbn[In];tauto.
   + split.
     * exact(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue DCge DCle M(fun _=>false)(enabled,nil,nil)O(spec_done None)CPU).
     * split.
       -- change(get(getabst(DYstate M enabled O))curtid=Some(oscurt OwnershipReady)).
          eapply V293_star_abst_get_l with(p:=V293_shared_fields OwnershipReady tasks(emp:EcbMod.map)(Int.repr 37))(q:=Atrue);
          [intros s H;exact(proj1(V293_shared_fields_get _ _ _ _ s H))|exact Fields].
       -- change(get(getabst(DYstate M enabled O))abstcblsid=Some(abstcblist tasks)).
          eapply V293_star_abst_get_l with(p:=V293_shared_fields OwnershipReady tasks(emp:EcbMod.map)(Int.repr 37))(q:=Atrue);
          [intros s H;exact(proj1(proj2(V293_shared_fields_get _ _ _ _ s H)))|exact Fields].
Qed.

Theorem DYclosed_call_resources:forall enabled sd,exists Mf,
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs(scall 112%Z nil),(kenil,kseq sret DCouter))
 ((DCge,DCle,Mf),(fun _=>false),(enabled,nil,nil)) /\
 spec_step sd(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)DCabs(END None)DYabs /\
 V293_task_records Mf DTblocked /\V293_bitmap_tasks 64 0 DTblocked /\
 DYfacts(Int.repr 3)64 0 DTblocked Mf DYabs.
Proof.
 intros enabled sd;destruct(DYcall_blocks enabled sd)as(Mf&Trace&Step&Records&Table&Bits&Owned).
 exists Mf;split;[exact Trace| ];split;[exact Step| ];split;[exact Records| ];split;[exact Bits| ].
 apply DYobservations with(enabled:=enabled);exact Owned.
Qed.

(* Fragment-only intervention: at the same first-y memory, replace the
   pending assignment by a no-op; keep both sequence and trace marker.
   The actual call prefix keeps DCcont; these two traces are not concatenated. *)
Definition DYno_write_cont:=kseq(sseq(sskip None)(sskip None))
 (kseq(sseq(sprim excrit)(scall 112%Z nil))(kseq sret DCouter)).
Theorem DYno_delay_write:forall enabled,exists My Mf,
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs DCafter,(kenil,DCcont))((DCge,DCle,My),(fun _=>false),(false,nil,[enabled])) /\
 V293_local_steps DCprogram(curs DCafter,(kenil,DYno_write_cont))
 ((DCge,DCle,My),(fun _=>false),(false,nil,[enabled]))
 (curs(scall 112%Z nil),(kenil,kseq sret DCouter))
 ((DCge,DCle,Mf),(fun _=>false),(enabled,nil,nil)) /\
 DYstate Mf enabled DCabs|=DYowned Int.zero 64 0 DLtasks /\
 DYfacts Int.zero 64 0 DLtasks Mf DCabs /\
 load Tint32 Mf(60%positive,44%Z)<>Some(Vint32(Int.repr 3)).
Proof.
 intro enabled;destruct(DCcall_first_y enabled)as(Mp&Mi&My&Param&Init&Raw&Prefix&Post&Records&Rest).
 pose proof(DYprepare My enabled Post)as Owned.
 destruct(V293_dly_after_y_execution 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 DCprogram DCge DCle My(fun _=>false)(enabled,nil,nil)DCabs(spec_done None)_ Int.zero 80 0
 DYenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)Owned)
 as(Mf&Clear&Returned&OldDelay).
 change(load Tint32 Mf(60%positive,44%Z)=Some(Vint32 Int.zero))in OldDelay.
 assert(Facts:DYfacts Int.zero 64 0 DLtasks Mf DCabs)by(apply DYobservations with(enabled:=enabled);exact Returned).
 exists My;exists Mf;split;[exact Prefix| ];split.
 - eapply V293_local_trans;[apply V293_csteps_local;apply Clear| ].
   unfold DYno_write_cont.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply excrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   apply V293_local_refl.
 - split;[exact Returned| ];split;[exact Facts|rewrite OldDelay;discriminate].
Qed.
