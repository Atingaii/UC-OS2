(* Nonempty caller heap WITHOUT the parameter or either local block.
   The probe consumes the real allocation/initialization and first-write cuts. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDlyCall.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition DCge:env:=set(set DLge 110%Z(70%positive,Tint8))111%Z(71%positive,Tint8).
Definition DCle:=V293_dly_call_lenv 401%Z 400%Z 402%Z 12%positive 11%positive 13%positive.
Definition DCfunction:=V293_dly_function 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z.
Definition DCprogram(f:fid):option function:=if Z.eq_dec f 1200%Z then Some DCfunction else None.
Definition DCbody:=V293_dly_full_body 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z.
Definition DCouter:=kcall 1200%Z DCbody emp kstop.
Definition DCafter:=V293_dly_after_y 103%Z 106%Z 105%Z 400%Z.
Definition DCcont:=V293_dly_after_y_cont 103%Z 401%Z 112%Z DCouter.
Definition DCrecords:=V293_record_layout OwnershipReady 4 rdy Vnull 0++DLlow.
Definition DCglobals:list V293_record_cell:=
 [((10%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady);
  ((30%positive,0%Z),Tint8,V293_byteval 80);((30%positive,1%Z),Tint8,V293_byteval 0);
  ((31%positive,0%Z),Tint8,V293_byteval 1);
  ((60%positive,44%Z),Tint32,Vint32 Int.zero);
  ((70%positive,0%Z),Tint8,V293_byteval 0);((71%positive,0%Z),Tint8,V293_byteval 0);
  ((90%positive,0%Z),Tint32,Vint32(Int.repr 99))].
Definition DCcells:=DCrecords++DCglobals.
Definition DCmem:=OwnershipCellsMemory DCcells.
Definition DCabs:=V293_shared_fixture_abs OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37).
Definition DCframe:=V293_owned_record_cells DCcells **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37).
Definition DCstate M enabled:RstateOP:=
 (DCge,DCle,M,(fun _=>false),(enabled,nil,nil),DCabs,spec_done None).
Definition DCpost M enabled:=
 DCstate M enabled|=V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **DCframe)).

Lemma DCentry:forall enabled,DCstate DCmem enabled|=DCframe.
Proof.
 intro enabled.
 assert(Physical:V293_target_wstate DCge DCle DCmem emp|=V293_owned_record_cells DCcells).
 { apply OwnershipCellsSpatial.
   - vm_compute;repeat split;intros;intuition congruence.
   - repeat constructor;vm_compute;reflexivity. }
 assert(Joint:V293_target_wstate DCge DCle DCmem DCabs|=DCframe).
 { unfold DCframe;eapply V293_target_wstate_star with(m1:=DCmem)(m2:=emp)(o1:=emp)(o2:=DCabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Physical.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 change(DCstate DCmem enabled|=DCframe)in Joint;exact Joint.
Qed.
Lemma DCfresh:forall b,b=11%positive \/b=12%positive \/b=13%positive ->fresh DCmem b.
Proof.
 intros b Choice l i E[v Bound];subst l.
 change(get DCmem(b,i)=Some v)in Bound.
 assert(Absent:get DCmem(b,i)=None).
 { apply OwnershipCellsOutside;destruct Choice as[Same|[Same|Same]];subst b;
   vm_compute;intro H;repeat destruct H as[H|H];congruence. }
 congruence.
Qed.
Lemma DCframe_load:forall a tp v,In(a,tp,v)DCcells ->forall s,
 s|=DCframe **Atrue ->load tp(getmem s)a=Some v.
Proof.
 intros a tp v Member s Held.
 assert(Cells:s|=V293_owned_record_cells DCcells **Atrue)
 by(unfold DCframe in Held;clear -Held;sep auto).
 eapply V293_record_star_load_l;[apply V293_owned_record_cells_load;exact Member|exact Cells].
Qed.
Lemma DCraw_load:forall a tp v s,rule_type_val_match tp v=true ->s|=Amapsto a tp true v **Atrue ->
 load tp(getmem s)a=Some v.
Proof.
 intros a tp v s Valid Held.
 eapply(V293_record_star_load_l(Amapsto a tp true v)Atrue tp a v);
 [intros st [H _];eapply mapstoval_load;[exact Valid|exact H]|exact Held].
Qed.
Lemma DCundef_load:forall a tp s,(tp=Tint8 \/tp=Tint32) ->
 s|=Amapsto a tp true Vundef **Atrue ->load tp(getmem s)a=Some Vundef.
Proof.
 intros a tp s Kind Held.
 eapply(V293_record_star_load_l(Amapsto a tp true Vundef)Atrue tp a Vundef);[ |exact Held].
 intros st [Mapsto Empty];unfold mapstoval in Mapsto;destruct Mapsto as(vl&Enc&Bytes);subst vl.
 pose proof(ptomvallist_loadbytes _ _ _ _ Bytes)as Read;rewrite encode_val_length in Read.
 destruct a as[b i];destruct Kind as[Same|Same];subst tp;unfold load,loadm;rewrite Read;reflexivity.
Qed.
Lemma DCframe_records:forall s,s|=DCframe **Atrue ->V293_task_records(getmem s)DLtasks.
Proof.
 intros s Held t priority status message Lookup.
 unfold DLtasks in Lookup;destruct(TcbMod.eq_dec t OwnershipWaiting)as[Same|Other].
 - subst t;rewrite map_get_set in Lookup;inversion Lookup;subst.
   eapply V293_record_layout_sound with(p:=6)(pend:=0);try reflexivity;try lia.
   intros a tp v Member;apply DCframe_load;[ |exact Held].
   unfold DCcells,DCrecords;apply in_or_app;left;apply in_or_app;right;exact Member.
 - rewrite map_get_set' in Lookup by congruence.
   destruct(TcbMod.eq_dec t OwnershipReady)as[Same|OtherR].
   + subst t;rewrite map_get_sig in Lookup;inversion Lookup;subst.
     eapply V293_record_layout_sound with(p:=4)(pend:=0);try reflexivity;try lia.
     intros a tp v Member;apply DCframe_load;[ |exact Held].
     unfold DCcells,DCrecords;apply in_or_app;left;apply in_or_app;left;exact Member.
   + rewrite map_get_sig' in Lookup by congruence;discriminate.
Qed.

Theorem DCcall_first_y:forall enabled,exists Mp Mi Mf,
 store Tint32(allocb DCmem 12%positive 0%Z 4)(12%positive,0%Z)(Vint32(Int.repr 3))=Some Mp /\
 store Tint32(allocb(allocb Mp 11%positive 0%Z 1)13%positive 0%Z 4)
 (13%positive,0%Z)(Vint32 Int.zero)=Some Mi /\
 load Tint8 Mi(11%positive,0%Z)=Some Vundef /\
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs DCafter,(kenil,DCcont))((DCge,DCle,Mf),(fun _=>false),(false,nil,[enabled])) /\
 DCpost Mf enabled /\V293_task_records Mf DLtasks /\
 load Tint8 Mf(11%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 Mf(13%positive,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32 Mf(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get DCabs abstcblsid=Some(abstcblist DLtasks).
Proof.
 intro enabled.
 destruct(V293_dly_call_entry DCprogram kstop DCge emp DCmem(fun _=>false)(enabled,nil,nil)
 DCabs(spec_done None)1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive(Int.repr 3)DCframe
 eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (DCfresh 12%positive ltac:(tauto))(DCfresh 11%positive ltac:(tauto))(DCfresh 13%positive ltac:(tauto))(DCentry enabled))
 as(Mp&Mi&ParamStore&Init&Entry&Owned).
 assert(Frame:DCstate Mi enabled|=DCframe **Atrue)by(clear -Owned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)DCcells ->load tp Mi a=Some v)
 by(intros a tp v Member;exact(DCframe_load a tp v Member(DCstate Mi enabled)Frame)).
 assert(Ticks:load Tint32 Mi(12%positive,0%Z)=Some(Vint32(Int.repr 3))).
 { assert(Slot:DCstate Mi enabled|=Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **Atrue)
   by(clear -Owned;sep auto).
   exact(DCraw_load (12%positive,0%Z)Tint32(Vint32(Int.repr 3))(DCstate Mi enabled)eq_refl Slot). }
 assert(YRaw:load Tint8 Mi(11%positive,0%Z)=Some Vundef).
 { assert(Slot:DCstate Mi enabled|=Amapsto(11%positive,0%Z)Tint8 true Vundef **Atrue)
   by(clear -Owned;sep auto).
   exact(DCundef_load (11%positive,0%Z)Tint8(DCstate Mi enabled)(or_introl eq_refl)Slot). }
 assert(YOwned:DCstate Mi enabled|=Amapsto(11%positive,0%Z)Tint8 true Vundef **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **DCframe)))
 by(clear -Owned;sep auto).
 destruct(V293_dly_body_first_y DCprogram DCouter DCge DCle Mi(fun _=>false)enabled nil nil DCabs(spec_done None)
 _ 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 60%positive 0%Z 0 70%positive 71%positive 12%positive(Int.repr 3)
 eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)
 eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)eq_refl Ticks ltac:(discriminate)
 eq_refl eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)ltac:(apply Read;vm_compute;tauto)
 ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)ltac:(lia)YOwned)
 as(Mf&YStore&Prefix&Post&Outside).
 exists Mp;exists Mi;exists Mf;split;[exact ParamStore| ];split;[exact Init| ];split;[exact YRaw| ];split.
 - eapply V293_local_trans;[exact Entry|exact Prefix].
 - split;[exact Post| ].
   assert(FrameF:DCstate Mf enabled|=DCframe **Atrue)by(clear -Post;sep auto).
   split;[exact(DCframe_records _ FrameF)| ];split.
   + assert(Y:DCstate Mf enabled|=V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **Atrue)
     by(clear -Post;sep auto).
     eapply V293_record_star_load_l with(s:=DCstate Mf enabled);[apply V293_owned_record_cell_load|exact Y].
   + split.
     * assert(CPU:DCstate Mf enabled|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
       by(clear -Post;sep auto).
       exact(DCraw_load (13%positive,0%Z)Tint32(Vint32 Int.zero)(DCstate Mf enabled)eq_refl CPU).
     * split.
       -- assert(Slot:DCstate Mf enabled|=Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **Atrue)
          by(clear -Post;sep auto).
          exact(DCraw_load (12%positive,0%Z)Tint32(Vint32(Int.repr 3))(DCstate Mf enabled)eq_refl Slot).
       -- split;[exact(DCframe_load (90%positive,0%Z)Tint32(Vint32(Int.repr 99)) ltac:(vm_compute;tauto)(DCstate Mf enabled)FrameF)|reflexivity].
Qed.

Theorem DCboth_IE:forall enabled,exists Mf,
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs DCafter,(kenil,DCcont))((DCge,DCle,Mf),(fun _=>false),(false,nil,[enabled])) /\
 DCpost Mf enabled.
Proof.
 intro enabled;destruct(DCcall_first_y enabled)as(Mp&Mi&Mf&Param&Init&Raw&Trace&Post&Rest).
 exists Mf;split;assumption.
Qed.

(* Only the initializer is omitted at a fragment boundary. Allocation and
   subsequent body are identical; this is not a trace of an altered function. *)
Theorem DCno_initializer:forall enabled,exists Mp Mf,
 let Ma:=allocb(allocb Mp 11%positive 0%Z 1)13%positive 0%Z 4 in
 store Tint32(allocb DCmem 12%positive 0%Z 4)(12%positive,0%Z)(Vint32(Int.repr 3))=Some Mp /\
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs DCbody,(kenil,DCouter))((DCge,DCle,Ma),(fun _=>false),(enabled,nil,nil)) /\
 load Tint8 Ma(11%positive,0%Z)=Some Vundef /\
 V293_local_steps DCprogram(curs(V293_dly_body 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z),(kenil,DCouter))
 ((DCge,DCle,Ma),(fun _=>false),(enabled,nil,nil))
 (curs DCafter,(kenil,DCcont))((DCge,DCle,Mf),(fun _=>false),(false,nil,[enabled])) /\
 (DCstate Mf enabled|=V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(13%positive,0%Z)Tint32 true Vundef **
 (Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **DCframe))) /\
 V293_task_records Mf DLtasks /\
 load Tint8 Mf(11%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint32 Mf(12%positive,0%Z)=Some(Vint32(Int.repr 3)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 V293_bytes_writable Mf 13%positive 0%Z 4 /\
 load Tint32 Mf(13%positive,0%Z)=Some Vundef /\
 load Tint32 Mf(13%positive,0%Z)<>Some(Vint32 Int.zero).
Proof.
 intro enabled.
 destruct(V293_dly_call_allocate DCprogram kstop DCge emp DCmem(fun _=>false)(enabled,nil,nil)
 DCabs(spec_done None)1200%Z 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z 402%Z
 12%positive 11%positive 13%positive(Int.repr 3)DCframe
 eq_refl ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 (DCfresh 12%positive ltac:(tauto))(DCfresh 11%positive ltac:(tauto))(DCfresh 13%positive ltac:(tauto))(DCentry enabled))
 as(Mp&ParamStore&Entry&Owned).
 set(Ma:=allocb(allocb Mp 11%positive 0%Z 1)13%positive 0%Z 4)in *.
 assert(Frame:DCstate Ma enabled|=DCframe **Atrue)by(clear -Owned;sep auto).
 assert(Read:forall a tp v,In(a,tp,v)DCcells ->load tp Ma a=Some v)
 by(intros a tp v Member;exact(DCframe_load a tp v Member(DCstate Ma enabled)Frame)).
 assert(Ticks:load Tint32 Ma(12%positive,0%Z)=Some(Vint32(Int.repr 3))).
 { assert(Slot:DCstate Ma enabled|=Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **Atrue)
   by(clear -Owned;sep auto).
   exact(DCraw_load (12%positive,0%Z)Tint32(Vint32(Int.repr 3))(DCstate Ma enabled)eq_refl Slot). }
 assert(YRaw:load Tint8 Ma(11%positive,0%Z)=Some Vundef).
 { assert(Slot:DCstate Ma enabled|=Amapsto(11%positive,0%Z)Tint8 true Vundef **Atrue)
   by(clear -Owned;sep auto).
   exact(DCundef_load (11%positive,0%Z)Tint8(DCstate Ma enabled)(or_introl eq_refl)Slot). }
 assert(YOwned:DCstate Ma enabled|=Amapsto(11%positive,0%Z)Tint8 true Vundef **
 (Amapsto(13%positive,0%Z)Tint32 true Vundef **
 (Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **DCframe)))
 by(clear -Owned;sep auto).
 destruct(V293_dly_body_first_y DCprogram DCouter DCge DCle Ma(fun _=>false)enabled nil nil DCabs(spec_done None)
 _ 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 60%positive 0%Z 0 70%positive 71%positive 12%positive(Int.repr 3)
 eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)
 eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)eq_refl Ticks ltac:(discriminate)
 eq_refl eq_refl eq_refl ltac:(apply Read;vm_compute;tauto)ltac:(apply Read;vm_compute;tauto)
 ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)ltac:(lia)YOwned)
 as(Mf&YStore&Prefix&Post&Outside).

 exists Mp;exists Mf;fold Ma;split;[exact ParamStore| ];split;[exact Entry| ];
 split;[exact YRaw| ];split;[exact Prefix| ];split;[exact Post| ].
 assert(FrameF:DCstate Mf enabled|=DCframe **Atrue)by(clear -Post;sep auto).
 assert(CPU:DCstate Mf enabled|=Amapsto(13%positive,0%Z)Tint32 true Vundef **Atrue)
 by(clear -Post;sep auto).
 assert(Raw:load Tint32 Mf(13%positive,0%Z)=Some Vundef)
 by(exact(DCundef_load (13%positive,0%Z)Tint32(DCstate Mf enabled)(or_intror eq_refl)CPU)).
 split;[exact(DCframe_records _ FrameF)| ];split.
 - assert(Y:DCstate Mf enabled|=V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **Atrue)
   by(clear -Post;sep auto).
   eapply V293_record_star_load_l with(s:=DCstate Mf enabled);[apply V293_owned_record_cell_load|exact Y].
 - split.
   + assert(Slot:DCstate Mf enabled|=Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **Atrue)
     by(clear -Post;sep auto).
     exact(DCraw_load (12%positive,0%Z)Tint32(Vint32(Int.repr 3))(DCstate Mf enabled)eq_refl Slot).
   + split;[exact(DCframe_load (90%positive,0%Z)Tint32(Vint32(Int.repr 99)) ltac:(vm_compute;tauto)(DCstate Mf enabled)FrameF)| ].
     split;[exact(V293_tick_raw_owned_writable 13%positive Tint32 Vundef Atrue DCge DCle Mf
       (fun _=>false)(enabled,nil,nil)DCabs(spec_done None)CPU)| ].
     split;[exact Raw|rewrite Raw;discriminate].
Qed.

Theorem DCinitialized_cpu_writable:forall enabled,exists Mf,
 DCpost Mf enabled /\V293_bytes_writable Mf 13%positive 0%Z 4.
Proof.
 intro enabled;destruct(DCcall_first_y enabled)as(Mp&Mi&Mf&Param&Init&Raw&Trace&Post&Rest).
 exists Mf;split;[exact Post| ].
 assert(CPU:DCstate Mf enabled|=Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 by(unfold DCpost in Post;clear -Post;sep auto).
 exact(V293_tick_raw_owned_writable 13%positive Tint32(Vint32 Int.zero)Atrue DCge DCle Mf
       (fun _=>false)(enabled,nil,nil)DCabs(spec_done None)CPU).
Qed.

(* This concrete frame contains no aux-sensitive assertion. Only here may
   the entry snapshot be converted to the actual critical endpoint state. *)
Theorem DCactual_critical_post:forall enabled,exists Mf,
 V293_local_steps DCprogram(curs(scall 1200%Z[econst32(Int.repr 3)]),(kenil,kstop))
 ((DCge,emp,DCmem),(fun _=>false),(enabled,nil,nil))
 (curs DCafter,(kenil,DCcont))((DCge,DCle,Mf),(fun _=>false),(false,nil,[enabled])) /\
 ((DCge,DCle,Mf,(fun _=>false),(false,nil,[enabled]),DCabs,spec_done None)|=
 V293_owned_record_cell((11%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(13%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(12%positive,0%Z)Tint32 true(Vint32(Int.repr 3)) **DCframe))).
Proof.
 intro enabled;destruct(DCboth_IE enabled)as(Mf&Trace&Post).
 exists Mf;split;[exact Trace|change(DCpost Mf enabled);exact Post].
Qed.
