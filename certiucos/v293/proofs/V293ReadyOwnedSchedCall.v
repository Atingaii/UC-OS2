(* A real scheduler call transports joint ready ownership to its source
   switch-or-skip boundary. The current task need not still be ready. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_owned_ready_good : forall br bg bp current,
 GoodInvAsrt(V293_ready_full br bg bp current).
Proof.
 intros;change(forall tasks events now,GoodInvAsrt
 ((EX tp:type,GV OSTCBCur@(Tptr tp)|->Vptr current) **
 (V293_shared_fields current tasks events now **V293_ready_payload br bg bp tasks))).
 intros;split;[ |split;[ |apply V293_ready_payload_good]].
 - unfold Agvarmapsto,Aptrmapsto;cbn;intros;repeat split;exact I.
 - unfold V293_shared_fields;cbn;repeat split;exact I.
Qed.

Lemma V293_owned_ready_disabled : forall br bg bp current ge le M ci O op R,
 (ge,le,M,(fun _:hid=>false),(false,nil,ci),O,op)|=
 V293_ready_full br bg bp current **R ->
 (ge,le,M,(fun _:hid=>false),(false,nil,ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)current **R.
Proof.
 intros br bg bp current ge le M ci O op R Held.
 assert(Flags:(ge,le,emp,(fun _:hid=>false),(false,nil,ci),emp,op)|=V293_shared_flags).
 { unfold V293_shared_flags;apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
   split;[apply map_join_emp| ];split;[apply map_join_emp| ];split.
   - apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
     split;[apply map_join_emp| ];split;[apply map_join_emp| ];split.
     + exists(fun _:hid=>false);split;repeat split;reflexivity.
     + repeat split;reflexivity.
   - exists INUM;repeat split;reflexivity. }
 assert(Joint:(ge,le,M,(fun _:hid=>false),(false,nil,ci),O,op)|=
 V293_shared_flags **(V293_ready_full br bg bp current **R)).
 { apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split;assumption. }
 apply astar_assoc_intro in Joint.
 eapply astar_mono;[apply V293_ready_switch_halves|intros s H;exact H|exact Joint].
Qed.

Definition V293_owned_sched_frame bh bo bc bn bi bl oldhigh oldtarget nc c R:=
 V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32 c) **
 (V293_owned_record_cell((bi,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))))).

(* Inputs contain ownership, bindings and lookup bytes, not an execution,
   a successful store, or an already established switch invariant. *)
Theorem V293_owned_sched_call : forall br bg bp P ks ge caller M enabled ci O op current R
 f saved interrupt lock helper table high target cached counter unmap group rows y
 bt bh bo bc bn bi bl oldhigh oldtarget nc c,
 P f=Some(V293_OSSched_success_function saved interrupt lock helper table high target cached counter) ->
 P helper=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved(cons interrupt(cons lock(cons table(cons high(cons target(cons cached(cons counter nil))))))) ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->
 get ge interrupt=Some(bi,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->
 get ge target=Some(bo,Tptr V293_tcb_type) ->get ge cached=Some(bc,Tint8) ->
 get ge counter=Some(bn,Tint32) ->nc<256 ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,caller,M,(fun _:hid=>false),(enabled,nil,ci),O,op)|=
 V293_ready_full br bg bp current **
 V293_owned_sched_frame bh bo bc bn bi bl oldhigh oldtarget nc c R ->
 exists bs byblock Mi My Mh Mtarget Mf,exists tasks lo hi entries next message,
 fresh M bs /\fresh Mi byblock /\
 get O abstcblsid=Some(abstcblist tasks) /\V293_ready_rel lo hi entries tasks /\
 get tasks next=Some(Int.repr(Z.of_nat(V293_ready_select lo hi(V293_ready_group lo hi))),rdy,message) /\
 V293_local_steps P(curs(scall f nil),(kenil,ks))
 ((ge,caller,M),(fun _:hid=>false),(enabled,nil,ci))
 ((if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then SKIP else curs(sprim(switch target))),
 (kenil,kseq(sseq(sprim excrit)sret)
 (kcall f(V293_OSSched_success_body saved interrupt lock helper table high target cached counter)caller ks)))
 ((ge,V293_cpu_lenv saved bs,Mf),(fun _:hid=>false),(false,nil,enabled::ci)) /\
 cstepstar P
 (curs(V293_OSSched_unlocked_prefix helper table high target),
 (kenil,kseq(V293_OSSched_change high cached counter(sprim(switch target)))
 (kseq(sseq(sprim excrit)sret)
 (kcall f(V293_OSSched_success_body saved interrupt lock helper table high target cached counter)caller ks))))
 (ge,V293_cpu_lenv saved bs,Mi)
 (SKIP,(kenil,kseq(V293_OSSched_change high cached counter(sprim(switch target)))
 (kseq(sseq(sprim excrit)sret)
 (kcall f(V293_OSSched_success_body saved interrupt lock helper table high target cached counter)caller ks))))
 (ge,V293_cpu_lenv saved bs,Mtarget) /\
 free Tint8 byblock My=Some Mh /\get Mh(byblock,0%Z)=None /\
 (if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then Mf=Mtarget else
 store Tint32 Mtarget(bn,0%Z)(Vint32(Int.add c Int.one))=Some Mf) /\
 (ge,V293_cpu_lenv saved bs,Mf,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)current **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32
 (if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then c else Int.add c Int.one)) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bi,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))))))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint32 Mf(bn,0%Z)=Some(Vint32
 (if Nat.eqb(V293_ready_select lo hi(V293_ready_group lo hi))nc then c else Int.add c Int.one)).
Proof.
 intros br bg bp P ks ge caller M enabled ci O op current R f saved interrupt lock helper table high
 target cached counter unmap group rows y bt bh bo bc bn bi bl oldhigh oldtarget nc c
 Program Helper Saved YT YG YR YH YP HP GI GL GT GG GR GH GP GO GC GN Nc Good Lookup Held.
 destruct(V293_ready_fresh_avoiding M(cons bt nil))as(bs&Fresh&Away).
 assert(BT:bs<>bt)by(intro E;apply Away;left;symmetry;exact E).
 set(le:=V293_cpu_lenv saved bs).
 assert(Names:forall x,In x(cons interrupt(cons lock(cons table(cons high(cons target(cons cached(cons counter nil))))))) ->get le x=None).
 { intros x Member;unfold le,V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply Saved;subst;exact Member. }
 set(body:=V293_OSSched_success_body saved interrupt lock helper table high target cached counter).
 set(change:=V293_OSSched_change high cached counter(sprim(switch target))).
 set(K:=kseq(sseq(sprim excrit)sret)(kcall f body caller ks)).
 set(F:=V293_owned_sched_frame bh bo bc bn bi bl oldhigh oldtarget nc c R).
 assert(GFrame:GoodInvAsrt F).
 { unfold F,V293_owned_sched_frame,V293_owned_record_cell;cbn;repeat split;try exact I;exact Good. }
 destruct(V293_sched_call_enter P ks ge caller M(fun _:hid=>false)(enabled,nil,ci)
 f saved interrupt lock helper table high target cached counter bs Program Fresh)
 as(Mi&Init&Writable&InitialFree&InitFrame&Enter).
 assert(CPU:(ge,caller,Mi,(fun _:hid=>false),(enabled,nil,ci),O,op)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **(V293_ready_full br bg bp current **F)).
 { eapply V293_cpu_initialized_frame;[exact Fresh|exact Held|exact Init]. }
 assert(Prepared:(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
 V293_ready_full br bg bp current **(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **F)).
 { assert(GoodAll:GoodInvAsrt(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
   (V293_ready_full br bg bp current **F))).
   { split;[cbn;exact I|split;[apply V293_owned_ready_good|exact GFrame]]. }
   pose proof(good_inv_prop _ GoodAll _ _ _ _ _ _ _ _ _ CPU le op false(enabled::ci))as H.
   clear -H;sep auto. }
 assert(IL:load Tint8 Mi(bi,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(getmem(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op))(bi,0%Z)=Some(V293_byteval 0)).
   assert(Cell:(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
   V293_owned_record_cell((bi,0%Z),Tint8,V293_byteval 0) **Atrue)
   by(unfold F,V293_owned_sched_frame in Prepared;clear -Prepared;sep auto).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Cell]. }
 assert(LL:load Tint8 Mi(bl,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(getmem(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op))(bl,0%Z)=Some(V293_byteval 0)).
   assert(Cell:(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
   V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **Atrue)
   by(unfold F,V293_owned_sched_frame in Prepared;clear -Prepared;sep auto).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Cell]. }
 pose proof(V293_sched_control_enter P(kcall f body caller ks)ge le Mi(fun _:hid=>false)enabled nil ci
 interrupt lock bi bl 0 0(sseq(V293_OSSched_unlocked_prefix helper table high target)change)
 ltac:(lia)ltac:(lia)(Names interrupt ltac:(cbn;tauto))GI(Names lock ltac:(cbn;tauto))GL IL LL)as Guards.
 cbn in Guards.
 set(Rest:=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bi,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **R))).
 assert(GDispatch:GoodInvAsrt(V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32 c) **Rest))).
 { unfold V293_owned_record_cell;cbn;repeat split;try exact I;exact Good. }
 assert(Ready:(ge,le,Mi,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)current **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32 c) **Rest))))).
 { apply V293_owned_ready_disabled in Prepared;unfold F,V293_owned_sched_frame in Prepared.
   unfold Rest;clear -Prepared;sep auto. }
 assert(LookupI:forall n,n<256 ->load Tint8 Mi(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros;rewrite <- (Lookup n H);apply V293_load_block_frame;intros;apply InitFrame;congruence. }
 destruct(V293_ready_dispatch_call br bg bp P(kseq change K)ge le Mi(fun _:hid=>false)
 (false,nil,enabled::ci)O op current
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32 c) **Rest))
 helper unmap group rows high y table target bt bh bo oldhigh oldtarget
 Helper YT YG YR YH YP HP GT GG GR GH GP
 (Names high ltac:(cbn;tauto))(Names table ltac:(cbn;tauto))(Names target ltac:(cbn;tauto))GO
 GDispatch LookupI Ready)
 as(tasks&lo&hi&entries&next&message&byblock&My&Mh&Mtarget&FreshY&Map&Rel&Task&Call&Skipped&Free&Removed&High&Prefix&Store&After&Target&Sched&Pre&Member&Dead&CallFrame&Frame).
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];apply V293_ready_selection_range;assumption||reflexivity. }
 assert(TailEntry:(ge,le,Mtarget,(fun _:hid=>false),(false,nil,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)current **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((bn,0%Z),Tint32,Vint32 c) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **Rest))))).
 { clear Ready Skipped Pre;sep auto. }
 destruct(V293_ready_source_change br bg bp P K ge le Mtarget(fun _:hid=>false)(false,nil,enabled::ci)O op current
 high cached counter target bh bc bn(V293_ready_select lo hi(V293_ready_group lo hi))nc c
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **Rest)
 ltac:(lia)Nc(Names high ltac:(cbn;tauto))(Names cached ltac:(cbn;tauto))(Names counter ltac:(cbn;tauto))GH GC GN TailEntry)
 as(Mf&Tail&CounterStore&Final&CounterLoad&Outside).
 assert(TargetFinal:load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next)).
 { change(load(Tptr V293_tcb_type)(getmem(ge,le,Mf,(fun _:hid=>false),(false,nil,enabled::ci),O,op))(bo,0%Z)=Some(Vptr next)).
   eapply V293_record_star_load_r;[ |exact Final].
   eapply V293_record_star_load_r;eapply V293_record_star_load_r;eapply V293_record_star_load_r.
   eapply V293_record_star_load_l;apply V293_owned_record_cell_load. }
 exists bs;exists byblock;exists Mi;exists My;exists Mh;exists Mtarget;exists Mf.
 exists tasks;exists lo;exists hi;exists entries;exists next;exists message.
 split;[exact Fresh| ];split;[exact FreshY| ];split;[exact Map| ];split;[exact Rel| ];split;[exact Task| ];split.
 - eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply snpcall_step]| ].
   eapply V293_local_trans;[exact Enter| ].
   eapply V293_local_trans;[exact Guards| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact Prefix| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   apply V293_csteps_local;exact Tail.
 - split;[exact Prefix| ];split;[exact Free| ];split;[exact Removed| ];split;[exact CounterStore| ];
   split;[exact Final| ];split;[exact TargetFinal|exact CounterLoad].
Qed.
