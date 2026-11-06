(* Nonempty body-entry fixtures, not initialized kernel reachability.
   Both task records, globals, all three locals and a separate canary exist. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.audit.probes.V293TimeDlyBlockingProbe.
Require Import CertiOS.audit.probes.V293TimeDlyTaskBridgeProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition DEge:env:=set(set DLge 110%Z(70%positive,Tint8))111%Z(71%positive,Tint8).
Definition DEle:env:=set DLle 402%Z(13%positive,Tint32).
Definition DEcells duration:=V293_dly_cells 10%positive 11%positive 12%positive
 60%positive 30%positive 31%positive 0%Z 4 duration Int.zero(V293_byteval 0)80 0 1.
Definition DEframe ni nl:list V293_record_cell:=
 [((70%positive,0%Z),Tint8,V293_byteval ni);((71%positive,0%Z),Tint8,V293_byteval nl);
  ((13%positive,0%Z),Tint32,Vint32 Int.zero);((90%positive,0%Z),Tint32,Vint32(Int.repr 99))].
Definition DEall duration ni nl:=DEcells duration++(DLextra++(DLlow++DEframe ni nl)).
Definition DEmem duration ni nl:=OwnershipCellsMemory(DEall duration ni nl).
Definition DEabs:=V293_shared_fixture_abs OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37).
Definition DEblocked duration:=set DLtasks OwnershipReady(Int.repr 4,wait os_stat_time duration,Vnull).
Definition DEfinalabs duration:=set DEabs abstcblsid(abstcblist(DEblocked duration)).
Definition DEbody:=V293_dly_body 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z.
Definition DEstate M O:=V293_target_wstate DEge DEle M O.

Lemma DEenv:V293_dly_env 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 30%positive 31%positive DEge DEle.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma DEspatial:forall duration ni nl,ni<256 ->nl<256 ->
 DEstate(DEmem duration ni nl)emp|=V293_owned_record_cells(DEall duration ni nl).
Proof.
 intros duration ni nl Ni Nl;apply OwnershipCellsSpatial.
 -   vm_compute;repeat split;intros;intuition congruence.
 - unfold DEall,DEcells,V293_dly_cells,DLextra,V293_dly_record_extra,DLlow,V293_record_layout,DEframe.
   apply Forall_forall;intros cell Member;cbn[app In]in Member.
   repeat destruct Member as[Same|Member];try contradiction;subst cell;try reflexivity;apply V293_byte_type;assumption.
Qed.
Lemma DEentry:forall duration ni nl,ni<256 ->nl<256 ->
 DEstate(DEmem duration ni nl)DEabs|=
 V293_owned_record_cells(DEcells duration) **(V293_owned_record_cells DLextra **
 (V293_owned_task_records(del DLtasks OwnershipReady) **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **
 V293_owned_record_cells(DEframe ni nl)))).
Proof.
 intros duration ni nl Ni Nl;pose proof(DEspatial duration ni nl Ni Nl)as Cells.
 assert(Physical:DEstate(DEmem duration ni nl)emp|=V293_owned_record_cells(DEcells duration) **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **V293_owned_record_cells(DEframe ni nl)))).
 { apply(proj1(OwnershipCellsAppend(DEcells duration)(DLextra++(DLlow++DEframe ni nl))_))in Cells.
   eapply astar_mono;[intros st H;exact H| |exact Cells].
   intros st H;apply OwnershipCellsAppend in H.
   eapply astar_mono;[intros st' H';exact H'| |exact H].
   intros st' H';apply OwnershipCellsAppend in H';exact H'. }
 assert(Joint:DEstate(DEmem duration ni nl)DEabs|=
 (V293_owned_record_cells(DEcells duration) **(V293_owned_record_cells DLextra **
 (V293_owned_record_cells DLlow **V293_owned_record_cells(DEframe ni nl)))) **
 V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)).
 { eapply V293_target_wstate_star with(m1:=DEmem duration ni nl)(m2:=emp)(o1:=emp)(o2:=DEabs).
   - apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - exact Physical.
   - exact(V293_shared_fixture_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37)). }
 assert(Reordered:DEstate(DEmem duration ni nl)DEabs|=V293_owned_record_cells(DEcells duration) **
 (V293_owned_record_cells DLextra **(V293_owned_record_cells DLlow **
 (V293_shared_fields OwnershipReady DLtasks(emp:EcbMod.map)(Int.repr 37) **V293_owned_record_cells(DEframe ni nl)))))
 by(clear -Joint;sep auto).
 eapply astar_mono;[intros st H;exact H| |exact Reordered].
 intros st H;eapply astar_mono;[intros st' H';exact H'| |exact H].
 intros st' H';eapply astar_mono;[apply DTlow_owned|intros st'' H'';exact H''|exact H'].
Qed.
Lemma DEreads:forall duration ni nl,ni<256 ->nl<256 ->
 load Tint8(DEmem duration ni nl)(70%positive,0%Z)=Some(V293_byteval ni) /\
 load Tint8(DEmem duration ni nl)(71%positive,0%Z)=Some(V293_byteval nl) /\
 load Tint32(DEmem duration ni nl)(12%positive,0%Z)=Some(Vint32 duration).
Proof.
 intros duration ni nl Ni Nl;pose proof(DEspatial duration ni nl Ni Nl)as Held.
 assert(Read:forall a tp v,In(a,tp,v)(DEall duration ni nl)->
 load tp(DEmem duration ni nl)a=Some v).
 { intros a tp v Member;exact(V293_owned_record_cells_load _ _ _ _ Member _ Held). }
 repeat split;apply Read;unfold DEall,DEcells,V293_dly_cells,DEframe;cbn;tauto.
Qed.

Theorem DEliteral:forall P ks sd enabled duration,duration<>Int.zero ->exists Mf,
 V293_local_steps P(curs DEbody,(kenil,ks))
 ((DEge,DEle,DEmem duration 0 0),(fun _=>false),(enabled,nil,nil))
 (curs(scall 112%Z nil),(kenil,kseq sret ks))((DEge,DEle,Mf),(fun _=>false),(enabled,nil,nil)) /\
 spec_step sd(spec_prim(cons(Vint32 duration)nil)V293_dly_block_step)DEabs(END None)(DEfinalabs duration) /\
 V293_task_records Mf(DEblocked duration) /\V293_bitmap_tasks 64 0(DEblocked duration) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)) /\
 get(DEfinalabs duration)curtid=Some(oscurt OwnershipReady).
Proof.
 intros P ks sd enabled duration Positive.
 destruct(DEreads duration 0 0 ltac:(lia)ltac:(lia))as[Ln[Ll Ld]].
 destruct(V293_OSTimeDly_body_to_sched_refines 103%Z 106%Z 105%Z 400%Z 401%Z 110%Z 111%Z 112%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 70%positive 71%positive 0%Z 4 duration
 P ks DEge DEle(DEmem duration 0 0)(fun _=>false)enabled nil nil DEabs(spec_done None)sd
 (V293_owned_record_cells(DEframe 0 0))Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DEenv eq_refl eq_refl Ln eq_refl eq_refl Ll ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)
 ltac:(change(54<=4294967295)%Z;lia)Positive DLtable DLbitmap eq_refl
 (DEentry duration 0 0 ltac:(lia)ltac:(lia)))as(Mf&Executed&Step&Records&Table&Bitmap&Returned).
 exists Mf;split;[exact Executed| ]. split;[exact Step| ]. split;[exact Records| ].
 split;[exact Bitmap| ]. split.
 - assert(Canary:(DEge,DEle,Mf,(fun _=>false),(enabled,nil,nil),DEfinalabs duration,spec_done None)|=
   V293_owned_record_cells(DEframe 0 0) **Atrue)by(clear -Returned;sep auto).
   change(load Tint32(getmem(DEge,DEle,Mf,(fun _=>false),(enabled,nil,nil),DEfinalabs duration,spec_done None))
   (90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Canary];apply V293_owned_record_cells_load;cbn[DEframe In];tauto.
 - reflexivity.
Qed.

Theorem DEhigh_unsigned:forall enabled,exists Mf,
 V293_local_steps(fun _=>None)(curs DEbody,(kenil,kstop))
 ((DEge,DEle,DEmem(Int.repr 2147483648)0 0),(fun _=>false),(enabled,nil,nil))
 (curs(scall 112%Z nil),(kenil,kseq sret kstop))((DEge,DEle,Mf),(fun _=>false),(enabled,nil,nil)) /\
 V293_task_records Mf(DEblocked(Int.repr 2147483648)).
Proof.
 intro enabled;destruct(DEliteral(fun _=>None)kstop(fun _ _=>False)enabled(Int.repr 2147483648)ltac:(discriminate))
 as(Mf&Exec&Step&Records&Rest);exists Mf;split;assumption.
Qed.

Lemma DErejection : forall duration ni nl,ni<256 ->nl<256 ->
 (ni<>0 \/ nl<>0 \/ duration=Int.zero) ->
 V293_dly_rejects DEge DEle(DEmem duration ni nl)401%Z 110%Z 111%Z.
Proof.
 intros duration ni nl Ni Nl Choice.
 destruct(DEreads duration ni nl Ni Nl)as[Ln[Ll Ld]].
 exists (70%positive);exists ni;split;[reflexivity| ];split;[reflexivity| ];split;[exact Ln| ];split;[exact Ni| ].
 destruct(Nat.eq_dec ni 0)as[Zero|Nonzero];[right;split;[exact Zero| ]|left;exact Nonzero].
 exists (71%positive);exists nl;split;[reflexivity| ];split;[reflexivity| ];split;[exact Ll| ];split;[exact Nl| ].
 destruct(Nat.eq_dec nl 0)as[ZeroL|NonzeroL];[right;split;[exact ZeroL| ]|left;exact NonzeroL].
 exists (12%positive);split;[reflexivity| ];assert(duration=Int.zero)by tauto;subst;exact Ld.
Qed.

Lemma DEwritable : forall duration ni nl,ni<256 ->nl<256 ->
 forall b tp,In(b,tp)(getaddr DEle)->V293_bytes_writable(DEmem duration ni nl)b 0%Z(typelen tp).
Proof.
 intros duration ni nl Ni Nl b tp Member.
 pose proof(DEspatial duration ni nl Ni Nl)as Held.
 unfold DEall,DEcells,V293_dly_cells,DLextra,V293_dly_record_extra,DLlow,V293_record_layout,DEframe in Held.
 cbn[app V293_owned_record_cells V293_owned_record_cell]in Held.
 assert(W11:V293_bytes_writable(DEmem duration ni nl)11%positive 0%Z(typelen Tint8)).
 { eapply V293_tick_raw_owned_writable with(v:=V293_byteval 0)(ge:=DEge)(le:=DEle)
   (ir:=fun _=>false)(aux:=(false,nil,nil))(O:=emp)(op:=spec_done None)(R:=Atrue).
   clear -Held;sep auto. }
 assert(W12:V293_bytes_writable(DEmem duration ni nl)12%positive 0%Z(typelen Tint32)).
 { eapply V293_tick_raw_owned_writable with(v:=Vint32 duration)(ge:=DEge)(le:=DEle)
   (ir:=fun _=>false)(aux:=(false,nil,nil))(O:=emp)(op:=spec_done None)(R:=Atrue).
   clear -Held;sep auto. }
 assert(W13:V293_bytes_writable(DEmem duration ni nl)13%positive 0%Z(typelen Tint32)).
 { eapply V293_tick_raw_owned_writable with(v:=Vint32 Int.zero)(ge:=DEge)(le:=DEle)
   (ir:=fun _=>false)(aux:=(false,nil,nil))(O:=emp)(op:=spec_done None)(R:=Atrue).
   clear -Held;sep auto. }
 vm_compute in Member;destruct Member as[E|[E|[E|E]]];
 [inversion E;subst;exact W11|inversion E;subst;exact W12|inversion E;subst;exact W13|contradiction].
Qed.

Theorem DEearly : forall P caller next enabled duration ni nl,ni<256 ->nl<256 ->
 (ni<>0 \/ nl<>0 \/ duration=Int.zero) ->exists Mf,
 V293_local_steps P(curs DEbody,(kenil,kcall 900%Z(sseq(sskip None)(sskip None))caller next))
 ((DEge,DEle,DEmem duration ni nl),(fun _=>false),(enabled,nil,nil))
 (curs(sskip None),(kenil,next))((DEge,caller,Mf),(fun _=>false),(enabled,nil,nil)) /\
 (forall b i,~In b(map fst(getaddr DEle))->get Mf(b,i)=get(DEmem duration ni nl)(b,i)) /\
 (forall b tp k,In(b,tp)(getaddr DEle)->k<typelen tp->get Mf(b,Z.of_nat k)=None).
Proof.
 intros P caller next enabled duration ni nl Ni Nl Choice.
 eapply V293_OSTimeDly_early_return with(f:=900%Z)(body:=sseq(sskip None)(sskip None)).
 - exact(DErejection duration ni nl Ni Nl Choice).
 - reflexivity.
 - vm_compute;constructor;[cbn;intuition congruence|constructor;[cbn;intuition congruence|constructor;[cbn;intuition congruence|constructor]]].
 - exact(DEwritable duration ni nl Ni Nl).
Qed.

(* Later guard identifiers are deliberately absent. Rejection must not read them. *)
Theorem DEnesting_shortcircuit : forall P ks,
 exists suffix,cstepstar P(curs DEbody,(kenil,ks))
 (sig 110%Z(70%positive,Tint8),(emp:env),DEmem Int.zero 255 0)
 (curs sret,(kenil,suffix))(sig 110%Z(70%positive,Tint8),(emp:env),DEmem Int.zero 255 0) /\
 callcont suffix=callcont ks.
Proof.
 intros P ks;eapply V293_dly_reject_cut.
 destruct(DEreads Int.zero 255 0 ltac:(lia)ltac:(lia))as[Read Rest].
 exists (70%positive);exists 255;split;[reflexivity| ];split;[reflexivity| ];
 split;[exact Read| ];split;[lia|left;lia].
Qed.

(* Prospective single-factor experiment: only replace excrit by SKIP.
   Both variants reach the same scheduler-call control point on the same
   input heap; their actual auxiliary states are measured separately. *)
Definition DEtail(restore:bool):=
 sseq(if restore then sprim excrit else sskip None)(scall 112%Z nil).
Definition DEpositive restore:=sseq(sprim encrit)
 (sseq(V293_dly_updates 103%Z 106%Z 105%Z 400%Z 401%Z)(DEtail restore)).
Definition DEvariant restore:=
 sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar 110%Z)Tint32))sret)
 (sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar 111%Z)Tint32))sret)
 (sseq(sifthen(ebinop olt(econst32 Int.zero)(evar 401%Z))(DEpositive restore))sret)).
Definition DEaux(restore enabled:bool):localst:=if restore then(enabled,nil,nil)else(false,nil,enabled::nil).
Lemma DEbaseline_exact : DEvariant true=DEbody.
Proof. reflexivity. Qed.

Definition DErun restore enabled Mf:=
 V293_local_steps(fun _=>None)(curs(DEvariant restore),(kenil,kstop))
 ((DEge,DEle,DEmem(Int.repr 3)0 0),(fun _=>false),(enabled,nil,nil))
 (curs(scall 112%Z nil),(kenil,kseq sret kstop))((DEge,DEle,Mf),(fun _=>false),DEaux restore enabled).
Theorem DEexperiment : forall restore enabled,exists Mf,
 DErun restore enabled Mf /\
 spec_step(fun _ _=>False)(spec_prim(cons(Vint32(Int.repr 3))nil)V293_dly_block_step)
 DEabs(END None)(DEfinalabs(Int.repr 3)) /\
 V293_task_records Mf(DEblocked(Int.repr 3)) /\V293_bitmap_tasks 64 0(DEblocked(Int.repr 3)) /\
 load Tint32 Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99)).
Proof.
 intros restore enabled.
 destruct(DEreads(Int.repr 3)0 0 ltac:(lia)ltac:(lia))as[Ln[Ll Ld]].
 destruct(V293_OSTimeDly_updates_refines 103%Z 106%Z 105%Z 400%Z 401%Z
 10%positive 11%positive 12%positive 60%positive 30%positive 31%positive 0%Z 4(Int.repr 3)
 (fun _=>None)(kseq(DEtail restore)(kseq sret kstop))DEge DEle(DEmem(Int.repr 3)0 0)
 (fun _=>false)(enabled,nil,nil)DEabs(spec_done None)(fun _ _=>False)
 (V293_owned_record_cells(DEframe 0 0))Int.zero(V293_byteval 0)80 0 DLentries DLtasks Vnull(emp:EcbMod.map)(Int.repr 37)
 DEenv ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(change(54<=4294967295)%Z;lia)
 ltac:(discriminate)DLtable DLbitmap eq_refl(DEentry(Int.repr 3)0 0 ltac:(lia)ltac:(lia)))
 as(Mf&Updates&Step&Records&Table&Bitmap&Returned).
 exists Mf;split.
 - unfold DErun.
   eapply V293_local_trans.
   { apply V293_csteps_local;unfold DEvariant.
     exact(V293_dly_guards_positive(fun _=>None)kstop DEge DEle(DEmem(Int.repr 3)0 0)
      401%Z 110%Z 111%Z(DEpositive restore)70%positive 71%positive 12%positive(Int.repr 3)
      eq_refl eq_refl Ln eq_refl eq_refl Ll eq_refl Ld ltac:(discriminate)). }
   unfold DEpositive.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans;[apply V293_csteps_local;exact Updates| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   unfold DEtail.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   destruct restore;cbn[DEaux].
   + eapply V293_local_cons;[apply excrit_step;reflexivity| ].
     eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply V293_local_refl.
   + eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply V293_local_refl.
 - split;[exact Step| ];split;[exact Records| ];split;[exact Bitmap| ].
   assert(Canary:(DEge,DEle,Mf,(fun _=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None)|=
   V293_owned_record_cells(DEframe 0 0) **Atrue)by(clear -Returned;sep auto).
   change(load Tint32(getmem(DEge,DEle,Mf,(fun _=>false),(enabled,nil,nil),DEfinalabs(Int.repr 3),spec_done None))
   (90%positive,0%Z)=Some(Vint32(Int.repr 99))).
   eapply V293_record_star_load_l;[ |exact Canary];apply V293_owned_record_cells_load;cbn[DEframe In];tauto.
Qed.
Lemma DEomitted_restore_detected : forall enabled,DEaux false enabled<>(enabled,nil,nil).
Proof. intros enabled Equal;inversion Equal. Qed.
