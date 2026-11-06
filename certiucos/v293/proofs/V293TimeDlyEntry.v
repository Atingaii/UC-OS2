(* Exact normalized OSTimeDly body, after cpu_sr=0 initialization.
   Execute guards, critical stack push/pop and the real blocking updates.
   The positive path stops BEFORE calling OS_Sched; no switch is invented. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyBlocking.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeDly.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_dly_unsigned_positive : forall n,
 Int.ltu Int.zero n=if Int.eq n Int.zero then false else true.
Proof.
 intro n;destruct(Int.eq_dec n Int.zero)as[Zero|Nonzero].
 - subst n;reflexivity.
 - rewrite Int.eq_false by exact Nonzero.
   assert(Positive:(0<Int.unsigned n)%Z).
   { pose proof(Int.unsigned_range n)as Range.
     assert(Int.unsigned n<>0%Z).
     { intro E;apply Nonzero;rewrite <-(Int.repr_unsigned n),E;reflexivity. }
     lia. }
   unfold Int.ltu;rewrite Int.unsigned_zero.
   destruct(zlt 0(Int.unsigned n));[reflexivity|lia].
Qed.

Lemma V293_dly_byte_guard_eval : forall ge le M x b n,
 n<256 ->get le x=None ->get ge x=Some(b,Tint8) ->
 load Tint8 M(b,0%Z)=Some(V293_byteval n) ->
 evalval(ebinop olt(econst32 Int.zero)(ecast(evar x)Tint32))(ge,le,M)=
 Some(Vint32(if negb(Nat.eqb n 0)then Int.one else Int.zero)).
Proof.
 intros ge le M x b n Bound Local Global Read.
 cbn[evalval evaltype evaladdr get_lenv get_genv];rewrite Local,Global.
 cbn -[load];rewrite Read;unfold V293_byteval.
 cbn[cast_eval bop_eval cmp_val cmpu].
 rewrite V293_exit_positive by exact Bound;destruct(negb(Nat.eqb n 0));reflexivity.
Qed.
Lemma V293_dly_ticks_guard_eval : forall ge le M ticks bd duration,
 get le ticks=Some(bd,Tint32) ->load Tint32 M(bd,0%Z)=Some(Vint32 duration) ->
 evalval(ebinop olt(econst32 Int.zero)(evar ticks))(ge,le,M)=
 Some(Vint32(if Int.eq duration Int.zero then Int.zero else Int.one)).
Proof.
 intros ge le M ticks bd duration Binding Read.
 cbn[evalval evaltype evaladdr get_lenv get_genv];rewrite Binding.
 cbn -[load];rewrite Read;cbn[bop_eval cmp_val cmpu].
 rewrite V293_dly_unsigned_positive;destruct(Int.eq duration Int.zero);reflexivity.
Qed.

(* Branch entry, not a premise that its body already executes. *)
Lemma V293_dly_if_branch : forall P ks m cond body (flag:bool),
 evalval cond m=Some(Vint32(if flag then Int.one else Int.zero)) ->
 cstepstar P(curs(sifthen cond body),(kenil,ks))m
 (curs(if flag then body else sskip None),(kenil,ks))m.
Proof.
 intros P ks m cond body flag Test.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sifthen_step]| ].
 eapply V293_cstepstar_trans.
 { apply V293_expr_steps;apply evalval_imply_estepstar;exact Test. }
 destruct flag;eapply c_stepstarn;
 [eapply stmt_step;[reflexivity|apply svift_step;reflexivity]|apply c_stepstar0|
  eapply stmt_step;[reflexivity|apply sviff_step;reflexivity]|apply c_stepstar0].
Qed.

Lemma V293_dly_guards_positive : forall P ks ge le M
 ticks nesting lock positive bi bl bd duration,
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 get le ticks=Some(bd,Tint32) ->load Tint32 M(bd,0%Z)=Some(Vint32 duration) ->duration<>Int.zero ->
 cstepstar P(curs(sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar nesting)Tint32))sret)
 (sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar lock)Tint32))sret)
 (sseq(sifthen(ebinop olt(econst32 Int.zero)(evar ticks))positive)sret))),(kenil,ks))(ge,le,M)
 (curs(positive),(kenil,kseq sret ks))(ge,le,M).
Proof.
 intros P ks ge le M ticks nesting lock positive bi bl bd duration
 Nn Gn Ln Nl Gl Ll Bd Ld Positive.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_cstepstar_trans.
 { apply V293_dly_if_branch with(flag:=false).
   exact(V293_dly_byte_guard_eval ge le M nesting bi 0 ltac:(lia)Nn Gn Ln). }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_cstepstar_trans.
 { apply V293_dly_if_branch with(flag:=false).
   exact(V293_dly_byte_guard_eval ge le M lock bl 0 ltac:(lia)Nl Gl Ll). }
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 apply V293_dly_if_branch with(flag:=true).
 rewrite(V293_dly_ticks_guard_eval _ _ _ _ _ _ Bd Ld).
 rewrite Int.eq_false by exact Positive;reflexivity.
Qed.

Lemma V293_dly_body_enters_positive : forall P ks ge le M
 current rows group y ticks nesting lock sched bi bl bd duration,
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->
 load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->
 load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 get le ticks=Some(bd,Tint32) ->load Tint32 M(bd,0%Z)=Some(Vint32 duration) ->duration<>Int.zero ->
 cstepstar P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,ks))(ge,le,M)
 (curs(V293_dly_positive current rows group y ticks sched),(kenil,kseq sret ks))(ge,le,M).
Proof.
 intros;unfold V293_dly_body;eapply V293_dly_guards_positive;eassumption.
Qed.

(* Stable positive-body interface. The spatial snapshot uses entry aux;
   csteps do not inspect aux, and actual loststeps restore that same aux.
   This does NOT transport an arbitrary aux-sensitive frame to the middle. *)
Theorem V293_OSTimeDly_body_to_sched_refines : forall current rows group y ticks nesting lock sched
 bc byloc bd bt br bg bi bl base p duration P ks ge le M ir enabled si ci O op sd R
 delay yv lo hi entries tasks message events now,
 V293_dly_env current rows group y ticks bc byloc bd br bg ge le ->
 get le nesting=None ->get ge nesting=Some(bi,Tint8) ->load Tint8 M(bi,0%Z)=Some(V293_byteval 0) ->
 get le lock=None ->get ge lock=Some(bl,Tint8) ->load Tint8 M(bl,0%Z)=Some(V293_byteval 0) ->
 p<13 ->lo<256 ->hi<256 ->(0<=base)%Z ->(base+54<=Int.max_unsigned)%Z ->
 duration<>Int.zero ->V293_priority_table entries tasks ->V293_bitmap_tasks lo hi tasks ->
 get tasks(bt,Int.repr base)=Some(Int.repr(Z.of_nat p),rdy,message) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration delay yv lo hi(V293_ready_group lo hi)) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)tasks events now **R))) ->
 let blocked:=set tasks(bt,Int.repr base)(Int.repr(Z.of_nat p),wait os_stat_time duration,message) in
 let O':=set O abstcblsid(abstcblist blocked) in
 let cleared:=V293_ready_clear_rows lo hi p in
 exists Mf,
 V293_local_steps P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(scall sched nil),(kenil,kseq sret ks))((ge,le,Mf),ir,(enabled,si,ci)) /\
 spec_step sd(spec_prim(cons(Vint32 duration)nil)V293_dly_block_step)O(END None)O' /\
 V293_task_records Mf blocked /\V293_priority_table entries blocked /\
 V293_bitmap_tasks(fst cleared)(snd cleared)blocked /\
 (ge,le,Mf,ir,(enabled,si,ci),O',op)|=V293_owned_record_cells
  (V293_dly_cells bc byloc bd bt br bg base p duration duration(V293_byteval(V293_prio_row p))
   (fst cleared)(snd cleared)(V293_ready_group(fst cleared)(snd cleared))) **
  (V293_owned_record_cells(V293_dly_record_extra bt base p message) **
  (V293_owned_task_records(del tasks(bt,Int.repr base)) **
  (V293_shared_fields(bt,Int.repr base)blocked events now **R))).
Proof.
 intros current rows group y ticks nesting lock sched bc byloc bd bt br bg bi bl base p duration P ks
 ge le M ir enabled si ci O op sd R delay yv lo hi entries tasks message events now
 Env Nn Gn Ln Nl Gl Ll Pb Lo Hi Base Limit Positive Table Bitmap Task Owned blocked O' cleared.
 assert(TickRead:load Tint32 M(bd,0%Z)=Some(Vint32 duration)).
 { change(load Tint32(getmem(ge,le,M,ir,(enabled,si,ci),O,op))(bd,0%Z)=Some(Vint32 duration)).
   eapply V293_record_star_load_l;[ |exact Owned].
   apply V293_owned_record_cells_load;cbn[V293_dly_cells In];tauto. }
 destruct Env as(Nc&Gc&Nr&Gr&Ng&Gg&By&Bd).
 assert(Env:V293_dly_env current rows group y ticks bc byloc bd br bg ge le)by(repeat split;assumption).
 set(tail:=kseq sret ks).
 destruct(V293_OSTimeDly_updates_refines current rows group y ticks bc byloc bd bt br bg base p duration
 P(kseq(sseq(sprim excrit)(scall sched nil))tail)ge le M ir(enabled,si,ci)O op sd R
 delay yv lo hi entries tasks message events now Env Pb Lo Hi Base Limit Positive Table Bitmap Task Owned)
 as(Mf&Updates&Step&Records&Prio&Bits&Returned).
 exists Mf;split;[ |split;[exact Step|split;[exact Records|split;[exact Prio|split;[exact Bits|exact Returned]]]]].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_dly_body_enters_positive;eassumption. }
 unfold V293_dly_positive;fold tail.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_cons;[apply encrit_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_trans;[apply V293_csteps_local;exact Updates| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply V293_local_cons;[apply excrit_step;reflexivity| ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
 apply V293_local_refl.
Qed.

(* Short-circuit read requirements. No binding/load is required for guards
   after the first rejection; neither task-table ownership nor sched exists
   in this precondition. These are body-entry facts, not allocation facts. *)
Definition V293_dly_rejects (ge le:env)(M:mem)(ticks nesting lock:var) : Prop :=
 exists bi ni,
 get le nesting=None /\get ge nesting=Some(bi,Tint8) /\
 load Tint8 M(bi,0%Z)=Some(V293_byteval ni) /\ni<256 /\
 (ni<>0 \/ (ni=0 /\exists bl nl,
 get le lock=None /\get ge lock=Some(bl,Tint8) /\
 load Tint8 M(bl,0%Z)=Some(V293_byteval nl) /\nl<256 /\
 (nl<>0 \/ (nl=0 /\exists bd,
 get le ticks=Some(bd,Tint32) /\load Tint32 M(bd,0%Z)=Some(Vint32 Int.zero))))).

Lemma V293_dly_reject_cut : forall P ks ge le M current rows group y ticks nesting lock sched,
 V293_dly_rejects ge le M ticks nesting lock ->
 exists suffix,
 cstepstar P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,ks))(ge,le,M)
 (curs sret,(kenil,suffix))(ge,le,M) /\callcont suffix=callcont ks.
Proof.
 intros P ks ge le M current rows group y ticks nesting lock sched
 (bi&ni&Nn&Gn&Ln&Nb&Choice).
 destruct Choice as[Nonzero|[Zero(bl&nl&Nl&Gl&Ll&Lb&Choice)]].
 - exists(kseq(sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar lock)Tint32))sret)
    (sseq(sifthen(ebinop olt(econst32 Int.zero)(evar ticks))
      (V293_dly_positive current rows group y ticks sched))sret))ks).
   split;[ |reflexivity]. unfold V293_dly_body.
   eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
   apply V293_dly_if_branch with(flag:=true).
   rewrite(V293_dly_byte_guard_eval ge le M nesting bi ni Nb Nn Gn Ln).
   assert(N:Nat.eqb ni 0=false)by(apply Nat.eqb_neq;exact Nonzero).
   rewrite N;reflexivity.
 - subst ni;destruct Choice as[Nonzero|[Zero(bd&Bd&Ld)]].
   + exists(kseq(sseq(sifthen(ebinop olt(econst32 Int.zero)(evar ticks))
      (V293_dly_positive current rows group y ticks sched))sret)ks).
     split;[ |reflexivity]. unfold V293_dly_body.
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_cstepstar_trans.
     { apply V293_dly_if_branch with(flag:=false).
       exact(V293_dly_byte_guard_eval ge le M nesting bi 0 Nb Nn Gn Ln). }
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     apply V293_dly_if_branch with(flag:=true).
     rewrite(V293_dly_byte_guard_eval ge le M lock bl nl Lb Nl Gl Ll).
     assert(N:Nat.eqb nl 0=false)by(apply Nat.eqb_neq;exact Nonzero).
     rewrite N;reflexivity.
   + subst nl;exists ks;split;[ |reflexivity]. unfold V293_dly_body.
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_cstepstar_trans.
     { apply V293_dly_if_branch with(flag:=false).
       exact(V293_dly_byte_guard_eval ge le M nesting bi 0 Nb Nn Gn Ln). }
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_cstepstar_trans.
     { apply V293_dly_if_branch with(flag:=false).
       exact(V293_dly_byte_guard_eval ge le M lock bl 0 Lb Nl Gl Ll). }
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
     eapply V293_cstepstar_trans.
     { apply V293_dly_if_branch with(flag:=false).
       exact(V293_dly_ticks_guard_eval ge le M ticks bd Int.zero Bd Ld). }
     eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]| ].
     apply c_stepstar0.
Qed.

(* Stable rejection interface: actual sret/free/caller restoration, not a
   stuck sret or an assumed callee; all nonlocal bytes and aux are preserved. *)
Theorem V293_OSTimeDly_early_return : forall P ks ge le caller M ir aux
 current rows group y ticks nesting lock sched f body next,
 V293_dly_rejects ge le M ticks nesting lock ->
 callcont ks=Some(kcall f body caller next) ->NoDup(map fst(getaddr le)) ->
 (forall b tp,In(b,tp)(getaddr le)->V293_bytes_writable M b 0%Z(typelen tp)) ->
 exists Mf,
 V293_local_steps P(curs(V293_dly_body current rows group y ticks nesting lock sched),(kenil,ks))
 ((ge,le,M),ir,aux)(curs(sskip None),(kenil,next))((ge,caller,Mf),ir,aux) /\
 (forall b i,~In b(map fst(getaddr le))->get Mf(b,i)=get M(b,i)) /\
 (forall b tp k,In(b,tp)(getaddr le)->k<typelen tp->get Mf(b,Z.of_nat k)=None).
Proof.
 intros P ks ge le caller M ir aux current rows group y ticks nesting lock sched f body next
 Reject Call ND Writable.
 destruct(V293_dly_reject_cut P ks ge le M current rows group y ticks nesting lock sched Reject)
 as(suffix&Prefix&SameCall).
 destruct(V293_void_return_execution P suffix ge le caller M f body next
 ltac:(rewrite SameCall;exact Call)ND Writable)as(Mf&Return&Frame&Removed).
 exists Mf;split;[ |split;assumption].
 eapply V293_local_trans;apply V293_csteps_local;[exact Prefix|exact Return].
Qed.
