(* Full normalized OSIntExit call on quiet paths. The original caller
   postcondition remains explicit; every fresh allocation is covered. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallEntryProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Lemma V293_saved_exec_successor : forall p f saved body ks ge caller M C' m',
 p f=Some((Tvoid,dnil,dcons saved Tint32 dnil,body)) ->
 cstep p(curs(sfexec f nil nil),(kenil,ks))(ge,caller,M)C' m' ->
 C'=(curs(salloc nil(dcons saved Tint32 dnil)),
     (kenil,kcall f(body)caller ks)) /\
 m'=(ge,(emp:env),M).
Proof.
 intros p f saved body ks ge caller M C' m' Bind H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   
   match goal with H:p _=Some _ |- _ =>rewrite Bind in H;inversion H;subst end.
   split;reflexivity.
Qed.

Lemma V293_saved_alloc_successor : forall p saved ks ge M C' m',
 cstep p(curs(salloc nil(dcons saved Tint32 dnil)),(kenil,ks))(ge,(emp:env),M)C' m' ->
 exists b,fresh M b /\ C'=(curs(salloc nil dnil),(kenil,ks)) /\
 m'=(ge,(set emp saved(b,Tint32):env),allocb M b 0%Z 4).
Proof.
 intros p saved ks ge M C' m' H;inversion H;subst.
 - match goal with H:estep _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
 - match goal with H:sstep _ _ _ _ _ _ _ |- _ =>inversion H;subst;try discriminate end.
   inversion H0;subst.
   repeat match goal with E:(_,_,_)=(_,_,_) |- _ =>inversion E;subst;clear E end.
   match goal with H:alloc _ _ _ _ _ _ |- _ =>destruct H as(b&F&EqM&N&EqL);subst end.
   exists b;split;[exact F|split;reflexivity].
Qed.

Lemma V293_saved_alloc_step : forall p saved ks ge M b,
 fresh M b ->
 cstep p(curs(salloc nil(dcons saved Tint32 dnil)),(kenil,ks))(ge,(emp:env),M)
 (curs(salloc nil dnil),(kenil,ks))(ge,(set emp saved(b,Tint32):env),allocb M b 0%Z 4).
Proof.
 intros p saved ks ge M b F;eapply stmt_step;[reflexivity| ].
 eapply salloclv_step;[reflexivity|reflexivity| ].
 exists b;repeat split;try assumption;try reflexivity.
 intros [v E];rewrite map_emp_get in E;discriminate.
Qed.

(* Every fresh allocation is covered at the original evaluated call boundary. *)
Theorem V293_saved_exec_entry_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs
 f saved body ks ph Th O,
 po f=Some((Tvoid,dnil,dcons saved Tint32 dnil,body)) ->
 get les t=Some caller -> get aus t=Some((false,si,cs):localst) ->
 get T t=Some(curs(sfexec f nil nil),(kenil,ks)) ->
 get O curtid=Some(oscurt t) ->
 (forall b,fresh M b ->
  ProgSim(pc,(po,pi,ip))
   (set T t(curs(body),
    (kenil,kcall f(body)caller ks)))
   (ge,set les t(set emp saved(b,Tint32):env),allocb M b 0%Z 4,ir,aus)ph Th O cst t) ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs
 f saved body ks ph Th O Bind Local Aux Code Cur Post.
 assert (Merged:(pumerge po pi)f=Some((Tvoid,dnil,dcons saved Tint32 dnil,body))).
 { unfold pumerge;rewrite Bind;reflexivity. }
 eapply V293_os_family_progsim with(le:=caller)(si:=si)(cs:=cs)
    (C:=(curs(sfexec f nil nil),(kenil,ks)));try eassumption.
   + exists(curs(sfexec f nil nil));exists kenil;exists ks;split;[reflexivity| ].
     left;exists f;exists (nil:vallist);exists((Tvoid,dnil,dcons saved Tint32 dnil,body));exists (nil:typelist).
     split;[reflexivity|exact Merged].
   + do 2 eexists;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dnil)(d2:=dcons saved Tint32 dnil);
     [reflexivity|reflexivity|exact Merged|exact I|reflexivity].
   + intros C2 g2 l2 M2 Step2.
     destruct(V293_saved_exec_successor (pumerge po pi) f saved body ks ge caller M C2 (g2,l2,M2) Merged Step2)as[A B].
     inversion B;subst g2 l2 M2;subst C2;clear B;repeat rewrite <-set_set_eq.
     eapply V293_os_family_progsim with(le:=(emp:env))(si:=si)(cs:=cs)
      (C:=(curs(salloc nil(dcons saved Tint32 dnil)),
        (kenil,kcall f(body)caller ks)));try eassumption.
     * apply map_get_set.
     * apply map_get_set.
     * eapply V293_bound_call_inos;exact Bind.
     * destruct(memory_has_fresh_block M)as[b F];do 2 eexists;apply V293_saved_alloc_step;exact F.
     * intros C3 g3 l3 M3 Step3.
       destruct(V293_saved_alloc_successor _ _ _ _ _ _ _ Step3)as(b&F&A&B).
       inversion B;subst g3 l3 M3;subst C3;clear B;repeat rewrite <-set_set_eq.
       eapply V293_os_family_progsim with(le:=(set emp saved(b,Tint32):env))(si:=si)(cs:=cs)
        (C:=(curs(salloc nil dnil),
          (kenil,kcall f(body)caller ks)));try eassumption.
       -- apply map_get_set.
       -- apply map_get_set.
       -- eapply V293_bound_call_inos;exact Bind.
       -- do 2 eexists;eapply stmt_step;[reflexivity|apply sallocend_step].
       -- intros C4 g4 l4 M4 Step4.
          destruct(V293_alloc_end_successor _ _ _ _ _ _ _ _ Step4)as[A B].
          inversion B;subst g4 l4 M4;subst C4;clear B.
          repeat rewrite <-set_set_eq;apply Post;exact F.
Qed.

Theorem V293_saved_call_entry_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs
 f saved body ks entry ph Th O,
 po f=Some((Tvoid,dnil,dcons saved Tint32 dnil,body)) ->
 get les t=Some caller -> get aus t=Some((false,si,cs):localst) ->
 get T t=Some(curs entry,(kenil,ks)) ->
 (entry=sfexec f nil nil \/ (entry=scall f nil /\ InOS(SKIP,(kenil,ks))(pumerge po pi))) ->
 get O curtid=Some(oscurt t) ->
 (forall b,fresh M b ->
  ProgSim(pc,(po,pi,ip))
   (set T t(curs(body),
    (kenil,kcall f(body)caller ks)))
   (ge,set les t(set emp saved(b,Tint32):env),allocb M b 0%Z 4,ir,aus)ph Th O cst t) ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs
 f saved body ks entry ph Th O Bind Local Aux Code Mode Cur Post.
 destruct Mode as[Exec | [Call Inside]];subst entry.
 - eapply V293_saved_exec_entry_progsim;try eassumption.
 - assert(Same:set les t caller=les).
   { change(CltEnvMod.set les t caller=les);apply CltEnvMod.get_set_same;exact Local. }
   eapply V293_os_family_progsim with(le:=caller)(si:=si)(cs:=cs)
    (C:=(curs(scall f nil),(kenil,ks)));try eassumption.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + do 2 eexists;eapply stmt_step;[reflexivity|apply snpcall_step].
   + intros C1 g1 l1 M1 Step1.
     destruct(V293_call_nil_successor _ _ _ _ _ _ Step1)as[A B];inversion B;subst g1 l1 M1;subst C1;clear B.
     change(ProgSim(pc,(po,pi,ip))(set T t(curs(sfexec f nil nil),(kenil,ks)))
       (ge,set les t caller,M,ir,aus)ph Th O cst t).
     rewrite Same;eapply V293_saved_exec_entry_progsim;try eassumption.
     * apply map_get_set.
     * intros b Fresh;rewrite <-set_set_eq;apply Post;exact Fresh.
Qed.

Lemma V293_assign_word_progsim :
 forall pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,ks))(pumerge po pi) ->get O curtid=Some(oscurt t) ->
 evaltype e1(ge,le,M)=Some Tint32 ->
 evaladdr e1(ge,le,M)=Some(Vptr(b,Int.zero)) ->
 evaltype e2(ge,le,M)=Some Tint32 ->evalval e2(ge,le,M)=Some v ->
 store Tint32 M(b,0%Z)v=Some M' ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))(ge,les,M',ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))(set T t(curs(sassign e1 e2),(kenil,ks)))(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ks ge le les M M' ir aus si cs e1 e2 b v ph Th O
 Local Aux Inside Cur Left Address Right Value Store Post.
 eapply V293_exit_pure_progsim with(ks:=ks)
 (C':=(cure e2,(kenil,kassignr e1 Tint32 ks)))(le:=le);try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity| ];eapply sassign_step;try eassumption;apply eq_int;auto.
 - eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
   (c':=curs(sskip(Some v)))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
   + apply evalval_imply_estepstar;exact Value.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + eapply V293_exit_pure_progsim with(ks:=ks)
     (C':=(cure(eaddrof e1),(kenil,kassignl v Tint32 ks)))(le:=le);try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sassignrv_step].
     * eapply V293_exit_expr_progsim with(m:=(ge,le,M))(m':=(ge,le,M))
       (c':=curs(sskip(Some(Vptr(b,Int.zero)))))(ke':=kenil)(le:=le);try eassumption;try reflexivity.
       -- apply evaladdr_imply_estepstar;exact Address.
       -- eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
       -- eapply V293_os_silent_progsim with
          (C:=(curs(sskip(Some(Vptr(b,Int.zero)))),(kenil,kassignl v Tint32 ks)))
          (C':=(SKIP,(kenil,ks)))(le:=le)(M':=M');try eassumption.
          ++ apply map_get_set.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ eapply stmt_step;[reflexivity| ];eapply sassignend_step;try reflexivity;exact Store.
          ++ intros Cf mf Other;eapply V293_store_cstep_unique;[exact Store|exact Other].
          ++ rewrite tasks_set_a_set_a;exact Post.
Qed.

(* Freeing saved and updating another byte commute in the physical heap. *)
Lemma V293_saved_free_write_byte : forall count M Mf bs i bn n,
 freeb M bs i count=Some Mf ->bn<>bs ->
 freeb(V293_write_byte M bn n)bs i count=Some(V293_write_byte Mf bn n).
Proof.
 induction count as [ | count IH];intros M Mf bs i bn n Free Apart.
 - cbn[freeb]in *;inversion Free;reflexivity.
 - cbn[freeb] in Free |- *.
   rewrite V293_write_byte_other by congruence.
   destruct(get M(bs,i))as[[permission raw] | ]eqn:E;try discriminate.
   destruct permission;try discriminate.
   destruct(freeb M bs(i+1)%Z count)as[Mt | ]eqn:Tail;try discriminate.
   inversion Free;subst Mf;rewrite(IH _ _ _ _ _ _ Tail Apart).
   change((match get M(bs,i) with
    |Some(true,_)=>Some(del(V293_write_byte Mt bn n)(bs,i)) | _=>None end)=
    Some(V293_write_byte(del Mt(bs,i))bn n)).
   rewrite E;f_equal;apply HalfPermMap.extensionality;intro a.
   change((if HalfPermMap.dec_A a(bs,i) then None else
     if HalfPermMap.dec_A a(bn,0%Z) then
       Some(true,Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))) else HalfPermMap.get Mt a)=
     (if HalfPermMap.dec_A a(bn,0%Z) then
       Some(true,Byte(Byte.repr(Int.unsigned(Int.repr(Z.of_nat n))))) else
       if HalfPermMap.dec_A a(bs,i) then None else HalfPermMap.get Mt a)).
   destruct(HalfPermMap.dec_A a(bs,i))as[Eq|Ne];
   destruct(HalfPermMap.dec_A a(bn,0%Z))as[Eq2|Ne2];try reflexivity;congruence.
Qed.

Lemma V293_saved_free_decrement : forall M Mf bs bn n,
 free Tint32 bs M=Some Mf ->bn<>bs ->
 free Tint32 bs(V293_exit_decrement_memory M bn n)=
 Some(V293_exit_decrement_memory Mf bn n).
Proof.
 intros M Mf bs bn n Free Apart;unfold V293_exit_decrement_memory.
 destruct(Nat.eqb n 0);[exact Free|apply V293_saved_free_write_byte;assumption].
Qed.

Lemma V293_decrement_block_frame : forall M M' bn n c,
 (forall i,get M'(c,i)=get M(c,i)) ->
 forall i,get(V293_exit_decrement_memory M' bn n)(c,i)=
 get(V293_exit_decrement_memory M bn n)(c,i).
Proof.
 intros M M' bn n c Frame i;unfold V293_exit_decrement_memory.
 destruct(Nat.eqb n 0);[apply Frame| ].
 unfold V293_write_byte;destruct(HalfPermMap.dec_A(bn,0%Z)(c,i))as[Eq|Ne].
 - inversion Eq;subst;repeat rewrite map_get_set;reflexivity.
 - repeat rewrite map_get_set' by congruence;apply Frame.
Qed.

(* This proof starts at the complete body, including saved initialization
   and running guard. It uses no simulation assumption inside the body. *)
Theorem V293_exit_body_progsim :
 forall pc po pi ip T cst t ge le caller les M Mz Mf ir aus si cs f ks bs
 running nesting lock saved table high target current counter sched handoff bn n locked
 (take:bool) ph Th O,
 get les t=Some le ->get aus t=Some((false,si,cs):localst) ->
 InOS(SKIP,(kenil,kcall f
 (V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff)caller ks))
 (pumerge po pi) ->get O curtid=Some(oscurt t) ->
 get le saved=Some(bs,Tint32) ->getaddr le=((bs,Tint32)::nil) ->
 store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz ->
 evalval(V293_OSIntEnter_running running)(ge,le,Mz)=
 Some(Vint32(if take then Int.one else Int.zero)) ->
 free Tint32 bs(if take then V293_exit_decrement_memory Mz bn n else Mz)=Some Mf ->
 (take=true ->n<256 /\ locked<256 /\get le nesting=None /\get ge nesting=Some(bn,Tint8) /\
 load Tint8 Mz(bn,0%Z)=Some(V293_byteval n) /\
 (0<n ->exists raw,get Mz(bn,0%Z)=Some(true,raw)) /\
 (Nat.pred n=0 ->get le lock=None /\ exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory Mz bn n)(bl,0%Z)=Some(V293_byteval locked)) /\
 (2<=n \/0<locked)) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,set les t caller,Mf,ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))
 (set T t(curs(V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff),
 (kenil,kcall f(V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff)caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge le caller les M Mz Mf ir aus si cs f ks bs
 running nesting lock saved table high target current counter sched handoff bn n locked
 take ph Th O Local Aux Inside Cur Saved Layout Store Guard Free Quiet Post.
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff).
 set(critical:=sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock
 (V293_exit_boundary_dispatch table high target current counter sched handoff))(sprim excrit))).
 change(ProgSim(pc,(po,pi,ip))(set T t(curs(sseq(sassign(evar saved)(econst32 Int.zero))
 (sseq(sifthen(V293_OSIntEnter_running running)critical)sret)),(kenil,kcall f body caller ks)))
 (ge,les,M,ir,aus)ph Th O cst t).
 eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
 (C':=(curs(sassign(evar saved)(econst32 Int.zero)),
 (kenil,kseq(sseq(sifthen(V293_OSIntEnter_running running)critical)sret)(kcall f body caller ks))));
 try eassumption;try reflexivity.
 - eapply stmt_step;[reflexivity|apply sseq_step].
 - eapply V293_assign_word_progsim with(le:=le)(b:=bs)(v:=Vint32 Int.zero)(M':=Mz);
   try eassumption;try reflexivity.
   + eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
   + cbn[evaltype get_lenv];rewrite Saved;reflexivity.
   + cbn[evaladdr get_lenv];rewrite Saved;reflexivity.
   + eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
     (C':=(curs(sseq(sifthen(V293_OSIntEnter_running running)critical)sret),(kenil,kcall f body caller ks)));
     try eassumption;try reflexivity.
     * eapply stmt_step;[reflexivity|apply sskip_step].
     * eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
       (C':=(curs(sifthen(V293_OSIntEnter_running running)critical),(kenil,kseq sret(kcall f body caller ks))));
       try eassumption;try reflexivity.
       -- eapply stmt_step;[reflexivity|apply sseq_step].
       -- eapply V293_exit_ifthen_progsim with(le:=le)
          (v:=Vint32(if take then Int.one else Int.zero))(take:=take);try eassumption.
          ++ eapply V293_context_inos;[exact Inside|reflexivity|reflexivity].
          ++ destruct take;reflexivity.
          ++ destruct take.
             ** destruct(Quiet eq_refl)as[B[L[N[G[R[W[K D]]]]]]].
                unfold critical;eapply V293_exit_quiet_return_progsim with(le:=le)
                (bs:=bs)(bn:=bn)(n:=n)(locked:=locked);try eassumption.
             ** eapply V293_exit_pure_progsim with(le:=le)(ks:=kcall f body caller ks)
                (C':=(curs sret,(kenil,kcall f body caller ks)));try eassumption;try reflexivity.
                --- eapply stmt_step;[reflexivity|apply sskip_step].
                --- eapply V293_one_local_return_progsim with(le:=le)(b:=bs)(tp:=Tint32);try eassumption.
Qed.

(* Stable complete-call interface: final heap is independent of allocation.
   The running-false path imposes no nesting/lock read obligation. *)
Theorem V293_exit_quiet_call_progsim :
 forall pc po pi ip T cst t ge caller les M ir aus si cs f ks entry
 running nesting lock saved table high target current counter sched handoff br run bn n locked ph Th O,
 po f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched handoff) ->
 get les t=Some caller ->get aus t=Some((false,si,cs):localst) ->
 get T t=Some(curs entry,(kenil,ks)) ->
 (entry=sfexec f nil nil \/ (entry=scall f nil /\ InOS(SKIP,(kenil,ks))(pumerge po pi))) ->
 get O curtid=Some(oscurt t) ->saved<>running ->run<256 ->
 get ge running=Some(br,Tint8) ->load Tint8 M(br,0%Z)=Some(V293_byteval run) ->
 (run=1 ->saved<>nesting /\saved<>lock /\n<256 /\locked<256 /\
 get ge nesting=Some(bn,Tint8) /\load Tint8 M(bn,0%Z)=Some(V293_byteval n) /\
 (0<n ->exists raw,get M(bn,0%Z)=Some(true,raw)) /\
 (Nat.pred n=0 ->exists bl,get ge lock=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)=Some(V293_byteval locked)) /\
 (2<=n \/0<locked)) ->
 ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,ks)))
 (ge,les,(if Nat.eqb run 1 then V293_exit_decrement_memory M bn n else M),ir,aus)ph Th O cst t ->
 ProgSim(pc,(po,pi,ip))T(ge,les,M,ir,aus)ph Th O cst t.
Proof.
 intros pc po pi ip T cst t ge caller les M ir aus si cs f ks entry
 running nesting lock saved table high target current counter sched handoff br run bn n locked ph Th O
 Bind Local Aux Code Mode Cur Sr Run Gr Read Quiet Post.
 eapply V293_saved_call_entry_progsim with(saved:=saved)
 (body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched handoff);
 try eassumption.
 intros bs Fresh.
 destruct(V293_success_scheduler_storage M bs Fresh)as(Mz&Store&W&Free&Frame).
 set(le:=set emp saved(bs,Tint32):env).
 assert(Saved:get le saved=Some(bs,Tint32))by(apply map_get_set).
 assert(NotLocal:forall x,saved<>x ->get le x=None).
 { intros x Ne;unfold le;rewrite map_get_set' by congruence;apply map_emp_get. }
 assert(Layout:getaddr le=((bs,Tint32)::nil)).
 { unfold le;change(getaddr(EnvMod.set EnvMod.emp saved(bs,Tint32))=((bs,Tint32)::nil));reflexivity. }
 assert(Rb:br<>bs)by(intro Eq;exact(V293_success_load_not_fresh M bs br run Fresh Read(eq_sym Eq))).
 assert(RunRead:load Tint8 Mz(br,0%Z)=Some(V293_byteval run)).
 { transitivity(load Tint8 M(br,0%Z));[apply V293_load_block_frame;intro i;apply Frame;exact Rb|exact Read]. }
 assert(Guard:evalval(V293_OSIntEnter_running running)(ge,le,Mz)=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero))).
 { unfold V293_OSIntEnter_running;change(evalval(ebinop oeq(ecast(evar running)Tint32)(econst32(Int.repr(Z.of_nat 1))))(ge,le,Mz)=
   Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)));eapply V293_success_global_byte_eq;
   try eassumption;try lia;apply NotLocal;exact Sr. }
 assert(Restore:set(set les t le)t caller=les).
 { rewrite <-set_set_eq;change(CltEnvMod.set les t caller=les);apply CltEnvMod.get_set_same;exact Local. }
 eapply V293_exit_body_progsim with(le:=le)(Mz:=Mz)(bs:=bs)
 (bn:=bn)(n:=n)(locked:=locked)(take:=Nat.eqb run 1)
 (Mf:=if Nat.eqb run 1 then V293_exit_decrement_memory M bn n else M);
 try eassumption.
 - apply map_get_set.
 - eapply V293_bound_call_inos;exact Bind.
 - destruct(Nat.eqb run 1)eqn:E;[ | exact Free].
   apply Nat.eqb_eq in E;destruct(Quiet E)as[Sn[Sl[B[L[G[R[Write[Lock Disabled]]]]]]]].
   eapply V293_saved_free_decrement;[exact Free| ].
   intro Eq;exact(V293_success_load_not_fresh M bs bn n Fresh R(eq_sym Eq)).
 - intro E;apply Nat.eqb_eq in E.
   destruct(Quiet E)as[Sn[Sl[B[L[G[R[Write[Lock Disabled]]]]]]]].
   assert(Nb:bn<>bs)by(intro Eq;exact(V293_success_load_not_fresh M bs bn n Fresh R(eq_sym Eq))).
   repeat apply conj;try assumption;try(apply NotLocal;assumption).
   + transitivity(load Tint8 M(bn,0%Z));[apply V293_load_block_frame;intro i;apply Frame;exact Nb|exact R].
   + intro Positive;destruct(Write Positive)as[raw Full];exists raw;rewrite Frame by exact Nb;exact Full.
   + intro Zero;split;[apply NotLocal;exact Sl| ].
     destruct(Lock Zero)as[bl[Glock Rlock]];exists bl;split;[exact Glock| ].
     assert(Lb:bl<>bs).
     { apply not_eq_sym;eapply V293_success_load_not_fresh with(M:=V293_exit_decrement_memory M bn n)(n:=locked);
       [ | exact Rlock].
       unfold V293_exit_decrement_memory;destruct(Nat.eqb n 0);[exact Fresh| ].
       intros l j Eq;subst l;intros[v Present].
       change(get(V293_write_byte M bn(Nat.pred n))(bs,j)=Some v)in Present.
       rewrite V293_write_byte_other in Present by congruence.
       apply(Fresh(bs,j)j eq_refl);exists v;exact Present. }
     transitivity(load Tint8(V293_exit_decrement_memory M bn n)(bl,0%Z)).
     * apply V293_load_block_frame;apply V293_decrement_block_frame;intro i;apply Frame;exact Lb.
     * exact Rlock.
 - rewrite Restore;exact Post.
Qed.
