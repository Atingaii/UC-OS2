(* Actual client preparation, actual OS entry, and complete global return.
   Client and OS memories are independent; no artificial outer frame is added. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyGlobalCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeDlyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPIRefinement.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceReadyCall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPILifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_time_get_client_global : forall pc po pi ip T les aus t ge caller M ir aux
    cge cles CM cle f,
  get cles t=Some cle ->
  V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
    (V293_local_global_at T les aus t(curs(scall f []),(kenil,kstop))((ge,caller,M),ir,aux))
    (V293_local_global_at T les aus t(curs(sfexec f [] []),(kenil,kstop))((ge,caller,M),ir,aux)).
Proof.
  intros. eapply V293_client_unchanged_global;[exact H | | ].
  - eapply stmt_step;[reflexivity | apply snpcall_step].
  - apply V293_client_no_os_context;try reflexivity;intros;discriminate.
Qed.

(* This rejection is at the client boundary, not a test of the callee body. *)
Theorem V293_time_missing_client_binding : forall pc po pi ip t f args cge cles CM tst C' cst' tst',
  get cles t=None ->
  ~ ltstep(pc,(po,pi,ip))t(curs(scall f args),(kenil,kstop))(cge,cles,CM)tst C' cst' tst'.
Proof.
  intros pc po pi ip t f args cge cles CM tst C' cst' tst' Missing Step.
  assert(Outside:forall P,~InOS(curs(scall f args),(kenil,kstop))P).
  { intro P;apply V293_client_no_os_context;try reflexivity;intros;discriminate. }
  inversion Step;subst;[congruence | eapply Outside;eassumption].
Qed.

Lemma V293_time_global_return : forall pc po pi ip T les aus t cst ge le caller M Mf ir aux
    f body tau d1 d2 result,
  po f=Some(tau,d1,d2,body) -> freels(getaddr le)M Mf ->
  V293_global_steps(pc,(po,pi,ip))cst
    (V293_local_global_at T les aus t(V293_time_return_start result(kcall f body caller kstop))
      ((ge,le,M),ir,aux))
    (V293_local_global_at T les aus t(curs(sskip result),(kenil,kstop))((ge,caller,Mf),ir,aux)).
Proof.
  intros pc po pi ip T les aus t cst ge le caller M Mf ir aux f body tau d1 d2 result Bind Freed.
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(sfree(getaddr le)result),(kenil,kcall f body caller kstop))((ge,le,M),ir,aux)).
  { apply V293_loststep_global_single.
    - destruct result as[v | ];unfold V293_time_return_start,InOS;
        do 3 eexists;split;try reflexivity;
        right;left;exists f;exists caller;exists kstop;exists tau;exists d1;exists d2;exists body;exists body;
        split;try reflexivity;unfold pumerge;rewrite Bind;reflexivity.
    - destruct result as[v | ];unfold V293_time_return_start.
      + apply ostc_step;eapply stmt_step;[reflexivity | ].
        eapply(sretv_step(pumerge po pi)f _ body);[reflexivity | cbn;discriminate | reflexivity].
      + apply ostc_step;eapply stmt_step;[reflexivity | ];eapply sret_step;reflexivity. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(sfree nil result),(kenil,kcall f body caller kstop))((ge,le,Mf),ir,aux)).
  { pose proof(V293_time_freels_value _ (pumerge po pi)kstop ge le M Mf result Freed)as Free.
    eapply(V293_csteps_global pc po pi ip _ _ _ _ Free f body caller kstop tau d1 d2
      T les t ir (set aus t aux) aux cst Bind(map_get_set _ _ _)).
    change(goodks(pc,(po,pi,ip))(kcall f body caller kstop)).
    cbn[goodks];unfold pumerge;rewrite Bind;exact I. }
  apply V293_loststep_global_single.
  - eapply V293_bound_call_inos;exact Bind.
  - apply ostc_step;eapply stmt_step;[reflexivity | eapply sfreeend_step;reflexivity].
Qed.

Lemma V293_time_global_copy : forall pc po pi ip T les aus t cst ge le caller M ir enabled si ci O op
    f tau d1 d2 saved bs dl dst bd old sl src bc n tail R,
  po f=Some(tau,d1,d2,sseq(sassign(evar saved)(econst32 Int.zero))
    (sseq(sseq(sprim encrit)(sseq(sassign(evar dst)(evar src))(sprim excrit)))tail)) ->
  get le saved=Some(bs,Tint32) ->
  (ge,le,M,ir,(enabled,si,ci),O,op) |= V293_time_cell true saved bs Vundef **
    (V293_time_cell dl dst bd old ** (V293_time_cell sl src bc(Vint32 n) ** R)) ->
  let body:=sseq(sassign(evar saved)(econst32 Int.zero))
    (sseq(sseq(sprim encrit)(sseq(sassign(evar dst)(evar src))(sprim excrit)))tail) in
  exists Mz Mc,
    store Tint32 M(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
    store Tint32 Mz(bd,0%Z)(Vint32 n)=Some Mc /\
    V293_global_steps(pc,(po,pi,ip))cst
      (V293_local_global_at T les aus t(curs body,(kenil,kcall f body caller kstop))
        ((ge,le,M),ir,(enabled,si,ci)))
      (V293_local_global_at T les aus t(curs tail,(kenil,kcall f body caller kstop))
        ((ge,le,Mc),ir,(enabled,si,ci))) /\
    (ge,le,Mc,ir,(enabled,si,ci),O,op) |= V293_time_cell true saved bs(Vint32 Int.zero) **
      (V293_time_cell dl dst bd(Vint32 n) ** (V293_time_cell sl src bc(Vint32 n) ** R)).
Proof.
  intros pc po pi ip T les aus t cst ge le caller M ir enabled si ci O op f tau d1 d2
    saved bs dl dst bd old sl src bc n tail R Bind Saved Owned body.
  destruct(V293_time_body_prefix(pumerge po pi)kstop ge le M ir enabled si ci O op
    saved bs dl dst bd old sl src bc n tail R Saved Owned)as(Mz&Mc&Zero&Copy&Trace&Post).
  exists Mz;exists Mc;split;[exact Zero | ];split;[exact Copy | ];split;[ | exact Post].
  eapply(V293_local_steps_global pc po pi ip _ _ _ _ Trace f body caller kstop tau d1 d2
    T les aus t cst Bind).
  change(goodks(pc,(po,pi,ip))(kcall f body caller kstop)).
  cbn[goodks];unfold pumerge;rewrite Bind;exact I.
Qed.
(* Entry is rebuilt in the original global semantics: only the client prefix
   uses CM; sfexec and each allocation operate on the independent OS heap. *)
Lemma V293_time_get_global_entry : forall pc po pi ip T les aus t cge cles CM cle
    ge caller M ir aux O op f now ticks saved bt bs R,
  get cles t=Some cle -> po f=Some(V293_TimeGet_function now ticks saved) ->
  ticks<>saved -> fresh M bt -> fresh(allocb M bt 0%Z 4)bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op)|=R ->
  let Ma:=allocb(allocb M bt 0%Z 4)bs 0%Z 4 in
  V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
    (V293_local_global_at T les aus t(curs(scall f []),(kenil,kstop))((ge,caller,M),ir,aux))
    (V293_local_global_at T les aus t(curs(V293_TimeGet_body now ticks saved),
      (kenil,kcall f(V293_TimeGet_body now ticks saved)caller kstop))
      ((ge,V293_time_call_locals ticks saved bt bs,Ma),ir,aux)) /\
  (ge,V293_time_call_locals ticks saved bt bs,Ma,ir,aux,O,op)|=
    Amapsto(bs,0%Z)Tint32 true Vundef ** (Amapsto(bt,0%Z)Tint32 true Vundef ** R).
Proof.
  intros pc po pi ip T les aus t cge cles CM cle ge caller M ir aux O op
    f now ticks saved bt bs R Get Bind TS FT FS Held Ma.
  assert(Program:pumerge po pi f=Some(V293_TimeGet_function now ticks saved)).
  { unfold pumerge;rewrite Bind;reflexivity. }
  destruct(V293_time_get_call_entry(pumerge po pi)kstop ge caller M ir aux O op f
    now ticks saved bt bs R Program TS FT FS Held)as[Local Owned].
  split;[ | exact Owned].
  eapply V293_global_trans;[eapply V293_time_get_client_global;exact Get | ].
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc nil(dcons ticks Tint32(dcons saved Tint32 dnil))),
      (kenil,kcall f(V293_TimeGet_body now ticks saved)caller kstop))((ge,emp,M),ir,aux)).
  { apply V293_loststep_global_single.
    - exists(curs(sfexec f [] []));exists kenil;exists kstop;split;[reflexivity | left].
      exists f;exists(@nil val);exists(V293_TimeGet_function now ticks saved);exists(@nil type).
      split;[reflexivity | exact Program].
    - apply ostc_step;eapply stmt_step;[reflexivity | ].
      eapply sfexec_step with(d1:=dnil)(d2:=dcons ticks Tint32(dcons saved Tint32 dnil));
        [reflexivity | reflexivity | exact Program | exact I | reflexivity]. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc nil(dcons saved Tint32 dnil)),
      (kenil,kcall f(V293_TimeGet_body now ticks saved)caller kstop))
      ((ge,set emp ticks(bt,Tint32),allocb M bt 0%Z 4),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step;eapply stmt_step;[reflexivity | ];eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bt;repeat split;try assumption;try reflexivity.
      intros[v E];rewrite map_emp_get in E;discriminate. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc nil dnil),(kenil,kcall f(V293_TimeGet_body now ticks saved)caller kstop))
      ((ge,V293_time_call_locals ticks saved bt bs,Ma),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step;eapply stmt_step;[reflexivity | ];eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bs;repeat split;try assumption;try reflexivity.
      intros[v E];rewrite map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
  apply V293_loststep_global_single.
  - eapply V293_bound_call_inos;exact Bind.
  - apply ostc_step;eapply stmt_step;[reflexivity | apply sallocend_step].
Qed.

Lemma V293_time_set_global_entry : forall pc po pi ip T les aus t cge cles CM cle
    ge caller M ir aux O op f now ticks saved bt bs n R,
  get cles t=Some cle -> po f=Some(V293_TimeSet_function now ticks saved) ->
  ticks<>saved -> fresh M bt -> fresh M bs -> bt<>bs ->
  (ge,V293_time_call_locals ticks saved bt bs,M,ir,aux,O,op)|=R ->
  exists Mp Ma,
    store Tint32(allocb M bt 0%Z 4)(bt,0%Z)(Vint32 n)=Some Mp /\
    Ma=allocb Mp bs 0%Z 4 /\
    V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
      (V293_local_global_at T les aus t(curs(scall f[econst32 n]),(kenil,kstop))((ge,caller,M),ir,aux))
      (V293_local_global_at T les aus t(curs(V293_TimeSet_body now ticks saved),
        (kenil,kcall f(V293_TimeSet_body now ticks saved)caller kstop))
        ((ge,V293_time_call_locals ticks saved bt bs,Ma),ir,aux)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Ma,ir,aux,O,op)|=
      Amapsto(bs,0%Z)Tint32 true Vundef ** (Amapsto(bt,0%Z)Tint32 true(Vint32 n) ** R).
Proof.
  intros pc po pi ip T les aus t cge cles CM cle ge caller M ir aux O op
    f now ticks saved bt bs n R Get Bind TS FT FS Blocks Held.
  assert(Program:pumerge po pi f=Some(V293_TimeSet_function now ticks saved)).
  { unfold pumerge;rewrite Bind;reflexivity. }
  destruct(V293_time_set_call_entry(pumerge po pi)kstop ge caller M ir aux O op f
    now ticks saved bt bs n R Program TS FT FS Blocks Held)
    as(Mp&Ma&Store&Memory&Local&Owned).
  assert(FS':fresh Mp bs).
  { eapply V293_time_fresh_after_store;[exact Blocks | | exact Store].
    apply V293_time_fresh_after_alloc;assumption. }
  exists Mp;exists Ma;split;[exact Store | ];split;[exact Memory | ];split;[ | exact Owned].
  eapply V293_global_trans;[eapply V293_constant_call_global;exact Get | ].
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc (cons (Vint32 n) nil)(dcons ticks Tint32(dcons saved Tint32 dnil))),
      (kenil,kcall f(V293_TimeSet_body now ticks saved)caller kstop))((ge,emp,M),ir,aux)).
  { apply V293_loststep_global_single.
    - exists(curs(sfexec f[Vint32 n][Tint32]));exists kenil;exists kstop;split;[reflexivity | left].
      exists f;exists[Vint32 n];exists(V293_TimeSet_function now ticks saved);exists[Tint32].
      split;[reflexivity | exact Program].
    - apply ostc_step;eapply stmt_step;[reflexivity | ].
      eapply sfexec_step with(d1:=dcons ticks Tint32 dnil)(d2:=dcons saved Tint32 dnil);
        [reflexivity | reflexivity | exact Program | split;[exact I | reflexivity] | reflexivity]. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc nil(dcons saved Tint32 dnil)),
      (kenil,kcall f(V293_TimeSet_body now ticks saved)caller kstop))
      ((ge,set emp ticks(bt,Tint32),Mp),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step;eapply stmt_step;[reflexivity | ];eapply sallocp_step with(b:=bt);
        [reflexivity | reflexivity | | apply map_get_set | exact Store].
      exists bt;repeat split;try assumption;try reflexivity.
      intros[v E];rewrite map_emp_get in E;discriminate. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (curs(salloc nil dnil),(kenil,kcall f(V293_TimeSet_body now ticks saved)caller kstop))
      ((ge,V293_time_call_locals ticks saved bt bs,Ma),ir,aux)).
  { apply V293_loststep_global_single.
    - eapply V293_bound_call_inos;exact Bind.
    - apply ostc_step;eapply stmt_step;[reflexivity | ];eapply salloclv_step;
        [reflexivity | reflexivity | ]. exists bs;repeat split;try assumption;try reflexivity.
      intros[v E];rewrite map_get_set' in E by congruence;rewrite map_emp_get in E;discriminate. }
  apply V293_loststep_global_single.
  - eapply V293_bound_call_inos;exact Bind.
  - apply ostc_step;eapply stmt_step;[reflexivity | apply sallocend_step].
Qed.
Lemma V293_time_get_global_tail : forall pc po pi ip T les aus t cst ge le caller M Mf ir aux
    O op f now ticks saved bt clock,
  po f=Some(V293_TimeGet_function now ticks saved) ->
  (ge,le,M,ir,aux,O,op)|=V293_time_cell true ticks bt(Vint32 clock) ** Atrue ->
  freels(getaddr le)M Mf ->
  V293_global_steps(pc,(po,pi,ip))cst
    (V293_local_global_at T les aus t(curs(srete(evar ticks)),
      (kenil,kcall f(V293_TimeGet_body now ticks saved)caller kstop))((ge,le,M),ir,aux))
    (V293_local_global_at T les aus t(curs(sskip(Some(Vint32 clock))),(kenil,kstop))
      ((ge,caller,Mf),ir,aux)).
Proof.
  intros pc po pi ip T les aus t cst ge le caller M Mf ir aux O op
    f now ticks saved bt clock Bind Read Freed.
  destruct(V293_time_cell_read true ticks bt clock Atrue _ Read)as[Value Typed].
  assert(Expr:cstepstar(pumerge po pi)(curs(srete(evar ticks)),(kenil,kstop))(ge,le,M)
    (curs(sskip(Some(Vint32 clock))),(kenil,kret kstop))(ge,le,M)).
  { eapply c_stepstarn;[eapply stmt_step;[reflexivity | apply srete_step] | ].
    apply V293_expr_steps;apply evalval_imply_estepstar;exact Value. }
  eapply V293_global_trans with(b:=V293_local_global_at T les aus t
    (V293_time_return_start(Some(Vint32 clock))(kcall f(V293_TimeGet_body now ticks saved)caller kstop))
      ((ge,le,M),ir,aux)).
  - eapply(V293_csteps_global pc po pi ip _ _ _ _ Expr f(V293_TimeGet_body now ticks saved)
      caller kstop Tint32 dnil(dcons ticks Tint32(dcons saved Tint32 dnil))
      T les t ir(set aus t aux)aux cst Bind(map_get_set _ _ _)).
    change(goodks(pc,(po,pi,ip))(kcall f(V293_TimeGet_body now ticks saved)caller kstop)).
    cbn[goodks];unfold pumerge;rewrite Bind;exact I.
  - eapply V293_time_global_return;[exact Bind | exact Freed].
Qed.

(* Stable generated getter interface: a complete continuous global call,
   with exact heap identity at linearization and at the final free/return. *)
Theorem V293_source_time_get_global : forall br bg bp bn t pc po pi ip T les aus
    cge cles CM cle sd ge caller M ir enabled si ci O f now ticks saved bt bs clock,
  get cles t=Some cle -> po f=Some(V293_source_OSTimeGet_function now ticks saved) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M bt -> fresh M bs -> bt<>bs -> get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,(enabled,si,ci),O,V293_time_get_action)|=
    V293_time_ready_core br bg bp bn ** CurTid t ->
  exists Mc Mf,
    V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
      (V293_local_global_at T les aus t(curs(scall f []),(kenil,kstop))((ge,caller,M),ir,(enabled,si,ci)))
      (V293_local_global_at T les aus t(curs(sskip(Some(Vint32 clock))),(kenil,kstop))
        ((ge,caller,Mf),ir,(enabled,si,ci))) /\
    spec_step sd V293_time_get_action O(END(Some(Vint32 clock)))O /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),O,
      END(Some(Vint32 clock)))|=V293_time_ready_core br bg bp bn ** Atrue /\
    (ge,caller,Mf,ir,(enabled,si,ci),O,END(Some(Vint32 clock)))|=
      V293_time_ready_core br bg bp bn ** CurTid t /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp bn t pc po pi ip T les aus cge cles CM cle sd ge caller M ir
    enabled si ci O f now ticks saved bt bs clock Get Bind TS NT NS Global FT FS Blocks Slot Held.
  rewrite V293_source_time_get_exact in Bind.
  pose proof(V293_source_time_entry_core br bg bp bn t ge caller
    (V293_time_call_locals ticks saved bt bs)M ir(enabled,si,ci)O V293_time_get_action
    ir(enabled,si,ci)V293_time_get_action Held)as Callee.
  destruct(V293_time_get_global_entry pc po pi ip T les aus t cge cles CM cle ge caller M
    ir(enabled,si,ci)O V293_time_get_action f now ticks saved bt bs
    (V293_time_ready_core br bg bp bn ** CurTid t)Get Bind TS FT
    (V293_time_fresh_after_alloc M bt bs Blocks FS)Callee)as[Entry Owned].
  pose proof(V293_source_time_name_owned br bg bp bn t ge _ ir(enabled,si,ci)O V293_time_get_action
    now ticks saved bt bs clock Vundef TS NT NS Global Slot Owned)as Named.
  destruct(V293_source_time_current_good t)as[Good Free].
  destruct(V293_time_get_body_refinement br bg bp(pumerge po pi)sd kstop ge caller _ ir
    enabled si ci O now ticks saved bn bt bs clock Vundef(CurTid t)f TS Good Free Named)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  destruct(V293_time_global_copy pc po pi ip T les aus t(cge,cles,CM)ge _ caller _ ir
    enabled si ci O V293_time_get_action f Tint32 dnil(dcons ticks Tint32(dcons saved Tint32 dnil))
    saved bs true ticks bt Vundef false now bn clock(srete(evar ticks))
    (V293_time_ready_fields br bg bp clock ** CurTid t)Bind(map_get_set _ _ _)Named)
    as(Mz'&Mc'&Zero'&Copy'&Body&Post).
  rewrite Zero in Zero';inversion Zero';subst Mz'.
  rewrite Copy in Copy';inversion Copy';subst Mc'.
  exists Mc;exists Mf;split.
  - eapply V293_global_trans;[exact Entry | ];eapply V293_global_trans;[exact Body | ].
    eapply V293_time_get_global_tail with(bt:=bt)(O:=O)(op:=V293_time_get_action);[exact Bind | | exact Freed].
    clear -Post;sep auto.
  - split;[exact Step | ];split;[exact Closed | ];split;assumption.
Qed.

Theorem V293_source_time_set_global : forall br bg bp bn t pc po pi ip T les aus
    cge cles CM cle sd ge caller M ir enabled si ci O f now ticks saved bt bs clock n,
  get cles t=Some cle -> po f=Some(V293_source_OSTimeSet_function now ticks saved) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M bt -> fresh M bs -> bt<>bs -> get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,(enabled,si,ci),O,V293_time_set_action n)|=
    V293_time_ready_core br bg bp bn ** CurTid t ->
  exists Mc Mf,
    V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)
      (V293_local_global_at T les aus t(curs(scall f[econst32 n]),(kenil,kstop))((ge,caller,M),ir,(enabled,si,ci)))
      (V293_local_global_at T les aus t(curs(sskip None),(kenil,kstop))((ge,caller,Mf),ir,(enabled,si,ci))) /\
    spec_step sd(V293_time_set_action n)O(END None)(set O ostmid(ostm n)) /\
    (ge,V293_time_call_locals ticks saved bt bs,Mc,ir,(false,si,enabled::ci),set O ostmid(ostm n),
      END None)|=V293_time_ready_core br bg bp bn ** Atrue /\
    (ge,caller,Mf,ir,(enabled,si,ci),set O ostmid(ostm n),END None)|=
      V293_time_ready_core br bg bp bn ** CurTid t /\
    freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf.
Proof.
  intros br bg bp bn t pc po pi ip T les aus cge cles CM cle sd ge caller M ir
    enabled si ci O f now ticks saved bt bs clock n Get Bind TS NT NS Global FT FS Blocks Slot Held.
  rewrite V293_source_time_set_exact in Bind.
  pose proof(V293_source_time_entry_core br bg bp bn t ge caller
    (V293_time_call_locals ticks saved bt bs)M ir(enabled,si,ci)O(V293_time_set_action n)
    ir(enabled,si,ci)(V293_time_set_action n)Held)as Callee.
  destruct(V293_time_set_global_entry pc po pi ip T les aus t cge cles CM cle ge caller M
    ir(enabled,si,ci)O(V293_time_set_action n)f now ticks saved bt bs n
    (V293_time_ready_core br bg bp bn ** CurTid t)Get Bind TS FT FS Blocks Callee)
    as(Mp&Ma&ParameterStore&Memory&Entry&Owned).
  pose proof(V293_source_time_name_owned br bg bp bn t ge Ma ir(enabled,si,ci)O(V293_time_set_action n)
    now ticks saved bt bs clock(Vint32 n)TS NT NS Global Slot Owned)as Named.
  assert(Reorder:(ge,V293_time_call_locals ticks saved bt bs,Ma,ir,(enabled,si,ci),O,V293_time_set_action n)|=
    V293_time_cell true saved bs Vundef ** (V293_time_cell false now bn(Vint32 clock) **
      (V293_time_cell true ticks bt(Vint32 n) ** (V293_time_ready_fields br bg bp clock ** CurTid t)))).
  { clear -Named;sep auto. }
  destruct(V293_source_time_current_good t)as[Good Free].
  destruct(V293_time_set_body_refinement br bg bp(pumerge po pi)sd kstop ge caller Ma ir
    enabled si ci O now ticks saved bn bt bs clock n(CurTid t)f TS Good Free Reorder)
    as(Mz&Mc&Mf&Zero&Copy&Prefix&Step&Closed&Suffix&Final&Freed).
  destruct(V293_time_global_copy pc po pi ip T les aus t(cge,cles,CM)ge _ caller Ma ir
    enabled si ci O(V293_time_set_action n)f Tvoid(dcons ticks Tint32 dnil)(dcons saved Tint32 dnil)
    saved bs false now bn(Vint32 clock)true ticks bt n sret
    (V293_time_ready_fields br bg bp clock ** CurTid t)Bind(map_get_set _ _ _)Reorder)
    as(Mz'&Mc'&Zero'&Copy'&Body&Post).
  rewrite Zero in Zero';inversion Zero';subst Mz'.
  rewrite Copy in Copy';inversion Copy';subst Mc'.
  exists Mc;exists Mf;split.
  - eapply V293_global_trans;[exact Entry | ];eapply V293_global_trans;[exact Body | ].
    exact(V293_time_global_return pc po pi ip T les aus t(cge,cles,CM)ge _ caller Mc Mf
      ir(enabled,si,ci)f(V293_TimeSet_body now ticks saved)Tvoid(dcons ticks Tint32 dnil)
      (dcons saved Tint32 dnil)None Bind Freed).
  - split;[exact Step | ];split;[exact Closed | ];split;assumption.
Qed.
(* Endpoint equality uses actual selected entries, not a synthetic task map. *)
Lemma V293_time_global_switch_then : forall pc po pi ip T les au current next ge M Ms Mf ir
    cst ks selected enabled si ci C result,
  lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
    (set T current(SKIP,(kenil,ks)))cst(ge,les,Ms,ir,au)next ->
  current<>next -> get T next=Some C -> get les next=Some selected ->
  get au next=Some(enabled,si,ci) ->
  V293_global_steps(pc,(po,pi,ip))cst
    (V293_local_global_at(set T current(SKIP,(kenil,ks)))les au next C
      ((ge,selected,Ms),ir,(enabled,si,ci)))
    (V293_local_global_at(set T current(SKIP,(kenil,ks)))les au next
      (curs(sskip result),(kenil,kstop))((ge,selected,Mf),ir,(enabled,si,ci))) ->
  V293_global_steps(pc,(po,pi,ip))cst(T,(ge,les,M,ir,au),current)
    (set(set T current(SKIP,(kenil,ks)))next(curs(sskip result),(kenil,kstop)),
      (ge,les,Mf,ir,au),next).
Proof.
  intros pc po pi ip T les au current next ge M Ms Mf ir cst ks selected enabled si ci C result
    Switch Apart Code Local Aux Call.
  cbn[V293_local_global_at V293_global_at]in Call.
  assert(Tsame:set(set T current(SKIP,(kenil,ks)))next C=set T current(SKIP,(kenil,ks))).
  { apply TasksMod.get_set_same.
    change(get(set T current(SKIP,(kenil,ks)))next=Some C).
    rewrite map_get_set' by congruence;exact Code. }
  assert(Lsame:set les next selected=les)by(apply CltEnvMod.get_set_same;exact Local).
  assert(Asame:set au next(enabled,si,ci)=au)by(apply TaskLStMod.get_set_same;exact Aux).
  rewrite Tsame,Lsame in Call.
  replace (set au next(enabled,si,ci)) with au in Call by exact(eq_sym Asame).
  unfold V293_global_steps.
  eapply rt1n_trans with(y:=(set T current(SKIP,(kenil,ks)),(ge,les,Ms,ir,au),next));
    [exact Switch | exact Call].
Qed.

Theorem V293_time_switch_global_get : forall br bg bp bn pc po pi ip T cge cles CM cle ks
    (current next : tid) target bt bc ge caller selected les M ir aux enabled si ci au O tp
    sd f now ticks saved ba bs clock,
  get cles next=Some cle ->
  po f=Some(V293_source_OSTimeGet_function now ticks saved) ->
  current<>next ->
  get les current=Some caller -> get au current=Some aux ->
  get les next=Some selected -> get au next=Some(enabled,si,ci) ->
  get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
  get T next=Some(curs(scall f []),(kenil,kstop)) ->
  get ge target=Some(bt,Tptr tp) -> load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
  get ge OSTCBCur=Some(bc,Tptr tp) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M ba -> fresh M bs -> ba<>bs -> ba<>bc -> bs<>bc ->
  get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,aux,O,V293_time_get_action) |= SWINVt(V293_time_ready_inv br bg bp bn)current ->
  exists Ms Mc Mf,
    lpstep(pc,(po,pi,ip))T(cge,cles,CM)(ge,les,M,ir,au)current
      (set T current(SKIP,(kenil,ks)))(cge,cles,CM)(ge,les,Ms,ir,au)next /\
    V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)(T,(ge,les,M,ir,au),current)
      (set(set T current(SKIP,(kenil,ks)))next(curs(sskip (Some(Vint32 clock))),(kenil,kstop)),
        (ge,les,Mf,ir,au),next) /\
    store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms /\
    spec_step sd V293_time_get_action(set O curtid(oscurt next))(END (Some(Vint32 clock)))(set O curtid(oscurt next)) /\
    (ge,selected,Mf,ir,(enabled,si,ci),(set O curtid(oscurt next)),END (Some(Vint32 clock)))|=
      V293_time_ready_core br bg bp bn ** CurTid next /\
    freels(getaddr(V293_time_call_locals ticks saved ba bs))Mc Mf.
Proof.
  intros br bg bp bn pc po pi ip T cge cles CM cle ks current next target bt bc ge caller selected
    les M ir aux enabled si ci au O tp sd f now ticks saved ba bs clock
    Client Program Different Local Aux Selected NextAux Code NextCode Target Read Current
    TS NT NS Global FA FS Blocks AC SC Slot Held.
  destruct(V293_time_ready_global_switch br bg bp bn pc po pi ip T(cge,cles,CM)ks current next target bt bc
    ge caller selected les M ir aux(enabled,si,ci)au O V293_time_get_action tp
    Local Aux Selected NextAux Code Target Read Current Held)as(Ms&Switch&Store&Strong&Load&Outside).
  assert(Time:get(set O curtid(oscurt next))ostmid=Some(ostm clock)).
  { rewrite map_get_set' by discriminate;exact Slot. }
  destruct(V293_source_time_get_global br bg bp bn next pc po pi ip
    (set T current(SKIP,(kenil,ks)))les au cge cles CM cle sd ge selected
    Ms ir enabled si ci(set O curtid(oscurt next))f now ticks saved ba bs clock
    Client Program TS NT NS Global
    (V293_time_switch_fresh M Ms bc tp next ba AC FA Store)
    (V293_time_switch_fresh M Ms bc tp next bs SC FS Store)Blocks Time Strong)
    as(Mc&Mf&Call&Step&Closed&Final&Freed).
  exists Ms;exists Mc;exists Mf;split;[exact Switch | ];split.
  - eapply V293_time_global_switch_then;[exact Switch | exact Different | exact NextCode |
      exact Selected | exact NextAux | exact Call].
  - split;[exact Store | ];split;[exact Step | ];split;assumption.
Qed.

Theorem V293_time_switch_global_set : forall br bg bp bn pc po pi ip T cge cles CM cle ks
    (current next : tid) target bt bc ge caller selected les M ir aux enabled si ci au O tp
    sd f now ticks saved ba bs clock n,
  get cles next=Some cle ->
  po f=Some(V293_source_OSTimeSet_function now ticks saved) ->
  current<>next ->
  get les current=Some caller -> get au current=Some aux ->
  get les next=Some selected -> get au next=Some(enabled,si,ci) ->
  get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
  get T next=Some(curs(scall f [econst32 n]),(kenil,kstop)) ->
  get ge target=Some(bt,Tptr tp) -> load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
  get ge OSTCBCur=Some(bc,Tptr tp) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M ba -> fresh M bs -> ba<>bs -> ba<>bc -> bs<>bc ->
  get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,aux,O,(V293_time_set_action n)) |= SWINVt(V293_time_ready_inv br bg bp bn)current ->
  exists Ms Mc Mf,
    lpstep(pc,(po,pi,ip))T(cge,cles,CM)(ge,les,M,ir,au)current
      (set T current(SKIP,(kenil,ks)))(cge,cles,CM)(ge,les,Ms,ir,au)next /\
    V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)(T,(ge,les,M,ir,au),current)
      (set(set T current(SKIP,(kenil,ks)))next(curs(sskip None),(kenil,kstop)),
        (ge,les,Mf,ir,au),next) /\
    store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms /\
    spec_step sd (V293_time_set_action n)(set O curtid(oscurt next))(END None)(set(set O curtid(oscurt next))ostmid(ostm n)) /\
    (ge,selected,Mf,ir,(enabled,si,ci),(set(set O curtid(oscurt next))ostmid(ostm n)),END None)|=
      V293_time_ready_core br bg bp bn ** CurTid next /\
    freels(getaddr(V293_time_call_locals ticks saved ba bs))Mc Mf.
Proof.
  intros br bg bp bn pc po pi ip T cge cles CM cle ks current next target bt bc ge caller selected
    les M ir aux enabled si ci au O tp sd f now ticks saved ba bs clock n
    Client Program Different Local Aux Selected NextAux Code NextCode Target Read Current
    TS NT NS Global FA FS Blocks AC SC Slot Held.
  destruct(V293_time_ready_global_switch br bg bp bn pc po pi ip T(cge,cles,CM)ks current next target bt bc
    ge caller selected les M ir aux(enabled,si,ci)au O (V293_time_set_action n) tp
    Local Aux Selected NextAux Code Target Read Current Held)as(Ms&Switch&Store&Strong&Load&Outside).
  assert(Time:get(set O curtid(oscurt next))ostmid=Some(ostm clock)).
  { rewrite map_get_set' by discriminate;exact Slot. }
  destruct(V293_source_time_set_global br bg bp bn next pc po pi ip
    (set T current(SKIP,(kenil,ks)))les au cge cles CM cle sd ge selected
    Ms ir enabled si ci(set O curtid(oscurt next))f now ticks saved ba bs clock n
    Client Program TS NT NS Global
    (V293_time_switch_fresh M Ms bc tp next ba AC FA Store)
    (V293_time_switch_fresh M Ms bc tp next bs SC FS Store)Blocks Time Strong)
    as(Mc&Mf&Call&Step&Closed&Final&Freed).
  exists Ms;exists Mc;exists Mf;split;[exact Switch | ];split.
  - eapply V293_time_global_switch_then;[exact Switch | exact Different | exact NextCode |
      exact Selected | exact NextAux | exact Call].
  - split;[exact Store | ];split;[exact Step | ];split;assumption.
Qed.
