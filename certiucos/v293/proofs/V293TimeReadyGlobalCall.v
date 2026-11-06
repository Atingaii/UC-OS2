(* One real global switch, followed on its actual heap by a generated time
   call. The call suffix is local; no global interleaving claim is made. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeSourceReadyCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAPICall.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSharedSet.
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.code.V293TimeSource.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyShared.
Require Import CertiOS.certiucos.v293.proofs.V293TimeReadyEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.

(* Forgetting the clock is used only to obtain the physical writable store.
   The postcondition below is recovered with the original strong invariant. *)
Lemma V293_time_ready_switch_forget : forall br bg bp bn t,
  SWINVt(V293_time_ready_inv br bg bp bn)t ==>
    SWINVt(V293_ready_inv br bg bp)t ** Atrue.
Proof.
  intros br bg bp bn t s Held.
  apply V293_time_ready_switch_full_open in Held.
  unfold V293_time_ready_switch_full,V293_time_ready_switch_fields in Held.
  sep normal in Held. sep destruct Held.
  apply astar_mono with(P:=V293_shared_flags ** V293_ready_full br bg bp t)(Q:=Atrue).
  - apply V293_ready_switch_halves.
  - intros st H;exact H.
  - unfold V293_ready_full. clear -Held. sep auto.
Qed.

Theorem V293_time_ready_global_switch : forall br bg bp bn pc po pi ip T cst ks
    (current next : tid) target bt bc ge caller selected les M ir aux nextaux au O op tp,
  get les current=Some caller -> get au current=Some aux ->
  get les next=Some selected -> get au next=Some nextaux ->
  get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
  get ge target=Some(bt,Tptr tp) -> load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
  get ge OSTCBCur=Some(bc,Tptr tp) ->
  (ge,caller,M,ir,aux,O,op) |= SWINVt(V293_time_ready_inv br bg bp bn)current ->
  exists Ms,
    lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
      (set T current(SKIP,(kenil,ks)))cst(ge,les,Ms,ir,au)next /\
    store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms /\
    (ge,selected,Ms,ir,nextaux,set O curtid(oscurt next),op) |=
      V293_time_ready_core br bg bp bn ** CurTid next /\
    load(Tptr tp)Ms(bc,0%Z)=Some(Vptr next) /\
    (forall c i,c<>bc \/(i<0)%Z \/(4<=i)%Z ->get Ms(c,i)=get M(c,i)).
Proof.
  intros br bg bp bn pc po pi ip T cst ks current next target bt bc ge caller selected
    les M ir aux nextaux au O op tp Local Aux Selected NextAux Code Target Read Current Held.
  pose proof(V293_time_ready_switch_forget br bg bp bn current _ Held)as Weak.
  destruct(V293_ready_current_write br bg bp current next Atrue ge caller M ir aux O op bc tp Weak Current)
    as(Ms&Store&Ready&Load&Outside).
  pose proof(V293_time_ready_switch_store br bg bp bn current next ge caller M Ms ir aux O op
    bc tp Held Current Store)as Strong.
  pose proof(V293_time_ready_entry_halves br bg bp bn next _ Strong)as Halves.
  exists Ms;split.
  - eapply pswitch_step with(tst:=((ge,caller,M),ir,aux))(l:=bt)(tp:=tp)(b:=bc);
      try reflexivity;try eassumption.
    unfold projS,projD. rewrite Local,Aux;reflexivity.
  - split;[exact Store | ]. split.
    + destruct aux as[[ie si]ci]. destruct nextaux as[[ie' si']ci'].
      eapply V293_source_time_entry_core;exact Halves.
    + split;assumption.
Qed.

Lemma V293_time_switch_fresh : forall M Ms bc tp next b,
  b<>bc -> fresh M b -> store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms -> fresh Ms b.
Proof.
  intros M Ms bc tp next b Apart Fresh Store l i E [v Bound];subst l.
  change(get Ms(b,i)=Some v)in Bound.
  erewrite V293_storebytes_outside in Bound;[ | exact Store | left;exact Apart].
  apply(Fresh(b,i)i eq_refl);exists v;exact Bound.
Qed.

(* The selected code and environment are the entries in the switch maps.
   Only the switch is global here; the call uses the identical Ms endpoint. *)
Theorem V293_time_switch_source_get : forall br bg bp bn pc po pi ip T cst ks ksel
    (current next : tid) target bt bc ge caller selected les M ir aux enabled si ci au O tp
    sd f now ticks saved ba bs clock,
  po f=Some(V293_source_OSTimeGet_function now ticks saved) ->
  current<>next ->
  get les current=Some caller -> get au current=Some aux ->
  get les next=Some selected -> get au next=Some(enabled,si,ci) ->
  get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
  get T next=Some(curs(scall f []),(kenil,ksel)) ->
  get ge target=Some(bt,Tptr tp) -> load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
  get ge OSTCBCur=Some(bc,Tptr tp) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M ba -> fresh M bs -> ba<>bs -> ba<>bc -> bs<>bc ->
  get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,aux,O,V293_time_get_action) |= SWINVt(V293_time_ready_inv br bg bp bn)current ->
  exists Ms Mc Mf,
    lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
      (set T current(SKIP,(kenil,ks)))cst(ge,les,Ms,ir,au)next /\
    get(set T current(SKIP,(kenil,ks)))next=Some(curs(scall f []),(kenil,ksel)) /\
    store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms /\
    V293_local_steps(pumerge po pi)(curs(scall f []),(kenil,ksel))
      ((ge,selected,Ms),ir,(enabled,si,ci))
      (curs(sskip (Some(Vint32 clock))),(kenil,ksel))((ge,selected,Mf),ir,(enabled,si,ci)) /\
    spec_step sd V293_time_get_action(set O curtid(oscurt next))(END (Some(Vint32 clock)))(set O curtid(oscurt next)) /\
    (ge,selected,Mf,ir,(enabled,si,ci),(set O curtid(oscurt next)),END (Some(Vint32 clock))) |=
      V293_time_ready_core br bg bp bn ** CurTid next /\
    freels(getaddr(V293_time_call_locals ticks saved ba bs))Mc Mf.
Proof.
  intros br bg bp bn pc po pi ip T cst ks ksel current next target bt bc ge caller selected
    les M ir aux enabled si ci au O tp sd f now ticks saved ba bs clock
    Program Different Local Aux Selected NextAux Code NextCode Target Read Current
    TS NT NS Global FA FS Blocks AC SC Slot Held.
  destruct(V293_time_ready_global_switch br bg bp bn pc po pi ip T cst ks current next target bt bc
    ge caller selected les M ir aux(enabled,si,ci)au O V293_time_get_action tp
    Local Aux Selected NextAux Code Target Read Current Held)as(Ms&Switch&Store&Strong&Load&Outside).
  assert(Bind:pumerge po pi f=Some(V293_source_OSTimeGet_function now ticks saved)).
  { unfold pumerge;rewrite Program;reflexivity. }
  assert(Time:get(set O curtid(oscurt next))ostmid=Some(ostm clock)).
  { rewrite map_get_set' by discriminate;exact Slot. }
  destruct(V293_source_time_get_ready_call br bg bp bn next(pumerge po pi)sd ksel ge selected
    Ms ir enabled si ci(set O curtid(oscurt next)) f now ticks saved ba bs clock
    Bind TS NT NS Global
    (V293_time_switch_fresh M Ms bc tp next ba AC FA Store)
    (V293_time_switch_fresh M Ms bc tp next bs SC FS Store)Blocks Time Strong)
    as(Mc&Mf&Exec&Prefix&Suffix&Step&Closed&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split.
  - rewrite map_get_set' by congruence;exact NextCode.
  - split;[exact Store | ]. split;[exact Exec | ]. split;[exact Step | ]. split;assumption.
Qed.

(* The selected code and environment are the entries in the switch maps.
   Only the switch is global here; the call uses the identical Ms endpoint. *)
Theorem V293_time_switch_source_set : forall br bg bp bn pc po pi ip T cst ks ksel
    (current next : tid) target bt bc ge caller selected les M ir aux enabled si ci au O tp
    sd f now ticks saved ba bs clock n,
  po f=Some(V293_source_OSTimeSet_function now ticks saved) ->
  current<>next ->
  get les current=Some caller -> get au current=Some aux ->
  get les next=Some selected -> get au next=Some(enabled,si,ci) ->
  get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
  get T next=Some(curs(scall f [econst32 n]),(kenil,ksel)) ->
  get ge target=Some(bt,Tptr tp) -> load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
  get ge OSTCBCur=Some(bc,Tptr tp) ->
  ticks<>saved -> now<>ticks -> now<>saved -> get ge now=Some(bn,Tint32) ->
  fresh M ba -> fresh M bs -> ba<>bs -> ba<>bc -> bs<>bc ->
  get O ostmid=Some(ostm clock) ->
  (ge,caller,M,ir,aux,O,(V293_time_set_action n)) |= SWINVt(V293_time_ready_inv br bg bp bn)current ->
  exists Ms Mc Mf,
    lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
      (set T current(SKIP,(kenil,ks)))cst(ge,les,Ms,ir,au)next /\
    get(set T current(SKIP,(kenil,ks)))next=Some(curs(scall f [econst32 n]),(kenil,ksel)) /\
    store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Ms /\
    V293_local_steps(pumerge po pi)(curs(scall f [econst32 n]),(kenil,ksel))
      ((ge,selected,Ms),ir,(enabled,si,ci))
      (curs(sskip None),(kenil,ksel))((ge,selected,Mf),ir,(enabled,si,ci)) /\
    spec_step sd (V293_time_set_action n)(set O curtid(oscurt next))(END None)(set(set O curtid(oscurt next))ostmid(ostm n)) /\
    (ge,selected,Mf,ir,(enabled,si,ci),(set(set O curtid(oscurt next))ostmid(ostm n)),END None) |=
      V293_time_ready_core br bg bp bn ** CurTid next /\
    freels(getaddr(V293_time_call_locals ticks saved ba bs))Mc Mf.
Proof.
  intros br bg bp bn pc po pi ip T cst ks ksel current next target bt bc ge caller selected
    les M ir aux enabled si ci au O tp sd f now ticks saved ba bs clock n
    Program Different Local Aux Selected NextAux Code NextCode Target Read Current
    TS NT NS Global FA FS Blocks AC SC Slot Held.
  destruct(V293_time_ready_global_switch br bg bp bn pc po pi ip T cst ks current next target bt bc
    ge caller selected les M ir aux(enabled,si,ci)au O (V293_time_set_action n) tp
    Local Aux Selected NextAux Code Target Read Current Held)as(Ms&Switch&Store&Strong&Load&Outside).
  assert(Bind:pumerge po pi f=Some(V293_source_OSTimeSet_function now ticks saved)).
  { unfold pumerge;rewrite Program;reflexivity. }
  assert(Time:get(set O curtid(oscurt next))ostmid=Some(ostm clock)).
  { rewrite map_get_set' by discriminate;exact Slot. }
  destruct(V293_source_time_set_ready_call br bg bp bn next(pumerge po pi)sd ksel ge selected
    Ms ir enabled si ci(set O curtid(oscurt next)) f now ticks saved ba bs clock n
    Bind TS NT NS Global
    (V293_time_switch_fresh M Ms bc tp next ba AC FA Store)
    (V293_time_switch_fresh M Ms bc tp next bs SC FS Store)Blocks Time Strong)
    as(Mc&Mf&Exec&Prefix&Suffix&Step&Closed&Final&Freed).
  exists Ms. exists Mc. exists Mf. split;[exact Switch | ]. split.
  - rewrite map_get_set' by congruence;exact NextCode.
  - split;[exact Store | ]. split;[exact Exec | ]. split;[exact Step | ]. split;assumption.
Qed.

(* The shared abstract current slot must agree with the same physical cell;
   ready records and the clock alone cannot repair a stale task identity. *)
Lemma V293_time_ready_current_owned : forall br bg bp bn R ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_time_ready_core br bg bp bn ** R ->
  exists t b tp, get O curtid=Some(oscurt t) /\
    get ge OSTCBCur=Some(b,Tptr tp) /\ load(Tptr tp)M(b,0%Z)=Some(Vptr t).
Proof.
  intros br bg bp bn R ge le M ir aux O op Held.
  unfold V293_time_ready_core,V293_time_ready_fields in Held.
  sep normal in Held. sep destruct Held.
  assert(Current:(ge,le,M,ir,aux,O,op) |= CurTid x0 ** Atrue)by(clear -Held;sep auto).
  destruct(V293_shared_current_read _ _ _ _ _ _ _ _ _ Current)as(b&tp&Name&Read).
  exists x0. exists b. exists tp. split.
  - change(get(getabst(ge,le,M,ir,aux,O,op))curtid=Some(oscurt x0)).
    eapply V293_star_abst_get_l with(p:=Aabsdata curtid(oscurt x0))(q:=Atrue).
    + apply V293_shared_abs_get.
    + unfold V293_shared_fields in Held;clear Current;sep auto.
  - split;assumption.
Qed.
