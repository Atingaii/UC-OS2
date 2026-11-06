(* Immediate global switch with a jointly owned active-task endpoint.
   Enabled selected tasks carry ready_full, not the disabled switch flags. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyOwnedSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.

Lemma V293_owned_switch_active_view : forall br bg bp t R ge le M ir ie is cs O op,
 GoodInvAsrt R ->
 (ge,le,M,ir,(ie,is,cs),O,op)|=SWINVt(V293_ready_inv br bg bp)t **R ->
 forall le' ie' cs',
 (ge,le',M,ir,(ie',is,cs'),O,op)|=V293_ready_full br bg bp t **R.
Proof.
 intros br bg bp t R ge le M ir ie is cs O op Good Held le' ie' cs'.
 assert(Open:(ge,le,M,ir,(ie,is,cs),O,op)|=
 (V293_shared_flags **V293_ready_full br bg bp t) **R).
 { eapply astar_mono;[apply V293_ready_switch_full|intros s H;exact H|exact Held]. }
 assert(Full:(ge,le,M,ir,(ie,is,cs),O,op)|=V293_ready_full br bg bp t **R).
 { assert(Empty:V293_shared_flags ==>Aemp).
   { intros s Flags;unfold V293_shared_flags in Flags.
     apply astar_l_aemp_elim.
     eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
     [ |intros s0[k[_ E]];exact E|exact Flags].
     intros s0 F;apply astar_l_aemp_elim.
     eapply astar_mono with(P:=isrclr)(Q:=Aie false);
     [ |intros s1[_ E];exact E|exact F].
     intros s1[r[Flag Clear]];exact(proj2 Flag). }
   apply astar_l_aemp_elim.
   eapply astar_mono;[exact Empty|intros s H;exact H| ].
   clear Held Empty;sep auto. }
 eapply good_inv_prop;[split;[apply V293_owned_ready_good|exact Good]|exact Full].
Qed.

(* The caller supplies current ownership, not a successful store or final heap.
   The selected environment/auxiliary bindings are checked on the same maps.
   Interrupt-stack identity is explicit; IE and critical stack may change. *)
Theorem V293_owned_global_switch : forall br bg bp pc po pi ip T cst ks current next
 target bt bc ge le le' les M ir ie ie' is cs cs' au O op R tp,
 get les current=Some le ->get au current=Some(ie,is,cs) ->
 get les next=Some le' ->get au next=Some(ie',is,cs') ->
 get T current=Some(curs(sprim(switch target)),(kenil,ks)) ->
 get ge target=Some(bt,Tptr tp) ->load(Tptr tp)M(bt,0%Z)=Some(Vptr next) ->
 get ge OSTCBCur=Some(bc,Tptr tp) ->GoodInvAsrt R ->
 (ge,le,M,ir,(ie,is,cs),O,op)|=SWINVt(V293_ready_inv br bg bp)current **R ->
 exists Mf,
 lpstep(pc,(po,pi,ip))T cst(ge,les,M,ir,au)current
 (set T current(SKIP,(kenil,ks)))cst(ge,les,Mf,ir,au)next /\
 store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf /\
 (ge,le',Mf,ir,(ie',is,cs'),set O curtid(oscurt next),op)|=
 V293_ready_full br bg bp next **R /\
 load(Tptr tp)Mf(bc,0%Z)=Some(Vptr next) /\
 get(set O curtid(oscurt next))curtid=Some(oscurt next) /\
 get les next=Some le' /\get au next=Some(ie',is,cs') /\
 (forall c i,c<>bc \/(i<0)%Z \/(4<=i)%Z ->get Mf(c,i)=get M(c,i)).
Proof.
 intros br bg bp pc po pi ip T cst ks current next target bt bc ge le le' les M ir
 ie ie' is cs cs' au O op R tp Local Aux NextLocal NextAux Code Target Read Current Good Held.
 destruct(V293_ready_switch_step br bg bp pc po pi ip T cst ks current next target bt bc
 ge le les M ir(ie,is,cs)au O op R tp Local Aux Code Target Read Current Held)
 as(Mf&Step&Store&After&Load&Hskip&Other&Outside).
 exists Mf;split;[exact Step| ];split;[exact Store| ];split.
 - eapply V293_owned_switch_active_view;[exact Good|exact After].
 - split;[exact Load| ];split;[apply map_get_set| ];
   split;[exact NextLocal| ];split;assumption.
Qed.
