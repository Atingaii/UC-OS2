(* Independent byte heap: the empty local invariant is a fixture, not the
   production task invariant. Entry interrupt-enable is explicitly false. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition IEge : env := set(set(sig OSTCBCur (703%positive,Tptr Tvoid))
 9101%Z (701%positive,Tint8))9102%Z (702%positive,Tint8).
Definition IEtid : tid := (704%positive,Int.zero).
Definition IEbyte b n := V293_encoded_memory b 0 true (encode_val Tint8(V293_byteval n)).
Definition IEcurrent := V293_encoded_memory 703%positive 0 false (encode_val(Tptr Tvoid)(Vptr IEtid)).
Definition IEmemory run nest := merge(IEbyte 701%positive run)(merge(IEbyte 702%positive nest)IEcurrent).
Definition IEstate M := V293_wstate IEge emp M.
Definition IEresource run nest := V293_interrupt_resource 9101%Z 9102%Z 701%positive 702%positive run nest V293_witness_li IEtid.
Definition IEprogram := V293_OSIntEnter_unit 9200%Z 9101%Z 9102%Z.
Definition IEfpre := V293_interrupt_fpre 9101%Z 9102%Z 701%positive 702%positive V293_witness_li V293_witness_li_good.
Definition IEfpost := V293_interrupt_fpost 9101%Z 9102%Z 701%positive 702%positive V293_witness_li V293_witness_li_good.
Definition IElogic run nest := cons (logic_lv (cons (V293_byteval run) (cons (V293_byteval nest) nil))) (cons (logic_code(spec_done None)) nil).
Definition IEpre run nest := Aemp ** (V293_interrupt_pre 9101%Z 9102%Z 701%positive 702%positive run nest V293_witness_li IEtid (spec_done None) ** A_dom_lenv nil).
Definition IEpost run nest := Aemp ** (V293_interrupt_post 9101%Z 9102%Z 701%positive 702%positive run nest V293_witness_li IEtid (spec_done None) None ** A_dom_lenv nil).

Lemma IEcurrent_owned : IEstate IEcurrent |= CurTid IEtid.
Proof.
 exists Tvoid. exists 703%positive.
 eapply V293_wstate_star with(m1:=emp)(m2:=IEcurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 703%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma IElocal : CurTid IEtid ==> CurLINV V293_witness_li IEtid.
Proof.
 intros s HS. exists([]:list logicvar). unfold LINV,V293_witness_li.
 pose proof V293_witness_li_good as Good. clear -HS Good;sep auto.
Qed.
Lemma IEglobals : IEstate emp |= V293_interrupt_globals 9101%Z 9102%Z 701%positive 702%positive.
Proof.
 unfold V293_interrupt_globals. split.
 - exists 701%positive. split;[vm_compute;reflexivity|repeat split;reflexivity].
 - exists 702%positive. split;[vm_compute;reflexivity|repeat split;reflexivity].
Qed.
Ltac IEapart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold IEbyte,IEcurrent;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma IEresource_owned : forall run nest,IEstate(IEmemory run nest) |= IEresource run nest.
Proof.
 intros. unfold IEresource,V293_interrupt_resource,V293_interrupt_cells.
 cbn [V293_rdy_raw_cells].
 eapply V293_wstate_star with(m1:=IEbyte 701%positive run)(m2:=merge(IEbyte 702%positive nest)IEcurrent).
 - IEapart 701%positive.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply V293_wstate_star with(m1:=IEbyte 702%positive nest)(m2:=IEcurrent).
   + IEapart 702%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + eapply V293_wstate_star with(m1:=emp)(m2:=IEcurrent).
     * apply map_join_comm;apply map_join_emp.
     * apply IEglobals.
     * apply astar_comm. apply astar_l_aie_intro;[apply IElocal;apply IEcurrent_owned|reflexivity].
Qed.
Lemma IEdomain : forall M,eq_dom_env(getlenv(IEstate M))nil.
Proof.
 intros M x tp;change (False <-> exists b,get (emp:env) x=Some(b,tp));split;[contradiction|intros[b H];rewrite map_emp_get in H;discriminate].
Qed.
Lemma IEpre_owned : forall run nest,run<256 -> nest<256 ->
 IEstate(IEmemory run nest) |= IEpre run nest.
Proof.
 intros run nest Hr Hn. unfold IEpre.
 apply astar_l_aemp_intro. apply astar_comm. apply astar_l_adomlenv_intro;[ |apply IEdomain].
 unfold V293_interrupt_pre. apply astar_l_apure_intro;[ |auto].
 apply astar_l_aop'_intro;[apply IEresource_owned|reflexivity].
Qed.
Lemma IEunsigned : forall n,n<256 -> Z.to_nat(Int.unsigned(Int.repr(Z.of_nat n)))=n.
Proof.
 intros n H. rewrite Int.unsigned_repr by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 apply Nat2Z.id.
Qed.
Theorem IEbuilders : forall run nest,run<256 -> nest<256 ->
 Some(IEpre run nest)=BuildPreI IEprogram 9200%Z nil (IElogic run nest) IEfpre IEtid /\
 Some(fun result => Aemp ** (V293_interrupt_post 9101%Z 9102%Z 701%positive 702%positive run nest V293_witness_li IEtid (spec_done None) result ** A_dom_lenv nil))=
 BuildRetI IEprogram 9200%Z nil (IElogic run nest) IEfpost IEtid.
Proof.
 intros run nest Hr Hn.
 unfold BuildPreI,BuildRetI,IEprogram,V293_OSIntEnter_unit.
 destruct(Z.eq_dec 9200%Z 9200%Z);[ |contradiction].
 cbv beta iota zeta delta [V293_OSIntEnter_function rev revlcons dl_vl_match buildp buildq good_decllist getlenvdom IEfpre IEfpost V293_interrupt_fpre V293_interrupt_fpost getasrt IElogic V293_interrupt_pre_asrt V293_interrupt_post_asrt V293_byteval].
 rewrite !IEunsigned by assumption. split;reflexivity.
Qed.
Theorem IEnonempty_builders : forall run nest,run<256 -> nest<256 ->
 exists pre, Some pre=BuildPreI IEprogram 9200%Z nil(IElogic run nest)IEfpre IEtid /\
 IEstate(IEmemory run nest) |= pre.
Proof.
 intros run nest Hr Hn. exists(IEpre run nest). split;[exact(proj1(IEbuilders run nest Hr Hn))|apply IEpre_owned;assumption].
Qed.
Theorem IEbody_checked : forall Spec sd I run nest pre post,
 Some pre=BuildPreI IEprogram 9200%Z nil(IElogic run nest)IEfpre IEtid ->
 Some post=BuildRetI IEprogram 9200%Z nil(IElogic run nest)IEfpost IEtid ->
 InfRules Spec sd V293_witness_li I post Afalse pre(V293_OSIntEnter_body 9101%Z 9102%Z)Afalse IEtid.
Proof.
 intros. eapply V293_OSIntEnter_internal_contract;try eassumption. reflexivity.
Qed.
Theorem IEenvironment : forall sd I,
 WFFunEnv IEprogram(V293_OSIntEnter_spec 9200%Z 9101%Z 9102%Z 701%positive 702%positive V293_witness_li V293_witness_li_good)sd V293_witness_li I.
Proof. intros;apply V293_OSIntEnter_WFFunEnv. Qed.
Theorem IEactual_eval : forall run nest,run<256 -> nest<256 ->
 evalval(V293_OSIntEnter_running 9101%Z)(getsmem(IEstate(IEmemory run nest)))=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)) /\
 evalval(V293_OSIntEnter_room 9102%Z)(getsmem(IEstate(IEmemory run nest)))=
 Some(Vint32(if Nat.ltb nest 255 then Int.one else Int.zero)).
Proof.
 intros run nest Hr Hn.
 pose proof(V293_interrupt_entry_rearrange 9101%Z 9102%Z 701%positive 702%positive
 run nest V293_witness_li IEtid(spec_done None) _ (IEpre_owned run nest Hr Hn))as Owned.
 apply astar_comm in Owned. apply astar_l_apure_elim in Owned. destruct Owned as[_ Owned].
 apply astar_l_aop'_elim in Owned. destruct Owned as[_ Owned].
 pose proof(V293_interrupt_owned_eval _ _ _ _ _ _ _ _ Hr Hn
 (V293_interrupt_builder_env 9101%Z 9102%Z 701%positive 702%positive V293_witness_li IEtid) Owned)as E.
 tauto.
Qed.

Lemma IEpost_owned : forall run nest,
 IEstate(IEmemory run(V293_interrupt_nest_after run nest)) |= IEpost run nest.
Proof.
 intros. unfold IEpost. apply astar_l_aemp_intro. apply astar_comm.
 apply astar_l_adomlenv_intro;[ |apply IEdomain]. unfold V293_interrupt_post.
 apply astar_l_apure_intro;[ |reflexivity].
 apply astar_l_aop'_intro;[apply IEresource_owned|reflexivity].
Qed.
Lemma IEafter_range : forall run nest,nest<256 -> V293_interrupt_nest_after run nest<256.
Proof.
 intros run nest Hn. unfold V293_interrupt_nest_after.
 destruct(Nat.eqb run 1)eqn:Er;destruct(Nat.ltb nest 255)eqn:En;cbn;try lia.
 apply Nat.ltb_lt in En;lia.
Qed.
Lemma IEpost_load : forall run nest M,nest<256 -> IEstate M |= IEpost run nest ->
 load Tint8 M(702%positive,0%Z)=Some(V293_byteval(V293_interrupt_nest_after run nest)).
Proof.
 intros run nest M Hn HS. unfold IEpost in HS.
 apply astar_l_aemp_elim in HS. apply astar_comm in HS.
 apply astar_l_adomlenv_elim in HS. destruct HS as[_ HS].
 unfold V293_interrupt_post in HS. apply astar_l_apure_elim in HS. destruct HS as[_ HS].
 apply astar_l_aop'_elim in HS. destruct HS as[_ HS].
 eapply (V293_rdy_raw_load (V293_interrupt_cells 701%positive 702%positive run(V293_interrupt_nest_after run nest))
 (V293_interrupt_globals 9101%Z 9102%Z 701%positive 702%positive ** (CurLINV V293_witness_li IEtid ** Aie false)) _ _ _ (IEstate M)).
 - cbn [V293_interrupt_cells In];tauto.
 - apply V293_byte_type;apply IEafter_range;exact Hn.
 - exact HS.
Qed.

(* Each comparison keeps the other byte fixed, and evaluates the original
   expressions from the independently constructed spatial heap. *)
Theorem IErun_control :
 evalval(V293_OSIntEnter_running 9101%Z)(getsmem(IEstate(IEmemory 1 254)))=Some(Vint32 Int.one) /\
 evalval(V293_OSIntEnter_running 9101%Z)(getsmem(IEstate(IEmemory 0 254)))=Some(Vint32 Int.zero) /\
 evalval(V293_OSIntEnter_running 9101%Z)(getsmem(IEstate(IEmemory 2 254)))=Some(Vint32 Int.zero) /\
 V293_interrupt_nest_after 1 254=255 /\ V293_interrupt_nest_after 0 254=254 /\ V293_interrupt_nest_after 2 254=254.
Proof.
 split;[exact(proj1(IEactual_eval 1 254 ltac:(lia) ltac:(lia)))| ].
 split;[exact(proj1(IEactual_eval 0 254 ltac:(lia) ltac:(lia)))| ].
 split;[exact(proj1(IEactual_eval 2 254 ltac:(lia) ltac:(lia)))| ].
 repeat split;reflexivity.
Qed.
Theorem IEsaturation_control :
 evalval(V293_OSIntEnter_room 9102%Z)(getsmem(IEstate(IEmemory 1 254)))=Some(Vint32 Int.one) /\
 evalval(V293_OSIntEnter_room 9102%Z)(getsmem(IEstate(IEmemory 1 255)))=Some(Vint32 Int.zero) /\
 V293_interrupt_nest_after 1 254=255 /\ V293_interrupt_nest_after 1 255=255 /\
 IEstate(IEmemory 1 255) |= IEpost 1 254 /\ IEstate(IEmemory 1 255) |= IEpost 1 255.
Proof.
 split;[exact(proj2(IEactual_eval 1 254 ltac:(lia) ltac:(lia)))| ].
 split;[exact(proj2(IEactual_eval 1 255 ltac:(lia) ltac:(lia)))| ].
 split;[reflexivity| ]. split;[reflexivity| ]. split;[exact(IEpost_owned 1 254)|exact(IEpost_owned 1 255)].
Qed.
Theorem IEwrong_post_control :
 eq_dom_env(getlenv(IEstate(IEmemory 1 255)))nil /\
 IEstate(IEmemory 1 255) |= IEpost 1 254 /\
 ~ (IEstate(IEmemory 1 255) |= IEpost 1 253).
Proof.
 split;[apply IEdomain| ]. split;[exact(IEpost_owned 1 254)| ].
 intro Bad. pose proof(IEpost_load 1 253 (IEmemory 1 255)ltac:(lia) Bad)as Wrong.
 pose proof(IEpost_load 1 254 (IEmemory 1 255)ltac:(lia)(IEpost_owned 1 254))as Actual.
 rewrite Actual in Wrong. vm_compute in Wrong;discriminate.
Qed.
Theorem IEnot_running_outputs :
 IEstate(IEmemory 0 254) |= IEpost 0 254 /\ IEstate(IEmemory 2 254) |= IEpost 2 254.
Proof. split;[exact(IEpost_owned 0 254)|exact(IEpost_owned 2 254)]. Qed.
