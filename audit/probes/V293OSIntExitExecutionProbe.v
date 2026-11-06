Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition NEge : env := set(set emp 100%Z(51%positive,Tint8))101%Z(52%positive,Tint8).
Definition NEle : env := sig 601%Z(61%positive,Tint32).
Definition NEmem n := V293_fixture_put_bytes
 (V293_put_byte(V293_put_byte emp(51%positive,0%Z)1)(52%positive,0%Z)n)
 61%positive 0%Z(encode_val Tint32(Vint32(Int.repr 23))).
Definition NEbody := V293_OSIntExit_abstract_body 100%Z 101%Z 102%Z 601%Z
 103%Z 104%Z 105%Z 106%Z 107%Z 200%Z 203%Z.
Definition NEprogram : progunit := fun _=>None.

Lemma NEentry_loads : forall n,n<256 ->
 load Tint8(NEmem n)(51%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8(NEmem n)(52%positive,0%Z)=Some(V293_byteval n) /\
 load Tint32(NEmem n)(61%positive,0%Z)=Some(Vint32(Int.repr 23)).
Proof.
 intros n N;unfold NEmem;split.
 - etransitivity;[apply V293_load_block_frame;intro j;apply V293_fixture_bytes_outside;left;discriminate | ].
   rewrite V293_put_byte_other_load by discriminate;apply V293_put_byte_load;lia.
 - split.
   + etransitivity;[apply V293_load_block_frame;intro j;apply V293_fixture_bytes_outside;left;discriminate | ].
     apply V293_put_byte_load;exact N.
   + apply V293_fixture_encoded_load;reflexivity.
Qed.

(* Every store is constructed from writable bytes, not assumed. Both initial
   IE values and arbitrary interrupt/critical-stack tails use the SAME memory;
   the old saved word is 23, deliberately not the Boolean IE encoding. *)
Theorem NEnested_witness : forall n ir enabled si ci,2<=n -> n<256 ->
 exists Mf,
 V293_local_steps NEprogram(curs NEbody,(kenil,kcall 300%Z sret emp kstop))
 ((NEge,NEle,NEmem n),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((NEge,emp,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval(Nat.pred n)) /\
 load Tint8 Mf(51%positive,0%Z)=Some(V293_byteval 1) /\
 (forall k,k<4 -> get Mf(61%positive,Z.of_nat k)=None) /\
 (forall b i,b<>61%positive -> b<>52%positive ->get Mf(b,i)=get(NEmem n)(b,i)).
Proof.
 intros n ir enabled si ci Lower Bound.
 assert(W:V293_bytes_writable(NEmem n)61%positive 0%Z 4).
 { intros k K;unfold NEmem;eexists;apply V293_fixture_bytes_nth;rewrite encode_val_length;exact K. }
 destruct(V293_storebytes_exists(encode_val Tint32(Vint32 Int.zero))(NEmem n)61%positive 0%Z)
 as[M0 Init];[rewrite encode_val_length;exact W | ].
 assert(F0:forall b i,b<>61%positive ->get M0(b,i)=get(NEmem n)(b,i)).
 { intros;eapply V293_storebytes_outside;[exact Init | left;assumption]. }
 assert(Wn:V293_bytes_writable M0 52%positive 0%Z 1).
 { intros k K;assert(k=0)by lia;subst k;cbn;rewrite F0 by discriminate.
   unfold NEmem;rewrite V293_fixture_bytes_outside by(left;discriminate).
   eexists;apply V293_put_byte_get_same. }
 destruct(V293_storebytes_exists(encode_val Tint8(V293_byteval(Nat.pred n)))M0 52%positive 0%Z)
 as[M1 Dec];[rewrite encode_val_length;exact Wn | ].
 assert(F1:forall b i,b<>52%positive ->get M1(b,i)=get M0(b,i)).
 { intros;eapply V293_storebytes_outside;[exact Dec | left;assumption]. }
 assert(W0:V293_bytes_writable M0 61%positive 0%Z 4).
 { intros k K;destruct(W k K)as[v V];eapply V293_store_writable;[exact Init | exact V]. }
 assert(W1:forall b t,In(b,t)(getaddr NEle)->V293_bytes_writable M1 b 0%Z(typelen t)).
 { intros b t [E | F];[inversion E;subst b t | contradiction].
   intros k K;rewrite F1 by discriminate;apply W0;exact K. }
 destruct(NEentry_loads n Bound)as[Run[Nest Saved]].
 assert(R0:load Tint8 M0(51%positive,0%Z)=Some(V293_byteval 1)).
 { etransitivity;[apply V293_load_block_frame;intro j;apply F0;discriminate | exact Run]. }
 assert(N0:load Tint8 M0(52%positive,0%Z)=Some(V293_byteval n)).
 { etransitivity;[apply V293_load_block_frame;intro j;apply F0;discriminate | exact Nest]. }
 assert(Addr:getaddr NEle=[(61%positive,Tint32)])by reflexivity.
 assert(ND:NoDup(map fst(getaddr NEle))).
 { change(NoDup (cons 61%positive nil));repeat constructor;cbn;tauto. }
 destruct(V293_OSIntExit_nested_execution NEprogram(kcall 300%Z sret emp kstop)NEge NEle emp
 (NEmem n)M0 M1 ir enabled si ci
 100%Z 101%Z 102%Z 601%Z 103%Z 104%Z 105%Z 106%Z 107%Z 200%Z 203%Z
 51%positive 52%positive 61%positive n 300%Z sret kstop
 Lower Bound eq_refl Init eq_refl eq_refl R0 eq_refl eq_refl N0 Dec eq_refl ND W1)
 as[Mf[Exec[Frame Removed]]].
 exists Mf;split;[exact Exec | ].
 split.
 - etransitivity;[apply V293_load_block_frame;intro j;apply Frame;rewrite Addr;cbn;intuition discriminate | ].
   eapply V293_exit_byte_readback;[lia | exact Dec].
 - split.
   + etransitivity;[apply V293_load_block_frame;intro j;apply Frame;rewrite Addr;cbn;intuition discriminate | ].
     etransitivity;[apply V293_load_block_frame;intro j;apply F1;discriminate | exact R0].
   + split.
     * intros k K;apply Removed with Tint32;[left;reflexivity | exact K].
     * intros b i Bs Bn;rewrite Frame by(rewrite Addr;cbn;intuition congruence).
       rewrite F1 by exact Bn;apply F0;exact Bs.
Qed.

Corollary NEnest2 : forall ir enabled si ci,
 exists Mf,V293_local_steps NEprogram(curs NEbody,(kenil,kcall 300%Z sret emp kstop))
 ((NEge,NEle,NEmem 2),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((NEge,emp,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval 1).
Proof. intros;destruct(NEnested_witness 2 ir enabled si ci ltac:(lia)ltac:(lia))as[M[Exec[Load Rest]]];exists M;auto. Qed.
Corollary NEnest255 : forall ir enabled si ci,
 exists Mf,V293_local_steps NEprogram(curs NEbody,(kenil,kcall 300%Z sret emp kstop))
 ((NEge,NEle,NEmem 255),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kstop))((NEge,emp,Mf),ir,(enabled,si,ci)) /\
 load Tint8 Mf(52%positive,0%Z)=Some(V293_byteval 254).
Proof. intros;destruct(NEnested_witness 255 ir enabled si ci ltac:(lia)ltac:(lia))as[M[Exec[Load Rest]]];exists M;auto. Qed.

(* Single-factor ablation at an isolated critical-segment boundary: identical input,
   physical decrement and continuation; only excrit becomes a no-op. *)
Definition NEcritical (restore:bool) nesting lock dispatch :=
 sseq(sprim encrit)(sseq(V293_OSIntExit_nesting_dispatch nesting lock dispatch)
 (if restore then sprim excrit else sskip None)).
Theorem NEcritical_execution : forall restore P ks ge le M M' ir enabled si ci nesting lock bn n dispatch,
 2<=n ->n<256 ->get le nesting=None ->get ge nesting=Some(bn,Tint8) ->
 load Tint8 M(bn,0%Z)=Some(V293_byteval n) ->
 store Tint8 M(bn,0%Z)(V293_byteval(Nat.pred n))=Some M' ->
 V293_local_steps P(curs(NEcritical restore nesting lock dispatch),(kenil,ks))
 ((ge,le,M),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,ks))
 ((ge,le,M'),ir,if restore then(enabled,si,ci)else(false,si,enabled::ci)).
Proof.
 intros restore P ks ge le M M' ir enabled si ci nesting lock bn n dispatch Lower Bound NL G Load Store.
 unfold NEcritical.
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step] | ].
 eapply V293_local_cons;[apply encrit_step;reflexivity | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step] | ].
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sseq_step] | ].
 eapply V293_local_trans.
 { apply V293_csteps_local;eapply V293_OSIntExit_nested_middle_execution;eassumption. }
 eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity | apply sskip_step] | ].
 destruct restore.
 - eapply V293_local_cons;[apply excrit_step;reflexivity | apply V293_local_refl].
 - apply V293_local_refl.
Qed.
Theorem NEmissing_exit_changes_aux : forall (enabled:bool)(si:is)(ci:cs),
 (false,si,enabled::ci)<>(enabled,si,ci).
Proof.
 intros enabled si ci E;apply(f_equal(fun x:ie*is*cs=>length(snd x)))in E.
 cbn in E;lia.
Qed.
Theorem NEnest_changed : forall M M' bn n,2<=n ->n<256 ->
 store Tint8 M(bn,0%Z)(V293_byteval(Nat.pred n))=Some M' ->
 load Tint8 M'(bn,0%Z)<>Some(V293_byteval n).
Proof.
 intros M M' bn n Lower Bound Store Bad.
 pose proof(V293_exit_byte_readback M M' bn(Nat.pred n)ltac:(lia)Store)as Actual.
 rewrite Actual in Bad;inversion Bad as[Same].
 change(Int.unsigned(Int.repr(Z.of_nat(Nat.pred n)))=Int.unsigned(Int.repr(Z.of_nat n)))in Same.
 rewrite !Int.unsigned_repr in Same by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia);lia.
Qed.

(* Concrete paired executions, not merely a comparison of proposed states.
   This isolates the critical segment; it does not assert a mutant full-body
   trace from the function entry. The same return continuation is pending. *)
Theorem NEcritical_pair_witness : forall ir enabled si ci,
 exists M',
 V293_local_steps NEprogram
 (curs(NEcritical true 101%Z 102%Z sret),(kenil,kseq sret(kcall 300%Z sret emp kstop)))
 ((NEge,NEle,NEmem 2),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kseq sret(kcall 300%Z sret emp kstop)))
 ((NEge,NEle,M'),ir,(enabled,si,ci)) /\
 V293_local_steps NEprogram
 (curs(NEcritical false 101%Z 102%Z sret),(kenil,kseq sret(kcall 300%Z sret emp kstop)))
 ((NEge,NEle,NEmem 2),ir,(enabled,si,ci))
 (curs(sskip None),(kenil,kseq sret(kcall 300%Z sret emp kstop)))
 ((NEge,NEle,M'),ir,(false,si,enabled::ci)) /\
 load Tint8 M'(52%positive,0%Z)=Some(V293_byteval 1) /\
 (false,si,enabled::ci)<>(enabled,si,ci).
Proof.
 intros ir enabled si ci.
 assert(W:exists old,get(NEmem 2)(52%positive,0%Z)=Some(true,old)).
 { unfold NEmem;rewrite V293_fixture_bytes_outside by(left;discriminate).
   eexists;apply V293_put_byte_get_same. }
 destruct W as[old W].
 pose proof(V293_put_byte_store(NEmem 2)(52%positive,0%Z)1 old W)as Store.
 destruct(NEentry_loads 2 ltac:(lia))as[Run[Nest Saved]].
 exists(V293_put_byte(NEmem 2)(52%positive,0%Z)1).
 split.
 - eapply (NEcritical_execution true);try reflexivity;try eassumption;lia.
 - split.
   + eapply (NEcritical_execution false);try reflexivity;try eassumption;lia.
   + split;[apply V293_put_byte_load;lia | apply NEmissing_exit_changes_aux].
Qed.
