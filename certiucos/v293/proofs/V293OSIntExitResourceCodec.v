Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
(* Actual single-local builders for the original OSIntExit. This connects
   allocated builder assertions, not an allocator/free execution trace. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitIndexedPort.

(* Logical snapshots are proof arguments, not additional runtime state.
   Layout and assertion continuations remain static semantic parameters. *)
Record V293_exit_snapshot := V293_mk_exit_snapshot {
 V293_xlo:nat; V293_xhi:nat; V293_xcurrent:nat;
 V293_xnest:nat; V293_xlocked:nat;
 V293_xcounter:int32; V293_xold:val; V293_xtoken:val; V293_xvalue:val;
 V293_xentries:list val; V293_xtasks:TcbMod.map; V293_xaop:spec_code
}.
Definition V293_exit_snapshot_bounded x :=
 V293_xlo x<256 /\ V293_xhi x<256 /\ V293_xcurrent x<256 /\
 V293_xnest x<256 /\ V293_xlocked x<256.
Definition V293_exit_encode x : list logicvar :=
 logic_lv(V293_byteval(V293_xlo x)::V293_byteval(V293_xhi x)::
 V293_byteval(V293_xcurrent x)::V293_byteval(V293_xnest x)::
 V293_byteval(V293_xlocked x)::Vint32(V293_xcounter x)::V293_xold x::
 V293_xtoken x::V293_xvalue x::nil)::
 logic_lv(V293_xentries x)::logic_abstcb(V293_xtasks x)::logic_code(V293_xaop x)::nil.
Definition V293_exit_decode lg : option V293_exit_snapshot :=
 match lg with
 | logic_lv(Vint32 lo::Vint32 hi::Vint32 nc::Vint32 nest::Vint32 locked::
    Vint32 c::old::token::value::nil)::logic_lv entries::logic_abstcb tasks::logic_code aop::nil =>
   let l:=Z.to_nat(Int.unsigned lo) in let h:=Z.to_nat(Int.unsigned hi) in
   let n:=Z.to_nat(Int.unsigned nc) in let d:=Z.to_nat(Int.unsigned nest) in
   let k:=Z.to_nat(Int.unsigned locked) in
   if (l <? 256) && (h <? 256) && (n <? 256) && (d <? 256) && (k <? 256)
   then Some(V293_mk_exit_snapshot l h n d k c old token value entries tasks aop)
   else None
 | _ => None
 end.
Lemma V293_exit_codec_roundtrip : forall x,
 V293_exit_snapshot_bounded x -> V293_exit_decode(V293_exit_encode x)=Some x.
Proof.
 intros [lo hi nc nest locked c old token value entries tasks aop] [L [H [N [D K]]]].
 unfold V293_exit_decode,V293_exit_encode,V293_byteval;cbn.
 repeat rewrite V293_sched_snapshot_roundtrip by assumption.
 assert((lo <=? 255)=true)as EL by(apply Nat.leb_le;cbn in *;lia).
 assert((hi <=? 255)=true)as EH by(apply Nat.leb_le;cbn in *;lia).
 assert((nc <=? 255)=true)as EN by(apply Nat.leb_le;cbn in *;lia).
 assert((nest <=? 255)=true)as ED by(apply Nat.leb_le;cbn in *;lia).
 assert((locked <=? 255)=true)as EK by(apply Nat.leb_le;cbn in *;lia).
 rewrite EL,EH,EN,ED,EK;reflexivity.
Qed.
Lemma V293_exit_decode_bounded : forall lg x,
 V293_exit_decode lg=Some x -> V293_exit_snapshot_bounded x.
Proof.
 intros lg x.
 unfold V293_exit_decode.
 destruct lg as [ | a lg ];[discriminate| ];
 destruct a as [isr|is|ie|cs|hid|v|l|llv|led|lec|tasks|events|aop];try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | a l ];[discriminate| ];destruct a;try discriminate.
 destruct l as [ | old l ];[discriminate| ];destruct l as [ | token l ];[discriminate| ];
 destruct l as [ | value l ];[discriminate| ];destruct l;try discriminate.
 destruct lg as [ | a lg ];[discriminate| ];destruct a;try discriminate.
 destruct lg as [ | a lg ];[discriminate| ];destruct a;try discriminate.
 destruct lg as [ | a lg ];[discriminate| ];destruct a;try discriminate.
 destruct lg;try discriminate.
 match goal with |- (if ?b then _ else _)=_ -> _ => destruct b eqn:B end;[ |discriminate].
 intro E;inversion E;subst x;unfold V293_exit_snapshot_bounded;cbn.
 repeat rewrite Bool.andb_true_iff in B.
 repeat rewrite Nat.ltb_lt in B;tauto.
Qed.
Definition V293_exit_select
 (resource:V293_exit_snapshot -> tid -> addrval -> asrt) lg t address : asrt :=
 match V293_exit_decode lg with Some x=>resource x t address | None=>Afalse end.
Lemma V293_exit_select_good : forall resource,
 (forall x t address,GoodFunAsrt(resource x t address)) ->
 forall lg t address,GoodFunAsrt(V293_exit_select resource lg t address).
Proof.
 intros resource G lg t address;unfold V293_exit_select.
 destruct(V293_exit_decode lg);[apply G|exact I].
Qed.
Lemma V293_exit_select_encoded : forall resource x t,
 V293_exit_snapshot_bounded x ->
 V293_exit_select resource(V293_exit_encode x)t=resource x t.
Proof.
 intros;unfold V293_exit_select;rewrite V293_exit_codec_roundtrip by assumption;reflexivity.
Qed.

Section PhysicalResources.
Variables unmap group rows high:var.
Variables bt bg br bh:block.
Variable li:LocalInv.
Variable tp:type.
Variables bp bo bcur bcounter bn bl:block.
(* Neither continuations nor assertions can be packed into logicvar.
   Their good/local obligations are retained, not encoded or assumed away. *)
Variable output:V293_exit_snapshot -> tid -> asrt.
Variable switch_post:V293_exit_snapshot -> tid -> addrval -> asrt.
Definition V293_exit_snapshot_pre x t := V293_exit_physical_pre
 unmap group rows high bt bg br bh(V293_xlo x)(V293_xhi x)li t(V293_xaop x)
 tp bp bo(V293_xentries x)(V293_xtasks x)bcur bcounter bn bl(V293_xcurrent x)
 (V293_xnest x)(V293_xlocked x)(V293_xold x)(V293_xcounter x).
Definition V293_exit_snapshot_entry x t :=
 V293_saved_pointer_resource(V293_xaop x)(Vint32 Int.zero)(V293_exit_snapshot_pre x t).
Definition V293_exit_snapshot_acquired x t := V293_exit_acquired
 unmap group rows high bt bg br bh(V293_xlo x)(V293_xhi x)li t(V293_xaop x)
 tp bp bo(V293_xentries x)(V293_xtasks x)bcur bcounter bn bl(V293_xcurrent x)
 (V293_xnest x)(V293_xlocked x)(V293_xold x)(V293_xcounter x)(V293_xtoken x).
Definition V293_exit_snapshot_leaving x t := V293_exit_leaving
 unmap group rows high bt bg br bh(V293_xlo x)(V293_xhi x)li t(V293_xaop x)
 tp bp bo(V293_xentries x)(V293_xtasks x)bcur bcounter bn bl(V293_xcurrent x)
 (V293_xnest x)(V293_xlocked x)(V293_xold x)(V293_xcounter x)(V293_xtoken x)(switch_post x t).
Definition V293_exit_snapshot_restored x t :=
 V293_saved_pointer_resource(V293_xaop x)(V293_xvalue x)(output x t).
Variable Hli:GoodLInvAsrt li.
Variable OG:forall x t,GoodFunAsrt(output x t).
Variable SG:forall x t address,GoodFunAsrt(switch_post x t address).
Lemma V293_exit_snapshot_entry_good : forall x t address,
 GoodFunAsrt(V293_exit_snapshot_entry x t address).
Proof.
 intros;apply V293_saved_pointer_resource_good;unfold V293_exit_snapshot_pre;
 apply V293_exit_physical_pre_good;exact Hli.
Qed.
Lemma V293_exit_snapshot_acquired_good : forall x t address,
 GoodFunAsrt(V293_exit_snapshot_acquired x t address).
Proof. intros;apply V293_exit_acquired_good;exact Hli. Qed.
Lemma V293_exit_snapshot_leaving_good : forall x t address,
 GoodFunAsrt(V293_exit_snapshot_leaving x t address).
Proof. intros;apply V293_exit_leaving_good;[exact Hli|apply SG]. Qed.
Lemma V293_exit_snapshot_restored_good : forall x t address,
 GoodFunAsrt(V293_exit_snapshot_restored x t address).
Proof. intros;apply V293_saved_pointer_resource_good;apply OG. Qed.
End PhysicalResources.

Section EncodedBuilder.
Variables unmap group rows high:var.
Variables bt bg br bh:block.
Variable li:LocalInv.
Variable tp:type.
Variables bp bo bcur bcounter bn bl:block.
Variable Out:V293_exit_snapshot -> tid -> asrt.
Variable Sw:V293_exit_snapshot -> tid -> addrval -> asrt.
Variable Hli:GoodLInvAsrt li.
Variable OG:forall x t,GoodFunAsrt(Out x t).
Variable SG:forall x t address,GoodFunAsrt(Sw x t address).
Let entryS:=V293_exit_snapshot_entry unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl.
Let acquiredS:=V293_exit_snapshot_acquired unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl.
Let leavingS:=V293_exit_snapshot_leaving unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl Sw.
Let restoredS:=V293_exit_snapshot_restored Out.
Let entryF:=V293_exit_select entryS.
Let acquiredF:=V293_exit_select acquiredS.
Let leavingF:=V293_exit_select leavingS.
Let restoredF:=V293_exit_select restoredS.
Let FEG:forall lg t address,GoodFunAsrt(entryF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_entry_good;exact Hli. Qed.
Let FAG:forall lg t address,GoodFunAsrt(acquiredF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_acquired_good;exact Hli. Qed.
Let FLG:forall lg t address,GoodFunAsrt(leavingF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_leaving_good;assumption. Qed.
Let FRG:forall lg t address,GoodFunAsrt(restoredF lg t address).
Proof. apply V293_exit_select_good;apply V293_exit_snapshot_restored_good;exact OG. Qed.
Variables table target current counter nesting lock running:var.
Variable extra:asrt.
Variable run:nat.
Variable brun:block.
Variables lo hi nc nest locked:nat.
Variables old token value:val.
Variable c:int32.
Variable aop:spec_code.
Variable entries:list val.
Variable tasks:TcbMod.map.
Variable tid:Modules.tid.
Let snapshot:=V293_mk_exit_snapshot lo hi nc nest locked c old token value entries tasks aop.
Let shared:=V293_exit_snapshot_pre unmap group rows high bt bg br bh li tp bp bo bcur bcounter bn bl snapshot tid.
Let output:=Out snapshot tid.
Let switch_post:=Sw snapshot tid.
Let B_external_pre := V293_exit_builder_external_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_external_post := V293_exit_builder_external_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_fpre := V293_exit_builder_fpre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_fpost := V293_exit_builder_fpost table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_pre := V293_exit_builder_pre table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared extra run.
Let B_post := V293_exit_builder_post table target current counter nesting lock running tp bp bo bcur bcounter bn bl brun aop shared output extra run.
Let B_frame := V293_exit_builder_frame table high target current counter nesting lock running tp bp bo bcur bcounter bn bl brun extra run.
Let acquired := V293_exit_acquired unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let leaving := V293_exit_leaving unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.
Let tail := V293_exit_physical_tail unmap group rows high bt bg br bh lo hi li tid aop
 tp bp bo entries tasks bcur bcounter bn bl nc.

Theorem V293_OSIntExit_encoded_builder_contract : forall P f Spec sd I saved vl lg pre post
 sched_id enter exit int_switch
 (GP:GoodFunAsrt B_external_pre)
 (GQ:forall result,GoodFunAsrt(B_external_post result)),
 table<>saved -> high<>saved -> target<>saved -> current<>saved ->
 counter<>saved -> nesting<>saved -> lock<>saved -> running<>saved ->
 run<256 -> lo<256 -> hi<256 -> (exists p,V293_bitmap_ready lo hi p) ->
 nc<256 -> nest<256 -> locked<256 -> V293_bitmap_tasks lo hi tasks ->
 V293_priority_table entries tasks -> GoodFrm extra ->
 (output ==> CurLINV li tid) ->
 (forall bs,switch_post(bs,Int.zero) ==> CurLINV li tid) ->
 (run=1 -> Spec sched_id=Some(V293_sched_fpre unmap group rows high bt bg br bh li Hli,
  V293_sched_fpost unmap group rows high bt bg br bh li Hli,(Tvoid,nil))) ->
 (run=1 -> Spec enter=Some(V293_indexed_pointer_fpre entryF FEG,
  V293_indexed_pointer_fpost acquiredF FAG,(Tvoid,[Tptr Tint32]))) ->
 (run=1 -> Spec exit=Some(V293_indexed_pointer_fpre leavingF FLG,
  V293_indexed_pointer_fpost restoredF FRG,(Tvoid,[Tptr Tint32]))) ->
 (forall bs,run=1 -> V293_exit_depth nest=0 -> locked=0 ->
  V293_ready_select lo hi(V293_ready_group lo hi)<>nc ->
  InfRules Spec sd li I
   (fun result => [|result=None|] ** V293_exit_body_post run aop shared (V293_saved_pointer_resource aop value output) saved bs
     (B_frame saved)) Afalse
   ((tail(V293_exit_depth nest)locked(Int.add c Int.one) ** PV(bs,Int.zero)@Tint32|->token) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))
   (scall int_switch nil)
   (switch_post(bs,Int.zero) **
    (Alvarenv saved Tint32(bs,0%Z) ** (B_frame saved)))tid) ->
 P f=Some(V293_OSIntExit_function running nesting lock saved table high target current counter
  sched_id enter exit int_switch) ->
 Some pre=BuildPreI P f vl lg(B_fpre GP)tid ->
 Some post=BuildRetI P f vl lg(B_fpost GQ)tid ->
 InfRules Spec sd li I post Afalse pre
  (V293_OSIntExit_body running nesting lock saved table high target current counter
    sched_id enter exit int_switch) Afalse tid.
Proof.
 intros P f Spec sd I saved vl lg pre post sched_id enter exit int_switch GP GQ
 T H G C K N L R Hrun Hlo Hhi Hr Hnc Hn Hl Hb Htable F OL SL Lookup Enter Exit Call Body Pre Post.
 assert(Bound:V293_exit_snapshot_bounded snapshot)by(repeat split;assumption).
 eapply V293_OSIntExit_indexed_builder_contract
 with(unmap:=unmap)(group:=group)(rows:=rows)(lo:=lo)(hi:=hi)(nc:=nc)
 (bt:=bt)(bg:=bg)(br:=br)(bh:=bh)(entries:=entries)(tasks:=tasks)
 (shared:=shared)(output:=output)(aop:=aop)(run:=run)(extra:=extra)
 (entryF:=entryF)(acquiredF:=acquiredF)(leavingF:=leavingF)(restoredF:=restoredF)
 (FEG:=FEG)(FAG:=FAG)(FLG:=FLG)(FRG:=FRG)
 (enter_lg:=V293_exit_encode snapshot)(exit_lg:=V293_exit_encode snapshot)
 (P:=P)(f:=f)(vl:=vl)(lg:=lg)(GP:=GP)(GQ:=GQ)(Hli:=Hli)
 (token:=token)(old:=old)(c:=c)(nest:=nest)(locked:=locked)
 (switch_post:=switch_post)(value:=value);try eassumption.
 - unfold shared,V293_exit_snapshot_pre;apply V293_exit_physical_pre_local.
 - intros _;unfold entryF;rewrite V293_exit_select_encoded by exact Bound;reflexivity.
 - intros _;unfold acquiredF;rewrite V293_exit_select_encoded by exact Bound;reflexivity.
 - intros _;unfold leavingF;rewrite V293_exit_select_encoded by exact Bound;reflexivity.
 - intros _;unfold restoredF;rewrite V293_exit_select_encoded by exact Bound;reflexivity.
Qed.
End EncodedBuilder.
