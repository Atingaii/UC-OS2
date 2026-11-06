(* Place the existing returned core in the ORIGINAL framework partition.
   Enabled return: shared INV owns the core. Disabled return: RDYINV does.
   No new invariant, memory, abstract slot, or execution rule is introduced. *)
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Local Open Scope nat_scope.

Section ReturnPartition.
Variables br bg bp : block.
Variable target : var.
Variable tp : type.
Variable cells : list(addr*type).
Variable cache : block.
Let G := V293_ready_current_inv br bg bp target tp cells cache.
Let C := V293_ready_current_core br bg bp target tp cells cache.

Lemma V293_return_enabled_INV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(true,si,ci),O,op)|=C ->
 (ge,le,M,ir,(true,si,ci),O,op)|=INV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 change((ge,le,M,ir,(true,si,ci),O,op)|=Aemp **(inv_ieon G \\// inv_ieoff G)).
 apply astar_l_aemp_intro;left;unfold inv_ieon.
 apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_current_noisr_core;exact Core.
Qed.

Lemma V293_return_disabled_INV_empty : forall ge le ir si ci op,
 (forall i,ir i=false) ->gettopis si<=INUM ->
 (ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=INV G.
Proof.
 intros ge le ir si ci op Clear Bound.
 change((ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=
 Aemp **(inv_ieon G \\// inv_ieoff G)).
 apply astar_l_aemp_intro;right;unfold inv_ieoff.
 apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 exists(gettopis si);apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
 split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[repeat split;reflexivity| ].
 destruct(proj1(Nat.lt_eq_cases (gettopis si) INUM)Bound)as[Less|Equal].
 - left;apply astar_l_apure_intro;[ |exact Less].
   unfold invlth_isr;replace(gettopis si+1)with(S(gettopis si))by lia.
   eapply V293_shared_clear_noisr_close;[exact Clear| ].
   apply V293_current_noisr_tail;split;reflexivity.
 - right;split;[exact Equal|split;reflexivity].
Qed.

Lemma V293_return_disabled_SWINV : forall ge le M ir si ci O op,
 (forall i,ir i=false) -> (ge,le,M,ir,(false,si,ci),O,op)|=C ->
 (ge,le,M,ir,(false,si,ci),O,op)|=SWINV G.
Proof.
 intros ge le M ir si ci O op Clear Core.
 assert(Flags:(ge,le,(emp:mem),ir,(false,si,ci),(emp:osabst),op)|=isrclr **Aie false).
 { apply sat_split';exists(emp:mem);exists(emp:mem);exists(emp:osabst);exists(emp:osabst).
   split;[apply map_join_emp| ];split;[apply map_join_emp| ];split;[ |repeat split;reflexivity].
   exists ir;split;[repeat split;reflexivity|split;[exact Clear|split;reflexivity]]. }
 unfold SWINV;apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[exact Flags| ].
 exists(gettopis si);apply sat_split';exists(emp:mem);exists M;exists(emp:osabst);exists O.
 split;[apply map_join_comm;apply map_join_emp| ];
 split;[apply map_join_comm;apply map_join_emp| ];split;[repeat split;reflexivity| ].
 unfold invlth_isr;rewrite Nat.sub_0_r.
 eapply V293_shared_clear_noisr_close;[exact Clear| ].
 apply V293_current_noisr_core;exact Core.
Qed.

(* This is a resource partition, not a claim that both sides own the core.
   The frame R is arbitrary and is neither weakened nor absorbed by Atrue. *)
Theorem V293_current_return_invariants : forall t R ge le M ir enabled si ci O op,
 (forall i,ir i=false) -> (enabled=false ->gettopis si<=INUM) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=C **(CurTid t **R) ->
 (ge,le,M,ir,(enabled,si,ci),O,op)|=(INV G **RDYINV G t) **R.
Proof.
 intros t R ge le M ir enabled si ci O op Clear Bound Held.
 assert(Packed:(ge,le,M,ir,(enabled,si,ci),O,op)|=(C **CurTid t) **R)by(sep auto).
 apply sat_split in Packed;destruct Packed as(m1&m2&o1&o2&JM&JO&Live&Frame).
 apply sat_split';exists m1;exists m2;exists o1;exists o2.
 split;[exact JM| ];split;[exact JO| ];split;[ |exact Frame].
 destruct enabled.
 - apply sat_split in Live;destruct Live as(mc&mr&oc&orr&JM'&JO'&Core&Current).
   apply sat_split';exists mc;exists mr;exists oc;exists orr.
   split;[exact JM'| ];split;[exact JO'| ];split.
   + apply V293_return_enabled_INV;assumption.
   + left;apply sat_split';exists(emp:mem);exists mr;exists(emp:osabst);exists orr.
     split;[apply map_join_comm;apply map_join_emp| ];
     split;[apply map_join_comm;apply map_join_emp| ];split;[ |exact Current].
     split;[repeat split;reflexivity|exists ir;split;
     [repeat split;reflexivity|split;[exact Clear|split;reflexivity]]].
 - apply sat_split';exists(emp:mem);exists m1;exists(emp:osabst);exists o1.
   split;[apply map_join_comm;apply map_join_emp| ];
   split;[apply map_join_comm;apply map_join_emp| ];split.
   + apply V293_return_disabled_INV_empty;[exact Clear|apply Bound;reflexivity].
   + right;unfold SWINVt;fold(CurTid t).
     apply sat_split in Live;destruct Live as(mc&mr&oc&orr&JM'&JO'&Core&Current).
     apply sat_split';exists mc;exists mr;exists oc;exists orr.
     split;[exact JM'| ];split;[exact JO'| ];split;[ |exact Current].
     apply V293_return_disabled_SWINV;assumption.
Qed.
End ReturnPartition.
