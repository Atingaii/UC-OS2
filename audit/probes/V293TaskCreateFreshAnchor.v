(* Prospective single-factor survivor-bound ablation. No call/Hook credit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFresh.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition AnchorCells : list V293_record_cell := [((1%positive,0),Tvoid,Vundef)].
Definition AnchorMemory : mem := emp.
Definition AnchorStart (protect : bool) := Pos.max 1%positive
 (if protect then Pos.succ(V293_cells_upper AnchorCells) else 1%positive).
Definition AnchorBlocks protect := V293_create_function_blocks (AnchorStart protect) (Pos.succ (AnchorStart protect)) (Pos.succ (Pos.succ (AnchorStart protect))) (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect)))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect)))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect))))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect)))))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect))))))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect)))))))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect))))))))))) (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (AnchorStart protect)))))))))))).
Lemma AnchorBothFresh : forall protect b, In b(AnchorBlocks protect) -> fresh AnchorMemory b.
Proof. intros protect b Member l i E [v Read]. change(None=Some v) in Read. discriminate. Qed.
Lemma AnchorBothDistinct : forall protect, NoDup(AnchorBlocks protect).
Proof. intros [];unfold AnchorBlocks,AnchorStart,AnchorCells,V293_cells_upper,V293_create_function_blocks;cbn;repeat constructor;cbn;intuition congruence. Qed.
Lemma AnchorWithBound : forall a tp v, In(a,tp,v) AnchorCells -> ~In(fst a)(AnchorBlocks true).
Proof. intros [b off] tp v [E|E];[inversion E;subst|contradiction]. vm_compute. intuition discriminate. Qed.
Lemma AnchorWithoutBound : exists a tp v, In(a,tp,v) AnchorCells /\ In(fst a)(AnchorBlocks false).
Proof. exists (1%positive,0). exists Tvoid. exists Vundef. split;left;reflexivity. Qed.
Lemma AnchorZeroSize : typelen Tvoid=0%nat.
Proof. reflexivity. Qed.
Lemma AnchorZeroOwned :
 V293_wstate (emp:env) (emp:env) AnchorMemory |= V293_rdy_raw_cells AnchorCells Atrue.
Proof.
 cbn [AnchorCells V293_rdy_raw_cells].
 eapply V293_wstate_star with (m1:=(emp:mem)) (m2:=(emp:mem)).
 - apply map_join_emp.
 - split;[ |reflexivity]. exists (@nil memval). split;reflexivity.
 - exact I.
Qed.
Print Assumptions AnchorBothFresh.
Print Assumptions AnchorBothDistinct.
Print Assumptions AnchorWithBound.
Print Assumptions AnchorWithoutBound.
Print Assumptions AnchorZeroOwned.
