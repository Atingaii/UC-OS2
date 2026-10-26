(* Representation refinement: compare observable operations to the original
   unrestricted functions, without assuming that every such function is a mem. *)
Require Import memory memory_bound.
Local Open Scope Z_scope.

Module RawMemory.
Definition t := addr -> option HalfPermMap.B.
Definition erase (m : mem) : t := HalfPermMap.contents m.
Definition empty : t := fun _ => None.
Definition update (m : t) a v : t :=
  fun x => if HalfPermMap.dec_A x a then Some v else m x.
Definition remove (m : t) a : t :=
  fun x => if HalfPermMap.dec_A x a then None else m x.
(* Independent legacy algorithms, not calls back into the implementation. *)
Definition combine_values (v1 v2 : HalfPermMap.B) : option HalfPermMap.B :=
  match v1, v2 with
  | (false,x), (false,y) =>
      if HalfPermMap.dec_C x y then Some (true,x) else Some v1
  | _, _ => Some v1
  end.
Definition subtract_values (v1 v2 : HalfPermMap.B) : option HalfPermMap.B :=
  match v1, v2 with
  | (true,x), (false,y) =>
      if HalfPermMap.dec_C x y then Some (false,x) else None
  | _, _ => None
  end.
Definition combine (m1 m2 : t) : t := fun x =>
  match m1 x with
  | None => m2 x
  | Some b1 => match m2 x with
               | None => m1 x
               | Some b2 => combine_values b1 b2
               end
  end.
Definition subtract (m1 m2 : t) : t := fun x =>
  match m1 x with
  | None => None
  | Some b => match m2 x with
              | None => Some b
              | Some b' => subtract_values b b'
              end
  end.
Definition compatible (m1 m2 : t) : Prop := forall x,
  match m1 x, m2 x with
  | None, _ | _, None => True
  | Some (false, v1), Some (false, v2) => v1 = v2
  | _, _ => False
  end.
Fixpoint allocate (m : t) b i n : t :=
  match n with
  | O => m
  | S n' => update (allocate m b (i+1) n') (b,i) (true,Undef)
  end.
Fixpoint release (m : t) b i n : option t :=
  match n with
  | O => Some m
  | S n' => match m (b,i), release m b (i+1) n' with
            | Some (true,_), Some m' => Some (remove m' (b,i))
            | _, _ => None
            end
  end.
Fixpoint write (m : t) l (bytes : list memval) : option t :=
  match bytes with
  | nil => Some m
  | v :: rest => match l with (b,i) =>
      match m l, write m (b,i+1) rest with
      | Some (true,_), Some m' => Some (update m' l (true,v))
      | _, _ => None
      end
    end
  end.
End RawMemory.

Theorem erase_empty : RawMemory.erase (emp : mem) = RawMemory.empty.
Proof. reflexivity. Qed.
Theorem erase_get : forall (m : mem) a, get m a = RawMemory.erase m a.
Proof. reflexivity. Qed.
Theorem erase_set : forall (m : mem) a v,
  RawMemory.erase (set m a v) = RawMemory.update (RawMemory.erase m) a v.
Proof. reflexivity. Qed.
Theorem erase_del : forall (m : mem) a,
  RawMemory.erase (del m a) = RawMemory.remove (RawMemory.erase m) a.
Proof. reflexivity. Qed.
Theorem erase_merge : forall (m1 m2 : mem),
  RawMemory.erase (merge m1 m2) =
  RawMemory.combine (RawMemory.erase m1) (RawMemory.erase m2).
Proof. reflexivity. Qed.
Theorem erase_minus : forall (m1 m2 : mem),
  RawMemory.erase (minus m1 m2) =
  RawMemory.subtract (RawMemory.erase m1) (RawMemory.erase m2).
Proof. reflexivity. Qed.
Theorem erase_sig : forall a v,
  RawMemory.erase (sig a v : mem) = RawMemory.update RawMemory.empty a v.
Proof. reflexivity. Qed.

Theorem erase_join : forall (m1 m2 m : mem),
  join m1 m2 m <->
  RawMemory.compatible (RawMemory.erase m1) (RawMemory.erase m2) /\
  RawMemory.erase m = RawMemory.combine (RawMemory.erase m1) (RawMemory.erase m2).
Proof.
  intros m1 m2 m; unfold Maps.join; cbn [memMap].
  unfold HalfPermMap.join, RawMemory.compatible, RawMemory.erase.
  split; intros [Hd Heq]; split.
  - intro a; specialize (Hd a); unfold HalfPermMap.disjoint in Hd.
    destruct (m1 a) as [[p1 v1]|]; destruct (m2 a) as [[p2 v2]|];
      try destruct p1; try destruct p2; simpl in *; tauto.
  - subst m; reflexivity.
  - intro a; specialize (Hd a).
    destruct (m1 a) as [[p1 v1]|]; destruct (m2 a) as [[p2 v2]|];
      try destruct p1; try destruct p2; simpl in *; tauto.
  - apply HalfPermMap.map_ext; intro a; exact (f_equal (fun f => f a) Heq).
Qed.

Theorem erase_allocb : forall n m b i,
  RawMemory.erase (allocb m b i n) = RawMemory.allocate (RawMemory.erase m) b i n.
Proof.
  induction n; intros m b i; [reflexivity |].
  change (RawMemory.update (RawMemory.erase (allocb m b (i+1) n)) (b,i) (true,Undef) =
    RawMemory.update (RawMemory.allocate (RawMemory.erase m) b (i+1) n) (b,i) (true,Undef)).
  rewrite IHn; reflexivity.
Qed.

Theorem erase_freeb : forall n m b i,
  option_map RawMemory.erase (freeb m b i n) =
  RawMemory.release (RawMemory.erase m) b i n.
Proof.
  induction n; intros; simpl; [reflexivity |].
  rewrite <- IHn.
  cbv beta iota zeta delta [Maps.get memMap HalfPermMap.get RawMemory.erase].
  unfold offset in *.
  destruct (m (b,i)) as [[permission v]|] eqn:E;
    destruct (freeb m b (i+1) n); try destruct permission; simpl;
    unfold offset in *; try rewrite E; reflexivity.
Qed.

Theorem erase_storebytes : forall bytes m b i,
  option_map RawMemory.erase (storebytes m (b,i) bytes) =
  RawMemory.write (RawMemory.erase m) (b,i) bytes.
Proof.
  induction bytes; intros; simpl; [reflexivity |].
  rewrite <- IHbytes.
  cbv beta iota zeta delta [Maps.get memMap HalfPermMap.get RawMemory.erase].
  unfold offset in *.
  destruct (m (b,i)) as [[permission v]|] eqn:E;
    destruct (storebytes m (b,i+1) bytes); try destruct permission; simpl;
    unfold offset in *; try rewrite E; reflexivity.
Qed.

(* Non-vacuity: the type is inhabited; arbitrary finite allocations can grow. *)
Theorem memory_inhabited : exists (m : mem), m = emp.
Proof. exists HalfPermMap.emp; reflexivity. Qed.
Theorem memory_is_bounded : forall m, exists upper, blocks_below m upper.
Proof. intro m; exact (HalfPermMap.bounded m). Qed.
Theorem allocation_can_continue : forall m n i,
  exists b, fresh m b /\ exists next,
    next = allocb m b i n /\ exists b', fresh next b'.
Proof.
  intros; destruct (memory_has_fresh_block m) as [b Hb].
  exists b; split; [exact Hb |].
  exists (allocb m b i n); split; [reflexivity | apply memory_has_fresh_block].
Qed.

Definition occupied_everywhere_raw : RawMemory.t := fun _ => Some (true,Undef).
Theorem saturated_raw_not_bounded : ~ HalfPermMap.raw_bounded occupied_everywhere_raw.
Proof.
  intros [upper Hbound]; apply (Pos.lt_irrefl upper).
  apply (Hbound upper 0 (true,Undef)); reflexivity.
Qed.
Theorem saturated_raw_not_representable :
  ~ exists m, RawMemory.erase m = occupied_everywhere_raw.
Proof.
  intros [m E]; apply saturated_raw_not_bounded.
  rewrite <- E; exact (HalfPermMap.bounded m).
Qed.

(* Concrete successful operations rule out an empty-only representation. *)
Example concrete_allocation :
  get (allocb (emp : mem) 1%positive 0 1) (1%positive,0) = Some (true,Undef).
Proof. unfold allocb; apply Maps.map_get_set. Qed.
Example concrete_write :
  exists next, storebytes (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) (MNull :: nil) =
    Some next /\ get next (1%positive,0) = Some (true,MNull).
Proof.
  exists (set (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) (true,MNull)).
  split.
  - change (match get (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) with
      | Some (true,_) => Some (set (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) (true,MNull))
      | _ => None end = Some (set (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) (true,MNull))).
    rewrite Maps.map_get_sig; reflexivity.
  - apply Maps.map_get_set.
Qed.
Example concrete_release :
  exists next, freeb (sig (1%positive,0) (true,Undef) : mem) 1%positive 0 1 = Some next /\
    get next (1%positive,0) = None.
Proof.
  exists (del (sig (1%positive,0) (true,Undef) : mem) (1%positive,0)).
  split.
  - change (match get (sig (1%positive,0) (true,Undef) : mem) (1%positive,0) with
      | Some (true,_) => Some (del (sig (1%positive,0) (true,Undef) : mem) (1%positive,0))
      | _ => None end = Some (del (sig (1%positive,0) (true,Undef) : mem) (1%positive,0))).
    rewrite Maps.map_get_sig; reflexivity.
  - rewrite Maps.map_del_sem.
    cbv beta iota zeta delta [Maps.map_dec_a memMap HalfPermMap.dec_A].
    destruct (addr_eq_dec (1%positive,0) (1%positive,0)); congruence.
Qed.
Example readonly_write_rejected :
  storebytes (sig (1%positive,0) (false,Undef) : mem) (1%positive,0) (MNull :: nil) = None.
Proof.
  change (match get (sig (1%positive,0) (false,Undef) : mem) (1%positive,0) with
    | Some (true,_) => Some (set (sig (1%positive,0) (false,Undef) : mem) (1%positive,0) (true,MNull))
    | _ => None end = None).
  rewrite Maps.map_get_sig; reflexivity.
Qed.
