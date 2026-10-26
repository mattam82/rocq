(* As with the meta-based unification, [apply] does not unify two terms
   without existential variables that are not convertible, even if
   unfolding a local definition would expose an existential variable that
   could be instantiated: [z] below is not unified with [y]. *)

Goal forall (y : nat), True.
Proof.
  intros y.
  refine (let z : nat := _ in _).
  Fail (assert (z = y) by apply eq_refl).
  Fail (assert (z = y) by reflexivity).
  (* An explicit instantiation works *)
  assert (z = y) by (unfold z; apply eq_refl).
  exact I.
Qed.
