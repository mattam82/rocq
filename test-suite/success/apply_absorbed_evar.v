(* An existential variable coming from the elaboration of the applied term
   (here the implicit argument [f]), applied to arguments of the lemma, is
   only unified first-order with the goal by [apply]/[eapply], as the former
   meta-based implementation did: it is not solved as a constant function
   when facing a variable. *)

Axiom y : nat.
Axiom foo : forall {f : nat -> nat} (x : nat), f x = y.

Goal forall (g : nat -> nat) (z : nat), g z = y.
Proof.
  intros g z.
  (* First-order unification: [f := g], [x := z] *)
  apply foo.
Qed.

Goal forall (z : nat), z = y.
Proof.
  intros z.
  (* [?f ?x] is not unified with [z] by making [f] a constant function. *)
  Fail eapply foo.
  (* The constant function has to be given explicitly. *)
  apply (foo (f := fun _ => z) 0).
Qed.
