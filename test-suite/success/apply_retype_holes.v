(* The types of the new goals created by [apply] are recomputed from the
   type of the applied term, as the meta-based refiner did: when the term
   is given with a cast to a type that is only convertible to its type, the
   goals get the types coming from the term (here
   [pointwise_relation nat iff f g]) rather than the ones of the cast
   ([myrel f g]). This matters e.g. for [simple apply (_ : Proper (equiv ==> R) f)]
   where the [Equiv] instance is resolved by typeclass resolution to a
   [pointwise_relation], on which Ltac matching is then possible. *)

From Corelib Require Import Morphisms.

Axiom P : (nat -> Prop) -> Prop.
Axiom P_proper : Proper (pointwise_relation nat iff ==> iff) P.

Definition myrel : (nat -> Prop) -> (nat -> Prop) -> Prop := pointwise_relation nat iff.

Goal forall f g : nat -> Prop, iff (P f) (P g).
Proof.
  intros.
  simple apply (P_proper : Proper (myrel ==> iff) P).
  match goal with |- pointwise_relation _ _ _ _ => idtac end.
Abort.
