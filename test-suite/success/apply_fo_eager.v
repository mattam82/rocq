(* In [apply], first-order unification of an existential variable applied
   to arguments with a rigid term is performed eagerly, as the meta-based
   unification did, instead of being postponed: [?M ?A =?= M T] is solved
   with [A := T] when encountered, rather than with an instance coming from
   a later (convertible) type constraint. *)

Axiom M : Type -> Type.
Axiom lookup : forall {A}, nat -> M A -> option A.
Axiom map_eq : forall {A} (m1 m2 : M A),
  (forall i, lookup i m1 = lookup i m2) -> m1 = m2.

Definition T := (nat * nat)%type.

Goal forall (f : M T) (g : M (nat * nat)), f = g.
Proof.
  intros f g.
  (* The type of the equality is [M T]: [A] is instantiated with [T], not
     with [nat * nat] coming from the type of [g]. *)
  apply map_eq.
  match goal with |- forall i, @lookup T i f = @lookup T i g => idtac end.
Abort.
