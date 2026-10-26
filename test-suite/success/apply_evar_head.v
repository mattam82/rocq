(* When the conclusion of the applied lemma is an existential variable
   applied to arguments, [apply] favors second-order matching (abstracting
   the arguments in the goal) only when the existential variable is one of
   the arguments of the lemma, not when it comes from the elaboration of
   the applied term (e.g. an implicit argument), in which case first-order
   unification is used, as with the former meta-based implementation. *)

Class Comm {A B} (R : A -> A -> Prop) (f : B -> B -> A) :=
  comm x y : R (f x y) (f y x).
Arguments comm {A B R} f {_} x y.

Goal forall (f : nat -> nat -> nat) (H : Comm eq f) a b, f a b = f b a.
Proof.
  intros.
  (* The relation [R] is an implicit argument: first-order unification
     instantiates it with [eq] and the [Comm eq f] instance is found. *)
  apply (comm f).
Qed.

Goal forall (f : nat -> nat -> nat) (H : Comm eq f) a b, f a b = f b a.
Proof.
  intros.
  (* With an explicit [R], second-order matching would abstract the two
     applications of [f] and find [fun x y => y = x], first-order
     unification is still preferred when it succeeds. *)
  apply (@comm _ _ eq f _).
Qed.
