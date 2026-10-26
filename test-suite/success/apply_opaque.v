(* As the meta-based unification, [apply] does not unfold constants that
   are declared opaque in the conversion oracle (e.g. with [Opaque]) to
   unify them with a term with a different head, while it still compares
   closed heads up to conversion (e.g. an opaque constant eta-convertible
   to a constructor). *)

Inductive expr := Rec (e : expr) | Lam (e : expr) | Var (n : nat).

Definition iter (f : expr) : expr := Rec (Lam f).
Global Opaque iter.

Goal exists e, Rec e = iter (Var 0).
Proof.
  eexists.
  (* [iter] is not unfolded to unify [Rec ?e] with [iter (Var 0)] *)
  Fail apply eq_refl.
  Transparent iter.
  apply eq_refl.
Qed.

Definition foo (n : nat) : nat := S n.
Global Opaque foo.

Goal exists m, foo 0 = S m.
Proof.
  eexists.
  (* The closed heads [foo] and [S] are convertible (eta) *)
  apply eq_refl.
Qed.
