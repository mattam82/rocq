(* [apply ... in] does not use higher-order unification by default
   (see also bugs/bug_19794.v), [apply_ho ... in] does. *)

Axiom nth_error : list nat -> unit.
Axiom nth_error_value_length : forall (xs:list nat), nth_error xs = tt -> True.

Axiom type : Set.

Lemma foo (eta_ident_cps : forall {T : type -> Type} {t} (f : forall t', T t'), T t) : True.
Proof.
Fail apply nth_error_value_length in eta_ident_cps.
apply_ho nth_error_value_length in eta_ident_cps.
exact eta_ident_cps.
Abort.

Lemma bar (H : forall (P : nat -> Prop) (n : nat), P n -> P (S n)) (h : 0 = 0) : True.
Proof.
(* First-order unification is enough here *)
apply H in h.
eapply_ho H in h.
exact I.
Qed.
