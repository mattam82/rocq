(* [apply ... in] uses higher-order unification to find the instances of
   the variables of the lemma only when the type of the hypothesis contains
   no existential variable (as the former meta-based unification refused to
   abstract over terms containing metas). *)

Axiom nth_error : list nat -> unit.
Axiom nth_error_value_length : forall (xs:list nat), nth_error xs = tt -> True.
Axiom type : Set.

Lemma foo (eta_ident_cps : forall {T : type -> Type} {t} (f : forall t', T t'), T t) : True.
Proof.
(* Would require [T := fun _ => nth_error ?xs = tt] (see also bugs/bug_19794.v) *)
Fail apply nth_error_value_length in eta_ident_cps.
exact I.
Qed.

Axiom up : Type -> Type. Axiom back : forall A, up A -> A. Axiom forth : forall A, A -> up A.
Axiom backforth : forall (A : Type) (P : A -> Type) (a : A), P (back A (forth A a)) -> P a.

Lemma bar (B : Type) (f : B -> Type) (b : B) (j : f (back B (forth B b))) : f b.
Proof.
(* [P] is found by second-order matching, abstracting [back B (forth B b)] *)
apply backforth in j.
exact j.
Qed.
