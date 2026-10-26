(* [apply] fails when an argument of the lemma that only appears in its
   conclusion is not instantiated by the unification with the goal, unless
   the flag "Legacy Apply Dependency" is set, in which case such arguments
   are left as existential variables (shelved when they appear in other
   goals, new goals otherwise), as with the former meta-based
   implementation. *)

Axiom Q : nat -> Prop.
Axiom foo : forall n, Q (0 * n).

Goal Q 0.
Proof.
  (* [n] only appears in the conclusion of [foo]: unifying it with [Q 0]
     succeeds by reduction without instantiating [n]. *)
  Fail apply foo.
  (* It has to be given explicitly, or [eapply] has to be used. *)
  apply foo with (n := 0).
Qed.

Goal Q 0.
Proof.
  Set Legacy Apply Dependency.
  (* [n] is left as a (shelved) existential variable, as with eapply *)
  apply foo.
  Unshelve.
  exact 0.
Qed.

(* Arguments that get unified with existing existential variables of the goal
   are allowed in both modes: the former implementation turned the
   corresponding metas into existential variables. *)

Axiom le : nat -> nat -> Prop.
Axiom length_le : forall (f : nat -> nat) (l : nat), le (f l) l.

Goal exists n m, le n m.
Proof.
  eexists; eexists.
  apply length_le.
  Unshelve.
  all: first [ exact 0 | exact (fun x => x) ].
Qed.
