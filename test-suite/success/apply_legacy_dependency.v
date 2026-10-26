(* [apply] fails when an argument of the lemma that only appears in its
   conclusion is not instantiated by the unification with the goal, unless
   the flag "Legacy Apply Dependency" is set, in which case such arguments
   are left as existential variables (shelved when they appear in other
   goals, new goals otherwise), as with the former meta-based
   implementation. *)

Axiom le : nat -> nat -> Prop.
Axiom length_le : forall (f : nat -> nat) (l : nat), le (f l) l.

Goal exists n m, le n m.
Proof.
  eexists; eexists.
  (* [f] and [l] only appear in the conclusion of [length_le]: unifying it
     with [le ?n ?m] instantiates [?n] and [?m] but not [f] and [l]. *)
  Fail apply length_le.
  (* They have to be given explicitly, or [eapply] has to be used. *)
  apply length_le with (f := fun x => x) (l := 0).
Qed.

Goal exists n m, le n m.
Proof.
  eexists; eexists.
  Set Legacy Apply Dependency.
  (* [f] and [l] are left as (shelved) existential variables, as with eapply *)
  apply length_le.
  Unshelve.
  all: first [ exact 0 | exact (fun x => x) ].
Qed.

Unset Legacy Apply Dependency.

Axiom T : Type. Axiom app : T -> T -> T. Axiom Perm : T -> T -> Prop.
Axiom Perm_refl : forall l, Perm l l.
Axiom Perm_app_tail : forall l l' tl, Perm l l' -> Perm (app l tl) (app l' tl).
Axiom Perm_trans : forall a b c, Perm a b -> Perm b c -> Perm a c.
Axiom a b : T.

Goal Perm (app a b) (app a b).
Proof.
  eapply Perm_trans.
  (* [l'] is not instantiated by unifying [Perm (app ?l ?tl) (app ?l' ?tl)]
     with [Perm (app a b) ?mid]. *)
  Fail apply Perm_app_tail.
  Set Legacy Apply Dependency.
  apply Perm_app_tail.
  (* [l'] is shelved, the premise [Perm a ?l'] and the second goal of
     [Perm_trans] remain *)
  all: apply Perm_refl.
Qed.

Unset Legacy Apply Dependency.

(* The flag only concerns arguments appearing in the conclusion: arguments
   appearing in a premise still have to be instantiated. *)
Axiom trans : forall n m p, le n m -> le m p -> le n p.

Goal exists n p, le n p.
Proof.
  eexists; eexists.
  Fail apply trans.
  Set Legacy Apply Dependency.
  Fail apply trans.
  Unset Legacy Apply Dependency.
  eapply trans; apply (length_le (fun x => x) 0).
Qed.
