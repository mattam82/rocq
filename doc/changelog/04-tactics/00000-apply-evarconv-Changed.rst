- **Changed:**
  The :tacn:`apply` tactic (and its variants :tacn:`eapply`,
  :tacn:`simple apply`, :tacn:`apply` in) now uses the evar-based
  unification algorithm (the one used for elaboration) instead of the
  legacy meta-based one. Unification of the conclusion of the applied lemma
  with the goal may use higher-order unification, and the arguments
  of the lemma solved by unification are no longer subject to the
  renaming heuristics of the previous implementation (in particular,
  existential variables introduced by :tacn:`eapply` are named after the
  binders of the applied lemma).
- **Added:**
  Flag :flag:`Legacy Apply Dependency` to restore the behavior of
  :tacn:`apply` turning the arguments of the applied lemma that only appear
  in its conclusion and remain uninstantiated into new goals, instead of
  failing (`eapply` or an explicit binding can be used instead)
  (by Matthieu Sozeau, Maxime Dénès and Hugo Herbelin).
