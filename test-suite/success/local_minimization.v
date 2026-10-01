From Corelib Require Import ListDef.
Set Local Minimization.
Set Printing Universes.
Set Debug "univMinim".
Set Debug "univMinim_each".
About map.
Set Debug "unification".
Set Debug "ustate".
Set Printing All.
Check fun l : list nat => map (fun x => x + 1) l.