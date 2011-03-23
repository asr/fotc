(* Tested with Coq 8.3 *)
(* Induction principle for N. *)

Require Import Coq.Unicode.Utf8.

Axiom D    : Set.
Axiom zero : D.
Axiom succ : D → D.

Inductive NProp : D → Prop :=
  | zNProp : NProp zero
  | sNProp : ∀ n, NProp n → NProp (succ n).

Check NProp_ind.

Inductive NSet : D → Set :=
  | zNSet : NSet zero
  | sNSet : ∀ n, NSet n → NSet (succ n).

Check NSet_rec.
Check NSet_ind.
Check NSet_rect.