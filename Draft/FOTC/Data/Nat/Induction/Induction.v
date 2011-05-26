(* Tested with Coq 8.3 *)

(* Induction principle for N. *)

Require Import Unicode.Utf8.

Axiom D    : Set.
Axiom zero : D.
Axiom succ : D → D.

Inductive NP : D → Prop :=
  | zNP : NP zero
  | sNP : ∀ n, NP n → NP (succ n).

Check NP_ind.

Inductive NS : D → Set :=
  | zNS : NS zero
  | sNS : ∀ n, NS n → NS (succ n).

Check NS_rec.
Check NS_ind.
Check NS_rect.
