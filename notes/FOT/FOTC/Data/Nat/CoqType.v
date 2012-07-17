(* Tested with Coq 8.4beta2 *)

(* Induction principle for N. *)

Require Import Unicode.Utf8.

Axiom D     : Set.
Axiom zero  : D.
Axiom succ₁ : D → D.

Inductive NP : D → Prop :=
  | zNP : NP zero
  | sNP : ∀ n, NP n → NP (succ₁ n).

Check NP_ind.

Inductive NS : D → Set :=
  | zNS : NS zero
  | sNS : ∀ n, NS n → NS (succ₁ n).

Check NS_ind.
Check NS_rec.
Check NS_rect.
