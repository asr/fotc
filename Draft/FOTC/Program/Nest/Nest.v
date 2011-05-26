(* Nested recursive function using the Bove-Capretta method *)

(* Tested with Coq 8.3pl2 *)

(* Induction-recursion is not allow in Coq *)

Require Import Unicode.Utf8.

Inductive Dom : nat → Prop :=
  | d0 : Dom 0
  | dS : ∀ x, Dom x → Dom (nest x) → Dom (S x)
with
Fixpoint nest (n : nat)(d : Dom n){struct d} : nat :=
  match d with
    | d0           => 0
    | dS x Dx Dnx  => 0
  end.
