Require Import Unicode.Utf8.

CoInductive Conat : Type :=
  | zero : Conat
  | succ : Conat → Conat.

CoFixpoint infty : Conat := succ infty.

Fixpoint fromNat (n : nat) : Conat :=
match n with
  | O    => zero
  | S n' => succ (fromNat n')
end.

(* CoFixpoint fromConat (n : Conat) : nat := *)
(* match n with *)
(*   | zero    => 0 *)
(*   | succ n' => S ( fromConat n') *)
(* end. *)
