(* Nested recursive function are not allowed in Coq *)

(* Fixpoint nest (n : nat) : nat := *)
(* match n with *)
(*   | 0    => 0 *)
(*   | S n' => nest (nest n') *)
(* end. *)

(* Error: *)
(* Recursive definition of nest is ill-formed. *)
