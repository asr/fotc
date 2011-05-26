(* zero divides zero *)

(* Tested with Coq 8.3pl2 *)

(* The relation the divisibility is defined by *)

(* Inductive Zdivide (a b:Z) : Prop := *)
(*     Zdivide_intro : forall q:Z, b = q * a -> Zdivide a b. *)

(* Notation "( a | b )" := (Zdivide a b) (at level 0) : Z_scope. *)

Require Import Znumtheory.
(* Open Scope Z_scope. *)

Theorem zeroDividesZero : (0 | 0).
Proof.
apply Zdivide_intro with 0.
auto.
Qed.
