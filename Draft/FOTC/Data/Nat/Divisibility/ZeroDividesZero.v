(* In Coq 8.3pl4 zero divides zero *)

(* The relation the divisibility is defined by *)

(* Inductive Zdivide (a b:Z) : Prop := *)
(*     Zdivide_intro : forall q:Z, b = q * a -> Zdivide a b. *)

(* Notation "( a | b )" := (Zdivide a b) (at level 0) : Z_scope. *)

Require Import Znumtheory.
(* Open Scope Z_scope. *)

Theorem zeroDividesZero : (0 | 0).
apply Zdivide_intro with 123.
simpl.
trivial.
Qed.
