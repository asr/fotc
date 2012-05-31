(* In Coq 8.3pl4, gcd 0 0 = 0 *)

Require Import ZArith.Znumtheory.
Require Import ZArith.BinInt.

Theorem gcd00 : Zgcd Z0 Z0 = Z0.
trivial.
Qed.
