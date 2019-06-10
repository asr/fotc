(* In Coq, gcd 0 0 = 0. *)

Require Import NArith.BinNatDef.
Import N.

Theorem gcd00 : gcd 0 0 = 0%N.
trivial.
Qed.
