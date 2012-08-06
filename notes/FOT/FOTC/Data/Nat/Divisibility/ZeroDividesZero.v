(* In Coq 8.4beta2 zero divides zero *)

Require Import NArith.BinNat.
Import N.

Theorem zeroDividesZero : divide 0 0.
unfold divide.
exists 123%N.
auto.
Qed.
