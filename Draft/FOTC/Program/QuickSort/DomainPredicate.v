(* Domain predicate for quicksort using the Bove-Capretta method *)

(* Tested with Coq 8.3 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Unicode.Utf8.

Definition ltb (m n : nat) : bool := leb (S m) n.

Inductive Dqs : list nat → Prop :=
  | dnil  : Dqs nil
  | dcons : ∀ x xs,
             Dqs (filter (fun y => ltb y x) xs) →
             Dqs (filter (fun y => ltb x y) xs) →
             Dqs (x :: xs).

Check Dqs_ind.
