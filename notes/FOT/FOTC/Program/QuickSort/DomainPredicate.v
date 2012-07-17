(* Domain predicate for quicksort using the Bove-Capretta method *)

(* Tested with Coq 8.4beta2 *)

Require Import Arith.Compare_dec.
Require Import Lists.List.
Require Import Unicode.Utf8.

Definition ltb (m n : nat) : bool := leb (S m) n.

Inductive Dqs : list nat → Prop :=
  | dnil  : Dqs nil
  | dcons : ∀ x xs,
            Dqs (filter (fun y => ltb y x) xs) →
            Dqs (filter (fun y => ltb x y) xs) →
            Dqs (x :: xs).

Check Dqs_ind.
