(* Domain predicate for quicksort using the Bove-Capretta method *)

Require Import Lists.List.
Require Import Unicode.Utf8.

Inductive Dqs : list nat → Prop :=
  | dnil  : Dqs nil
  | dcons : ∀ x xs,
            Dqs (filter (λ y, Nat.ltb y x) xs) →
            Dqs (filter (λ y, Nat.ltb x y) xs) →
            Dqs (x :: xs).

Check Dqs_ind.
