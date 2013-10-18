(* Definition of mutual inductive predicates *)

Require Import Unicode.Utf8.

Axiom D    : Set.
Axiom zero : D.
Axiom succ : D → D.

Inductive Even : D → Prop :=
| ezero : Even zero
| esucc : ∀ {n}, Odd n → Even (succ n)

with Odd : D → Prop :=
| osucc : ∀ {n}, Even n → Odd (succ n).

(* From Coq'Art: The Coq system generates induction principles that do
not cover the mutual structure of these types (p. 401). *)

Check Even_ind.
Check Odd_ind.

Scheme Even_mutual_ind :=
  Minimality for Even Sort Prop
with Odd_mutual_ind :=
  Minimality for Odd Sort Prop.

Check Even_mutual_ind.
Check Odd_mutual_ind.
