(* Tested with Coq 8.3 *)
(* The types used by the mirror function *)

Require Import Coq.Unicode.Utf8.

Axiom D    : Set.
Axiom nil  : D.
Axiom cons : D → D → D.
Axiom node : D → D → D.

Inductive Forest : D → Prop :=
| nilF  : Forest nil
| consF : forall (t ts : D), Tree t → Forest ts → Forest (cons t ts)

with Tree : D → Prop :=
| treeT : forall (d ts : D), Forest ts → Tree (node d ts).

(* From Coq'Art: The Coq system generates induction principles that do
not cover the mutual structure of these types (p. 401). *)

Check Tree_ind.
Check Forest_ind.

Scheme Tree_mutual_ind :=
  Minimality for Tree Sort Prop
with Forest_mutual_ind :=
  Minimality for Forest Sort Prop.

Check Tree_mutual_ind.
Check Forest_mutual_ind.
