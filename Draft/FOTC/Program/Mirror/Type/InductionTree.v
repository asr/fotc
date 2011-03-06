(* Tested with Coq 8.3 *)
(* Induction principle for the data types rose tree and forest *)

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

Check Tree_ind.
Check Forest_ind.