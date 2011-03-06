(* Tested with Coq 8.3 *)
(* Induction principle for the data types Tree and ListTree *)

Require Import Coq.Unicode.Utf8.

Axiom D    : Set.
Axiom nil  : D.
Axiom cons : D → D → D.
Axiom node : D → D → D.

Inductive ListTree : D → Prop :=
| nilLT  : ListTree nil
| consLT : forall (t ts : D), Tree t → ListTree ts → ListTree (cons t ts)

with Tree : D → Prop :=
| treeT : forall (d ts : D), ListTree ts → Tree (node d ts).

Check Tree_ind.
Check ListTree_ind.