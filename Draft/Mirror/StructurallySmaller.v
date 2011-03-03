(* Tested with Coq 8.3 *)

Require Import Coq.Unicode.Utf8.

Axiom D    : Set.
Axiom nil  : D.
Axiom cons : D → D → D.
Axiom node : D → D → D.

Inductive ListTree : D → Set :=
| nilLT  : ListTree nil
| consLT : forall (t ts : D), TreeT t → ListTree ts → ListTree (cons t ts)

with TreeT : D → Set :=
| treeT : forall (d ts : D), ListTree ts → TreeT (node d ts).

Fixpoint countT (t : D) (Tt : TreeT t) {struct Tt} : nat :=
  match Tt with
    treeT d ts LTts =>
      match LTts with
        | nilLT               => 0
        | consLT x xs Tx LTxs => countT _ (treeT d xs LTxs)
      end
  end.
