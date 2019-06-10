Require Import Unicode.Utf8.

Axiom D    : Set.
Axiom nil  : D.
Axiom cons : D → D → D.
Axiom node : D → D → D.

Inductive Forest : D → Set :=
| nilF  : Forest nil
| consF : ∀ t ts, TreeT t → Forest ts → Forest (cons t ts)

with TreeT : D → Set :=
| treeT : ∀ d ts, Forest ts → TreeT (node d ts).

Fixpoint countT (t : D) (Tt : TreeT t) {struct Tt} : nat :=
  match Tt with
    treeT d ts Fts =>
      match Fts with
        | nilF              => O
        | consF x xs Tx Fxs => countT _ Tx
        (* | consF x xs Tx Fxs => countT _ (treeT d xs Fxs) *)
      end
  end.
