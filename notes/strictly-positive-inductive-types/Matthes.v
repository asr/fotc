Require Import Unicode.Utf8.

Inductive tree (A : Set) : Set :=
|  nil_tree : tree A
|  branch   : A → tree A.

(* Error: Non strictly positive occurrence of "cont" in "((cont A → A) → *)
(*  A) → cont A". *)

(* Inductive cont (A : Set) : Set := *)
(* | nil_cont : cont A *)
(* | c       : ((cont A → A) → A) → cont A. *)

(* Error: Non strictly positive occurrence of "Tree" in "(tree Tree → *)
(*  Tree) → Tree". *)

(* Inductive Tree : Set := *)
(* | nil_Tree  : Tree *)
(* | branch_Tree : (tree(Tree) → Tree) → Tree. *)
