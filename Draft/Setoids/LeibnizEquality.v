(* Tested with Coq 8.3pl2 *)

Require Import Unicode.Utf8.

(* There is no difference if we use Prop, Set or Type in the
definitions *)

(* The identity type *)
Inductive Id {A : Type} (x : A) : A → Type :=
  refl : Id x x.

(* Leibniz equality (see [1, sec. 5.1.3]) *)

(* [1] Zhaohui Luo. Computation and Reasoning. A Type Theory for *)
(*     Computer Science. Oxford University Press, 1994. *)

Definition Leq {A : Type} (x y : A) : Type :=
  forall (P : A → Type), P x → P y.

(****************************************************************************)
(* Leibniz's equality and the identity type *)

(* "In the presence of a type of propositions "Prop" one can also *)
(* define propositional equality by Leibniz's principle." [2, p. 4] *)

(* [2] Martin Hofmman. Extensional concepts in intensional type *)
(*     theory. PhD thesis, University of Edinburgh, 1995 *)

Theorem id2leq :
  forall {A : Type} (x y : A), Id x y → Leq x y.
compute.
intros A x y H.
destruct H.
auto.
Qed.

Theorem leq2id :
  forall {A : Type} (x y : A), Leq x y → Id x y.
compute.
intros A x y H.
apply H.
apply refl.
Qed.
