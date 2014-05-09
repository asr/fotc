(* The HALO paper states the property *)
(* ∀ x . f x ≠ ones  (1) *)
(* shouldn't be proved because it is a non-admissible one. *)

Require Import Unicode.Utf8.

Set Implicit Arguments.

CoInductive Conat : Set :=
| zero : Conat
| succ : Conat → Conat.

CoFixpoint inf : Conat := succ inf.

CoInductive Colist (A : Set) : Set :=
| nil  : Colist A
| cons : A → Colist A → Colist A.

Local Notation "x ∷ xs" := (cons x xs) (at level 60, right associativity).

CoFixpoint ones : Colist Conat := succ zero ∷ ones.

(* CoInductive Stream (A : Set) : Set := cons : A → Stream A → Stream A. *)

(* CoFixpoint zeros : Stream Conat := zero ∷ zeros. *)

(* Definition head (A : Set)(xs : Stream A) := *)
(*   match xs with a ∷ xs' => a end. *)

(* Definition tail (A : Set)(xs : Stream A) := *)
(*   match xs with a ∷ xs' => xs' end. *)

CoInductive EqColist (A : Set) : Colist A → Colist A → Prop :=
  | eqNil :  ∀ xs xs' : Colist A,
             xs = nil A →
             xs' = nil A →
             EqColist xs xs'

  | eqCons : ∀ x : A, ∀ xs xs' : Colist A,
             EqColist xs xs' →
             EqColist (x ∷ xs) (x ∷ xs').

CoFixpoint f (n : Conat) : Colist Conat :=
match n with
  | zero    => zero ∷ nil Conat
  | succ n' => succ zero ∷ f n'
end.

(* The property (1). *)
(* Theorem thm (n : Conat) : f n <> ones. *)
