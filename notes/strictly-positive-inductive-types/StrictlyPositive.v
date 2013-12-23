Require Import Unicode.Utf8.

(****************************************************************************)
(* Parametric stability constraint (Coq'Art, p. 378). *)

(* Error: Last occurrence of "T" must have "A" as 1st argument in "∀ B
: Set, T B". *)

(* Inductive T (A : Set) : Type := c : ∀ B : Set, T B. *)

(****************************************************************************)
(* Head type constraint (Coq'Art, section 14.1.2.1). *)

(* (* Error: Non strictly positive occurrence of "T" in "T (T nat)". *) *)
(* Inductive T : Set → Set := c : T (T nat). *)

(****************************************************************************)
(* Strictly positive constraints (Coq'Art, section 14.1.2). *)

(* Error: Non strictly positive occurrence of "T" in "(T → T) → T". *)
(* Inductive T : Set := c : (T → T) → T. *)

(****************************************************************************)
(* Universe constraints (Coq'Art, section 14.1.2.3). *)

(* Error: Large non-propositional inductive types must be in Type. *)
(* Record group : Set := *)
(*   { A : Set; *)
(*     op : A → A → A; *)
(*     e  : A *)
(*   }. *)

(* Check Build_group. *)

Inductive Id1 (A : Type) : Type → Type := refl1 : Id1 A A.
Inductive Id2 (A : Set)  : Set → Set   := refl2 : Id2 A A.
Inductive Id3 (A : Prop) : Prop → Prop := refl3 : Id3 A A.

Inductive A : Set → Set := c : A nat.
