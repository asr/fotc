(* Tested with Coq 8.4. *)

Require Import Unicode.Utf8.

(****************************************************************************)
(* Parametric stability constraint (Coq Art, p. 378). *)

(* Error: Last occurrence of "T" must have "A" as 1st argument in "∀ B
: Set, T B". *)

(* Inductive T (A : Set) : Type := c : ∀ B : Set, T B. *)

(****************************************************************************)
(* Strictly positive constraints (Coq Art, section 14.1.2). *)

(* Error: Non strictly positive occurrence of "T" in "T (T nat)". *)
(* Inductive T : Set → Set := c : T (T nat). *)

(* Error: Non strictly positive occurrence of "T" in "(T → T) → T". *)
(* Inductive T : Set := c : (T → T) → T. *)
