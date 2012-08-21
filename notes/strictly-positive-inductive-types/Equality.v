(* See the Agda version. *)

Require Import Unicode.Utf8.

Inductive Id1 (A : Type) : Type → Type := refl1 : Id1 A A.
Inductive Id2 (A : Set)  : Set → Set   := refl2 : Id2 A A.
Inductive Id3 (A : Prop) : Prop → Prop := refl3 : Id3 A A.
