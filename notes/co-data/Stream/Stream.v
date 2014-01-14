Require Import Unicode.Utf8.

CoInductive Stream (A : Set) : Set := cons : A → Stream A → Stream A.

(* From (Leclerc and Paulin-Mohring 1994, p. 195). *)
CoFixpoint Stream_build {A X : Set} (h : X → (A * X)) (x : X) : Stream A :=
  match h x with pair a x' => cons A a (Stream_build h x') end.

(* From (Giménez, 1995, p. 40). *)
CoFixpoint
  Stream_corec {A X : Set} (h : X → (A * (Stream A + X))) (x : X) : Stream A :=
  match h x with
    | pair a (inl xs) => cons A a xs
    | pair a (inr x') => cons A a (Stream_corec h x')
  end.

(****************************************************************************)
(* References *)

(* Giménez, E. (1995). Codifying guarded definitions with recursive *)
(* schemes. In: Types for Proofs and Programs (TYPES ’94). Ed. by Dybjer, *)
(* P., Nordström, B. and Smith, J. Vol. 996. LNCS. Springer, pp. 39–59. *)

(* Leclerc, F. and Paulin-Mohring, C. (1994). Programming with Streams in *)
(* Coq. A case study : the Sieve of Eratosthenes. In: Types for Proofs *)
(* and Programs (TYPES ’93). Ed. by Barendregt, H. and Nipkow, *)
(* T. Vol. 806. LNCS. Springer, pp. 191–212. *)
