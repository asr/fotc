Require Import Unicode.Utf8.

Set Implicit Arguments.

CoInductive Stream' (A : Set) : Set :=
  cons : A → Stream' A → Stream' A.

CoFixpoint alter : Stream' bool := cons true (cons false alter).

CoFixpoint mapS {A B : Set}(f : A → B)(xs : Stream' A) : Stream' B :=
  match xs with
    | cons x xs' => cons (f x) (mapS f xs')
  end.

(* Recursive definition of alter' is ill-formed. *)
(* Unguarded recursive call *)
(* CoFixpoint alter' : Stream' bool := cons true (mapS negb alter'). *)
