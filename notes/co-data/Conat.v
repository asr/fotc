Require Import Unicode.Utf8.

CoInductive Conat : Set :=
  | cozero : Conat
  | cosucc : Conat → Conat.

(* Reference Manual. Version 8.4pl3, §1.3.3: Notice that no principle of *)
(* induction is derived from the definition of a co-inductive type, since *)
(* such principles only make sense for inductive ones. For co-inductive *)
(* ones, the only elimination principle is case analysis. *)

CoFixpoint infty : Conat := cosucc infty.

Fixpoint nat2conat (n : nat) : Conat :=
match n with
  | O    => cozero
  | S n' => cosucc (nat2conat n')
end.

(* CoFixpoint conat2nat (n : Conat) : nat := *)
(* match n with *)
(*   | cozero    => 0 *)
(*   | cosucc n' => S ( conat2nat n') *)
(* end. *)

(* Error: *)
(* Recursive definition of conat2nat is ill-formed. *)
(* In environment *)
(* conat2nat : Conat → nat *)
(* n : Conat *)
(* The codomain is "nat" *)
(* which should be a coinductive type. *)
(* Recursive definition is: *)
(* "λ n : Conat, match n with *)
(*               | cozero => 0 *)
(*               | cosucc n' => S (conat2nat n') *)
(*               end". *)
