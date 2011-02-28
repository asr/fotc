(* Well-founded induction on the relation MCR *)
(* Tested with Coq 8.3 *)

Require Import Coq.Unicode.Utf8.
Require Import Wf_nat.
Require Import Inverse_Image.

Definition MCR_f (n : nat) := 101 - n.

Definition MCR (m n : nat) := MCR_f m < MCR_f n.

Definition MCR_wf : well_founded MCR :=
wf_inverse_image nat nat lt MCR_f lt_wf.

Definition MCR_wfind :
  ∀ P : nat → Set,
  (∀ n : nat, (∀ m : nat, MCR m n → P m) → P n) →
  ∀ n : nat, P n :=
well_founded_induction MCR_wf.
