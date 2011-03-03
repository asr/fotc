(* Well-founded induction on the relation MCR *)
(* Tested with Coq 8.3 *)

Require Import Coq.Unicode.Utf8.
Require Import Wf_nat.
Require Import Inverse_Image.

Definition fn_MCR (n : nat) := 101 - n.

Definition MCR (m n : nat) := fn_MCR m < fn_MCR n.

Definition wf_MCR : well_founded MCR :=
wf_inverse_image nat nat lt fn_MCR lt_wf.

Definition wfInd_MCR :
  ∀ P : nat → Set,
  (∀ n : nat, (∀ m : nat, MCR m n → P m) → P n) →
  ∀ n : nat, P n :=
well_founded_induction wf_MCR.
