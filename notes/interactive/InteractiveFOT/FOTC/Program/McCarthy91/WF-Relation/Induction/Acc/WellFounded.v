(* Well-founded induction on the relation MCR *)

Require Import Inverse_Image.
Require Import Unicode.Utf8.
Require Import Wf_nat.

Definition fnMCR (n : nat) := 101 - n.

Definition MCR (m n : nat) := fnMCR m < fnMCR n.

Definition wfMCR : well_founded MCR :=
  wf_inverse_image nat nat lt fnMCR lt_wf.

Definition wfiMCR :
  ∀ P : nat → Set,
  (∀ n : nat, (∀ m : nat, MCR m n → P m) → P n) →
  ∀ n : nat, P n :=
well_founded_induction wfMCR.
