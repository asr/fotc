Require Import Unicode.Utf8.
Require Import Lists.List.

Theorem true_false : true ≠ false.
intro H.
discriminate H.
Qed.

Theorem O_S : ∀ n, O ≠ S n.
intros n H.
discriminate H.
Qed.

Theorem nil_cons: ∀ (A : Set)(x : A)(xs : list A),  nil ≠ x :: xs.
intros A x xs H.
discriminate H.
Qed.
