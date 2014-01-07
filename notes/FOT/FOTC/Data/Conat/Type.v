Require Import Unicode.Utf8.

Axiom D    : Set.
Axiom zero : D.
Axiom succ : D → D.

CoInductive Conat : D → Prop :=
  | cozero : Conat zero
  | cosucc : ∀ {n}, Conat n → Conat (succ n).

Theorem Conat_out : ∀ {n}, Conat n → n = zero ∨ (∃ n', n = succ n' ∧ Conat n').
intros n Cn.
case Cn.
left.
auto.
intros n' Cn'.
right.
exists n'.
auto.
Qed.

Theorem Conat_in : ∀ {n}, n = zero ∨ (∃ n', n = succ n' ∧ Conat n') → Conat n.
intros n h.
elim h.
clear h.
intro prf.
subst.
apply cozero.
clear h.
intros h.
elim h.
clear h.
intros n' h.
elim h.
clear h.
intros prf Cn'.
subst.
apply (cosucc Cn').
Qed.

(* Theorem Conat_coind : *)
(*   ∀ (A : D → Prop), *)
(*     (∀ {n}, A n → n = zero ∨ (∃ n', n = succ n' ∧ A n')) → *)
(*     ∀ {n}, A n → Conat n. *)
(* intros A h n An. *)
(* elim (h n An). *)
(* intro prf. *)
(* subst. *)
(* apply cozero. *)
(* intro prf. *)
(* elim prf; clear prf. *)
(* intros n' prf. *)
(* elim prf; clear prf. *)
(* intros prf An'. *)
(* subst. *)
(* apply cosucc. *)

(* CoFixpoint *)
(*   Conat_coind (A : D → Prop) *)
(*               (h : ∀ n, A n → n = zero ∨ (∃ n', n = succ n' ∧ A n')) *)
(*               (n : D) (An : A n ) : Conat n := *)
(*   match h n An with *)
(*      | or_introl prf => ... *)
(*      | or_intror prf => ... *)
(*   end. *)
