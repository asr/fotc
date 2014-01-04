Require Import Unicode.Utf8.

Axiom D     : Set.
Axiom zero  : D.
Axiom succ₁ : D → D.

CoInductive Conat : D → Prop :=
  | cozero : Conat zero
  | cosucc : ∀ {n}, Conat n → Conat (succ₁ n).

Theorem Conat_unf : ∀ {n}, Conat n → n = zero ∨ (∃ n', n = succ₁ n' ∧ Conat n').
intros n Cn.
case Cn.
left.
auto.
intros n' Cn'.
right.
exists n'.
auto.
Qed.

Theorem Conat_in : ∀ {n}, n = zero ∨ (∃ n', n = succ₁ n' ∧ Conat n') → Conat n.
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
