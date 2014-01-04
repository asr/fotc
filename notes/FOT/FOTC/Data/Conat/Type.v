Require Import Unicode.Utf8.

Axiom D     : Set.
Axiom zero  : D.
Axiom succ₁ : D → D.

CoInductive Conat : D → Prop :=
  | cozero : Conat zero
  | cosucc : ∀ n, Conat n → Conat (succ₁ n).

Theorem Conat_unf : ∀ n, Conat n → n = zero ∨ (∃ n', n = succ₁ n' ∧ Conat n').
intro n.
intro Cn.
case Cn.
left.
auto.
intro n'.
intro Cn'.
right.
exists n'.
auto.
Qed.
