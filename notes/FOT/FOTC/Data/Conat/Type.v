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

CoFixpoint Conat_coind (A : D → Prop)
                       (h : ∀ n, A n → n = zero ∨ (∃ n', n = succ n' ∧ A n'))
                       {n : D} (An : A n) : Conat n :=
match h n An with
  | or_introl prf => match eq_sym prf with eq_refl => cozero end
  | or_intror prf =>
    match prf with ex_intro n' Pn' =>
      match Pn' with conj prf' An' =>
        match eq_sym prf' with eq_refl =>
          cosucc (Conat_coind A h An')
        end
      end
    end
end.
