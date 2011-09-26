(* Definition of FOTC streams using Coq coinductive stuff *)

(* Tested with Coq 8.3pl2 *)

Require Import Unicode.Utf8.

Theorem sim {A : Set}{x y : A} : x = y → y = x.
intro h.
destruct h.
auto.
Qed.

Theorem subst {A : Set}(P : A → Set){x y : A} : x = y → P x → P y.
intros h Px.
destruct h.
auto.
Qed.

Inductive D : Set :=
  | consL : D → D → D.

Infix "::" := consL (at level 60, right associativity).

CoInductive Stream : D → Set :=
 | consS : forall (x : D)(xs : D), Stream xs → Stream (x :: xs).

CoFixpoint Stream_gfp₂
  (P : D → Prop)
  (h : forall (xs : D)(Pxs : P xs), {x' : D & {xs' : D | P xs' ∧ xs = x' :: xs'}})
  (xs : D)
  (Pxs : P xs) : Stream xs :=

  match h xs Pxs with
    | existS x' h1 => match h1 with
                        | exist xs' h2 => match h2 with
                                            | conj c1 c2 =>
                                                subst Stream (sim c2) (consS x' xs' (Stream_gfp₂ P h xs' c1))
                                          end
                      end
  end.
