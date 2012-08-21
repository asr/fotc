(* The map-iterate property *)

(* Tested with Coq 8.4. *)

(* From: Eduardo Giménez Pierre Castéran. A Tutorial on [Co-]Inductive
Types in Coq. May 1998 -- August 17, 2007. *)

Require Import Unicode.Utf8.

CoInductive Stream (A : Type) : Type := Cons : A → Stream A → Stream A.

Definition head {A : Type}(s : Stream A) :=
  match s with Cons a s' => a end.

Definition tail {A : Type}(s : Stream A) :=
  match s with Cons a s' => s' end.

CoFixpoint iterate {A : Type}(f : A → A)(a : A) : Stream A :=
  Cons A a (iterate f (f a)).

CoFixpoint map {A B : Type}(f : A → B)(s : Stream A) : Stream B:=
  match s with Cons a tl => Cons B (f a) (map f tl) end.

CoInductive EqSt {A : Type} : Stream A → Stream A → Prop :=
  eqst : ∀ s1 s2 : Stream A,
         head s1 = head s2 →
         EqSt (tail s1) (tail s2) →
         EqSt s1 s2.

Section Parks_Principle.
Variable A        : Type.
Variable R        : Stream A → Stream A → Prop.
Hypothesis bisim1 : ∀ s1 s2 : Stream A, R s1 s2 → head s1 = head s2.
Hypothesis bisim2 : ∀ s1 s2 : Stream A, R s1 s2 → R (tail s1) (tail s2).

CoFixpoint park_ppl (s1 s2 : Stream A)(p : R s1 s2) : EqSt s1 s2 :=
  eqst s1 s2
       (bisim1 s1 s2 p)
       (park_ppl (tail s1) (tail s2) (bisim2 s1 s2 p)).

End Parks_Principle.

Theorem map_iterate {A : Type}(f : A → A)(x : A) :
                    EqSt (iterate f (f x)) (map f (iterate f x)).
Proof.
apply park_ppl with
  (R := λ s1 s2, ∃ x : A, s1 = iterate f (f x) ∧ s2 = map f (iterate f x)).
intros s1 s2 (x0, (eqs1, eqs2));
  rewrite eqs1; rewrite eqs2; reflexivity.
intros s1 s2 (x0, (eqs1, eqs2)).
exists (f x0); split;
  [rewrite eqs1 | rewrite eqs2]; reflexivity.
exists x; split; reflexivity.
Qed.
