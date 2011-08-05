------------------------------------------------------------------------------
-- Using setoids to formalize the FOTC
------------------------------------------------------------------------------

{-
From Peter emails:

At that time I was considering an inductive data type D and an
inductively defined equality on D. But I think what we are doing now
is better.

For = : The reason is that with the propositional identity we have
identity elimination which lets us replace equals by equals. We cannot
do that in general if we have setoid equality.

For D: the reason why I prefer to postulate D is that we have no use
for the inductive structure of D, and this inductive structure would
make e g 0 + 0 different from 0. So in that case we need setoid
equality.
-}

module FOTC where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------

data D : Set where
  K S : D
  _·_ : D → D → D

module PeterEquality where

  -- From Peter's slides
  -- http://www.cse.chalmers.se/~peterd/slides/Amagasaki.pdf

  infix 7 _≐_

  data _≐_ : D → D → Set where
    refl  : ∀ x →                                       x ≐ x
    sym   : ∀ {x y} → x ≐ y →                           y ≐ x
    trans : ∀ {x y z} → x ≐ y → y ≐ z →                 x ≐ z
    cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≐ x₂ → y₁ ≐ y₂ → x₁ · y₁ ≐ x₂ · y₂
    Kax   : ∀ x y →                            K · x · y  ≐ x
    Sax   : ∀ x y z →                      S · x · y · z  ≐ x · z · (y · z)

  -- It seems we cannot define the identity elimination using the setoid
  -- equality
  -- subst : ∀ {x y} (P : D → Set) → x ≐ y → P x → P y
  -- subst P x≐y Px = {!!}

------------------------------------------------------------------------------

module LeibnizEquality where

  -- Barthe et al. [*, p. 262] use the Leibniz equality when
  -- they talk about setoids.

  -- [*] Gilles Barthe, Venanzio Capretta, and Olivier Pons. Setoids in
  -- type theory. Journal of Functional Programming, 13(2):261–293, 2003

  -- Using the Leibniz equality
  -- (Adapted from Agda/examples/lib/Logic/Leibniz.agda)

  infix 7 _≐_

  _≐_ : D → D → Set₁
  x ≐ y = (P : D → Set) → P x → P y

  -- We can proof the setoids properties

  ≐-refl : ∀ x → x ≐ x
  ≐-refl x P Px = Px

  ≐-sym : ∀ {x y} → x ≐ y → y ≐ x
  ≐-sym {x} x≐y P Py = x≐y (λ z → P z → P x) (λ Px → Px) Py

  ≐-trans : ∀ x y z → x ≐ y → y ≐ z → x ≐ z
  ≐-trans x y z x≐y y≐z P Px = y≐z P (x≐y P Px)

  -- and the identity elimination

  ≐-subst : ∀ (P : D → Set) {x y} → x ≐ y → P x → P y
  ≐-subst P x≐y = x≐y P

  -- but it seems we cannot prove the congruency

  -- ≐-cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≐ x₂ → y₁ ≐ y₂ → x₁ · y₁ ≐ x₂ · y₂
  -- ≐-cong x₁≐x₂ y₁≐y₂ P Px₁y₁ = {!!}
