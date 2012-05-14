------------------------------------------------------------------------------
-- Using setoids for formalizing the FOTC
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 14 May 2012.

{-

From Peter emails:

At that time I was considering an inductive data type D and an
inductively defined equality on D. But I think what we are doing now
is better.

For =: The reason is that with the propositional identity we have
identity elimination which lets us replace equals by equals. We cannot
do that in general if we have setoid equality.

For D: the reason why I prefer to postulate D is that we have no use
for the inductive structure of D, and this inductive structure would
make e g 0 + 0 different from 0. So in that case we need setoid
equality.

-}

module FOTC where

-- References:
--
-- • Gilles Barthe, Venanzio Capretta, and Olivier Pons. Setoids in
--   type theory. Journal of Functional Programming, 13(2):261–293,
--   2003.

------------------------------------------------------------------------------

module Setoid where

  -- From Peter's slides
  -- http://www.cse.chalmers.se/~peterd/slides/Amagasaki.pdf

  -- We add 3 to the fixities of the standard library.
  infixl 9 _·_  -- The symbol is '\cdot'.
  infix 7  _≐_

  data D : Set where
    K S : D
    _·_ : D → D → D

  -- The setoid equality.
  data _≐_ : D → D → Set where
    refl  : ∀ x →                                       x ≐ x
    sym   : ∀ {x y} → x ≐ y →                           y ≐ x
    trans : ∀ {x y z} → x ≐ y → y ≐ z →                 x ≐ z
    cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≐ x₂ → y₁ ≐ y₂ → x₁ · y₁ ≐ x₂ · y₂
    Kax   : ∀ x y →                            K · x · y  ≐ x
    Sax   : ∀ x y z →                      S · x · y · z  ≐ x · z · (y · z)

  -- The identity type.
  data _≡_ (x : D) : D → Set where
    refl : x ≡ x

  ----------------------------------------------------------------------------
  -- 14 May 2012: Using the inductive structure we cannot prove
  --
  -- K · x · y ≡ x,
  --
  -- we need the setoid equality.
  -- K-eq : ∀ {x y} → (K · x · y) ≡ x

  ----------------------------------------------------------------------------
  -- 14 May 2012. We cannot define the identity elimination using the
  -- setoid equality.
  --
  -- Adapted from Peter's email:

  -- Given
  postulate subst : (A : D → Set) → ∀ x y → x ≐ y → A x → A y

  -- you can get the instance

  subst-aux : ∀ x y → x ≐ y → x ≡ x → x ≡ y
  subst-aux x y h₁ h₂ = subst A x y h₁ refl
    where A : D → Set
          A z = x ≡ z

  -- hence you can prove

  thm : ∀ {x y} → x ≐ y → x ≡ y
  thm {x} {y} h = subst-aux x y h refl

  -- but this doesn't hold because "x ≡ y" (propositional equality)
  -- means identical expressions. We do NOT have K · x · y ≡ x.
  --
  -- The point is that ≐ is a non-trivial equivalence relation, and
  -- not all properties preserve it. However, all properties are
  -- preserved by ≡.

------------------------------------------------------------------------------

module LeibnizEquality where

  infix 7 _≡_

  data D : Set where
    K S : D
    _·_ : D → D → D

  -- (Barthe et al. 2003, p. 262) use the Leibniz equality when
  -- they talk about setoids.

  -- Using the Leibniz equality (adapted from
  -- Agda/examples/lib/Logic/Leibniz.agda)

  _≡_ : D → D → Set₁
  x ≡ y = (A : D → Set) → A x → A y

  -- we can prove the setoids properties

  refl : ∀ x → x ≡ x
  refl x A Ax = Ax

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} h A Ay = h (λ z → A z → A x) (λ Ax → Ax) Ay

  trans : ∀ x y z → x ≡ y → y ≡ z → x ≡ z
  trans x y z h₁ h₂ A Ax = h₂ A (h₁ A Ax)

  -- and the identity elimination

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A x≡y = x≡y A

  -- and the congruency

  cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ · y₁ ≡ x₂ · y₂
  cong {x₁} {x₂} {y₁} {y₂} h₁ h₂ A Ax₁x₂ =
    h₂ (λ z → A (x₂ · z)) (h₁ (λ z → A (z · y₁)) Ax₁x₂)
