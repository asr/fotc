------------------------------------------------------------------------------
-- Using setoids for formalizing the FOTC
------------------------------------------------------------------------------

-- Tested with the development version of Agda on 23 March 2012.

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

------------------------------------------------------------------------------

module PeterEquality where

  -- We add 3 to the fixities of the standard library.
  infixl 9 _·_  -- The symbol is '\cdot'.

  data D : Set where
    K S : D
    _·_ : D → D → D

  -- From Peter's slides
  -- http://www.cse.chalmers.se/~peterd/slides/Amagasaki.pdf

  infix 7 _≡_

  data _≡_ : D → D → Set where
    refl  : ∀ x →                                       x ≡ x
    sym   : ∀ {x y} → x ≡ y →                           y ≡ x
    trans : ∀ {x y z} → x ≡ y → y ≡ z →                 x ≡ z
    cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ · y₁ ≡ x₂ · y₂
    Kax   : ∀ x y →                            K · x · y  ≡ x
    Sax   : ∀ x y z →                      S · x · y · z  ≡ x · z · (y · z)

  -- It seems we cannot define the identity elimination using the setoid
  -- equality.
  --
  -- subst : ∀ {x y} (A : D → Set) → x ≡ y → A x → A y

module PeterD where

  -- We add 3 to the fixities of the standard library.
  infixl 9 _·_  -- The symbol is '\cdot'.

  data D : Set where
    zero succ true false : D
    _·_             : D → D → D
    loop            : D

  data _≡_ (x : D) : D → Set where
    refl : x ≡ x

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A refl Ax = Ax

  data N : D → Set where
    zN :               N zero
    sN : ∀ {n} → N n → N (succ · n)

  -- 2012-03-23: Why the inductive structure makes 0 + 0 different
  -- from 0? How to define _+_ ?

------------------------------------------------------------------------------

module LeibnizEquality where

  -- We add 3 to the fixities of the standard library.
  infixl 9 _·_  -- The symbol is '\cdot'.

  data D : Set where
    K S : D
    _·_ : D → D → D

  -- (Barthe et al. 2003, p. 262) use the Leibniz equality when
  -- they talk about setoids.

  -- • Gilles Barthe, Venanzio Capretta, and Olivier Pons. Setoids in
  --   type theory. Journal of Functional Programming, 13(2):261–293,
  --   2003

  -- Using the Leibniz equality
  -- (Adapted from Agda/examples/lib/Logic/Leibniz.agda)

  infix 7 _≡_

  _≡_ : D → D → Set₁
  x ≡ y = (A : D → Set) → A x → A y

  -- we can prove the setoids properties

  refl : ∀ x → x ≡ x
  refl x A Ax = Ax

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} x≡y A Ay = x≡y (λ z → A z → A x) (λ Ax → Ax) Ay

  trans : ∀ x y z → x ≡ y → y ≡ z → x ≡ z
  trans x y z x≡y y≡z A Ax = y≡z A (x≡y A Ax)

  -- and the identity elimination

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A x≡y = x≡y A

  -- but it seems we cannot prove the congruency

  -- cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → x₁ · y₁ ≡ x₂ · y₂
  -- cong x₁≡x₂ y₁≡y₂ A Ax₁y₁ = {!!}
