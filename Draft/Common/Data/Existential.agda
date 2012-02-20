-----------------------------------------------------------------------------
-- Existential elimination
-----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 19 February 2012.

module Existential where

-----------------------------------------------------------------------------

postulate
  D : Set

module ∃₁ where
  -- Type theoretical version

  -- We add 3 to the fixities of the standard library.
  infixr 7 _,_

  -- The existential quantifier type on D.
  data ∃ (P : D → Set) : Set where
    _,_ : (x : D) → P x → ∃ P

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  -- The existential elimination.
  ∃-proj₁ : ∀ {P} → ∃ P → D
  ∃-proj₁ (x , _) = x

  ∃-proj₂ : ∀ {P} → (p : ∃ P) → P (∃-proj₁ p)
  ∃-proj₂ (_ , Px) = Px

  -- Some examples

  -- The order of quantifiers of the same sort is irrelevant.
  ∃-ord : {P² : D → D → Set} → (∃[ x ] ∃[ y ] P² x y) → (∃[ y ] ∃[ x ] P² x y)
  ∃-ord (x , y , h) = y , x , h

-----------------------------------------------------------------------------

module ∃₂ where
  -- FOL version

  -- We add 3 to the fixities of the standard library.
  infixr 7 _,_

  -- The existential quantifier type on D.
  data ∃ (P : D → Set) : Set where
    _,_ : (x : D) → P x → ∃ P

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  -- FOL existential elimination
  --     ∃x.P(x)   P(x) → Q
  --  ------------------------
  --             Q
  ∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
  ∃-elim (x , p) h = h x p

  -- Some examples

  -- The order of quantifiers of the same sort is irrelevant.
  ∃-ord : {P² : D → D → Set} → (∃[ x ] ∃[ y ] P² x y) → (∃[ y ] ∃[ x ] P² x y)
  ∃-ord h = ∃-elim h (λ x h₁ → ∃-elim h₁ (λ y prf → y , x , prf))

  -- A proof non-FOL valid
  non-FOL : {P : D → Set} → ∃ P → D
  non-FOL h = ∃-elim h (λ x _ → x)

-----------------------------------------------------------------------------

module ∃₃ where
  -- A different version from the FOL existential introduction
  --      P(x)
  --  ------------
  --     ∃x.P(x)

  -- The existential quantifier type on D.
  data ∃ (P : D → Set) : Set where
    ∃-intro : ((x : D) → P x) → ∃ P

  -- Sugar syntax for the existential quantifier.
  syntax ∃ (λ x → e) = ∃[ x ] e

  postulate d : D

  -- FOL existential elimination.
  -- NB. It is neccesary that D ≠ ∅.
  ∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
  ∃-elim (∃-intro h₁) h₂ = h₂ d (h₁ d)

  -- Some examples

  -- Impossible
  -- thm : {P : D → Set} → ∃[ x ] P x → ∃[ y ] P y
  -- thm h = ∃-elim h (λ x prf → {!!})
