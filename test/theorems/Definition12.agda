------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition12 where

infixl 9 _·_
infix  7 _≡_

postulate
  D       : Set
  _≡_     : D → D → Set
  true if : D
  _·_     : D → D → D

postulate if-true : ∀ d₁ {d₂} → if · true · d₁ · d₂ ≡ d₁
{-# ATP axiom if-true #-}

if_then_else_ : D → D → D → D
if b then d₁ else d₂ = if · b · d₁ · d₂
{-# ATP definition if_then_else_ #-}

-- We test the translation of a definition with holes.
postulate foo : ∀ d₁ d₂ → if true then d₁ else d₂ ≡ d₁
{-# ATP prove foo #-}
