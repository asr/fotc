------------------------------------------------------------------------------
-- FOTC combinators for lists, colists, streams, etc.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Base.List where

open import FOTC.Base

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/List.agda).
infixr 8 _∷_

------------------------------------------------------------------------------
-- List constants.
postulate [] cons head tail null : D  -- FOTC partial lists.

-- Definitions
abstract
  _∷_  : D → D → D
  x ∷ xs = cons · x · xs
  -- {-# ATP definition _∷_ #-}

  head₁ : D → D
  head₁ xs = head · xs
  -- {-# ATP definition head₁ #-}

  tail₁ : D → D
  tail₁ xs = tail · xs
  -- {-# ATP definition tail₁ #-}

  null₁ : D → D
  null₁ xs = null · xs
  -- {-# ATP definition null₁ #-}

------------------------------------------------------------------------------
-- Conversion rules

-- Conversion rules for null.
-- null-[] :          null · []              ≡ true
-- null-∷  : ∀ x xs → null · (cons · x · xs) ≡ false
postulate
  null-[] : null₁ []                ≡ true
  null-∷  : ∀ x xs → null₁ (x ∷ xs) ≡ false

-- Conversion rule for head.
-- head-∷ : ∀ x xs → head · (cons · x · xs) ≡ x
postulate head-∷ : ∀ x xs → head₁ (x ∷ xs) ≡ x
{-# ATP axiom head-∷ #-}

-- Conversion rule for tail.
-- tail-∷ : ∀ x xs → tail · (cons · x · xs) ≡ xs
postulate tail-∷ : ∀ x xs → tail₁ (x ∷ xs) ≡ xs
{-# ATP axiom tail-∷ #-}

------------------------------------------------------------------------------
-- Discrimination rules

-- postulate []≢cons : ∀ {x xs} → [] ≢ cons · x · xs
postulate []≢cons : ∀ {x xs} → [] ≢ x ∷ xs
