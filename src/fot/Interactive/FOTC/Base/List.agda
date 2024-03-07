------------------------------------------------------------------------------
-- FOTC combinators for lists, colists, streams, etc.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Base.List where

open import Interactive.FOTC.Base

infixr 5 _∷_

------------------------------------------------------------------------------
-- List constants.
postulate [] cons head tail null : D  -- FOTC partial lists.

-- Definitions
abstract
  _∷_  : D → D → D
  x ∷ xs = cons · x · xs

  head₁ : D → D
  head₁ xs = head · xs

  tail₁ : D → D
  tail₁ xs = tail · xs

  null₁ : D → D
  null₁ xs = null · xs

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

-- Conversion rule for tail.
-- tail-∷ : ∀ x xs → tail · (cons · x · xs) ≡ xs
postulate tail-∷ : ∀ x xs → tail₁ (x ∷ xs) ≡ xs

------------------------------------------------------------------------------
-- Discrimination rules

-- postulate []≢cons : ∀ {x xs} → [] ≢ cons · x · xs
postulate []≢cons : ∀ {x xs} → [] ≢ x ∷ xs