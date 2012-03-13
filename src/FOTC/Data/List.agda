------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infixr 8 _++_

------------------------------------------------------------------------------
-- The FOTC list type.
open import FOTC.Data.List.Type public

------------------------------------------------------------------------------
-- Basic functions

postulate
  length    : D → D
  length-[] :          length []       ≡ zero
  length-∷  : ∀ x xs → length (x ∷ xs) ≡ succ₁ (length xs)
{-# ATP axiom length-[] length-∷ #-}

postulate
  _++_  : D → D → D
  ++-[] : ∀ xs →      []       ++ xs ≡ xs
  ++-∷  : ∀ x xs es → (x ∷ xs) ++ es ≡ x ∷ (xs ++ es)
{-# ATP axiom ++-[] ++-∷ #-}

-- List transformations

postulate
  -- NB. The function map is not a higher-order function.
  map    : D → D → D
  map-[] : ∀ f →      map f []       ≡ []
  map-∷  : ∀ f x xs → map f (x ∷ xs) ≡ f · x ∷ map f xs
{-# ATP axiom map-[] map-∷ #-}

postulate
  rev    : D → D → D
  rev-[] : ∀ es →      rev []       es ≡ es
  rev-∷  : ∀ x xs es → rev (x ∷ xs) es ≡ rev xs (x ∷ es)
{-# ATP axiom rev-[] rev-∷ #-}

reverse : D → D
reverse xs = rev xs []
{-# ATP definition reverse #-}

postulate
  replicate   : D → D → D
  replicate-0 : ∀ x →   replicate zero      x ≡ []
  replicate-S : ∀ n x → replicate (succ₁ n) x ≡ x ∷ replicate n x
{-# ATP axiom replicate-0 replicate-S #-}

-- Reducing lists

postulate
  -- NB. The function foldr is not a higher-order function.
  foldr    : D → D → D → D
  foldr-[] : ∀ f n  →     foldr f n []       ≡ n
  foldr-∷  : ∀ f n x xs → foldr f n (x ∷ xs) ≡ f · x · (foldr f n xs)
{-# ATP axiom foldr-[] foldr-∷ #-}

-- Building lists

postulate
  -- NB. The function iterate is not a higher-order function.
  iterate    : D → D → D
  iterate-eq : ∀ f x → iterate f x ≡ x ∷ iterate f (f · x)
{-# ATP axiom iterate-eq #-}
