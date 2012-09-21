------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List where

-- We add 3 to the fixities of the standard library.
infixr 8 _++_

open import FOTC.Base
open FOTC.Base.BList
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
  ++-[] : ∀ ys →      []       ++ ys ≡ ys
  ++-∷  : ∀ x xs ys → (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)
{-# ATP axiom ++-[] ++-∷ #-}

-- List transformations

postulate
  map    : D → D → D
  map-[] : ∀ f →      map f []       ≡ []
  map-∷  : ∀ f x xs → map f (x ∷ xs) ≡ f · x ∷ map f xs
{-# ATP axiom map-[] map-∷ #-}

postulate
  rev    : D → D → D
  rev-[] : ∀ ys →      rev []       ys ≡ ys
  rev-∷  : ∀ x xs ys → rev (x ∷ xs) ys ≡ rev xs (x ∷ ys)
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
  foldr    : D → D → D → D
  foldr-[] : ∀ f n  →     foldr f n []       ≡ n
  foldr-∷  : ∀ f n x xs → foldr f n (x ∷ xs) ≡ f · x · (foldr f n xs)
{-# ATP axiom foldr-[] foldr-∷ #-}

-- Building lists

postulate
  iterate    : D → D → D
  iterate-eq : ∀ f x → iterate f x ≡ x ∷ iterate f (f · x)
{-# ATP axiom iterate-eq #-}
