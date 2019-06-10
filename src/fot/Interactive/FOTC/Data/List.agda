------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.List where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.List.Type public

infixr 5 _++_

------------------------------------------------------------------------------
-- Basic functions

postulate
  length    : D → D
  length-[] : length []                ≡ zero
  length-∷  : ∀ x xs → length (x ∷ xs) ≡ succ₁ (length xs)

postulate
  _++_  : D → D → D
  ++-[] : ∀ ys → [] ++ ys            ≡ ys
  ++-∷  : ∀ x xs ys → (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)

-- List transformations

postulate
  map    : D → D → D
  map-[] : ∀ f → map f []            ≡ []
  map-∷  : ∀ f x xs → map f (x ∷ xs) ≡ f · x ∷ map f xs

postulate
  rev    : D → D → D
  rev-[] : ∀ ys → rev [] ys            ≡ ys
  rev-∷  : ∀ x xs ys → rev (x ∷ xs) ys ≡ rev xs (x ∷ ys)

reverse : D → D
reverse xs = rev xs []

postulate
  reverse'    : D → D
  reverse'-[] : reverse' []                ≡ []
  reverse'-∷  : ∀ x xs → reverse' (x ∷ xs) ≡ reverse' xs ++ (x ∷ [])

postulate
  replicate   : D → D → D
  replicate-0 : ∀ x → replicate zero x        ≡ []
  replicate-S : ∀ n x → replicate (succ₁ n) x ≡ x ∷ replicate n x

-- Reducing lists

postulate
  foldr    : D → D → D → D
  foldr-[] : ∀ f n → foldr f n []            ≡ n
  foldr-∷  : ∀ f n x xs → foldr f n (x ∷ xs) ≡ f · x · (foldr f n xs)

-- Building lists

postulate
  iterate    : D → D → D
  iterate-eq : ∀ f x → iterate f x ≡ x ∷ iterate f (f · x)
