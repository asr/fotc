------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

module LTC.Data.List where

open import LTC.Base

infixr 5 _++_

------------------------------------------------------------------------------
-- The LTC list type.
open import LTC.Data.List.Type public

------------------------------------------------------------------------------
-- Basic functions

postulate
  length    : D → D
  length-[] :              length []       ≡ zero
  length-∷  : (d ds : D) → length (d ∷ ds) ≡ succ (length ds)
{-# ATP axiom length-[] #-}
{-# ATP axiom length-∷ #-}

postulate
  _++_  : D → D → D
  ++-[] : (ds : D) →      []       ++ ds ≡ ds
  ++-∷  : (d ds es : D) → (d ∷ ds) ++ es ≡ d ∷ (ds ++ es)
{-# ATP axiom ++-[] #-}
{-# ATP axiom ++-∷ #-}

-- List transformations

postulate
  map    : D → D → D
  map-[] : (f : D) →      map f []       ≡ []
  map-∷  : (f d ds : D) → map f (d ∷ ds) ≡ f ∙ d ∷ map f ds
{-# ATP axiom map-[] #-}
{-# ATP axiom map-∷ #-}

postulate
  -- Behavior: rev xs ys = reverse xs ++ ys
  rev    : D → D → D
  rev-[] : (es : D) →      rev []       es ≡ es
  rev-∷  : (d ds es : D) → rev (d ∷ ds) es ≡ rev ds (d ∷ es)
{-# ATP axiom rev-[] #-}
{-# ATP axiom rev-∷ #-}

reverse : D → D
reverse ds = rev ds []
{-# ATP definition reverse #-}

postulate
  replicate   : D → D → D
  replicate-0 : (d : D) →   replicate zero     d ≡ []
  replicate-S : (d e : D) → replicate (succ e) d ≡ d ∷ replicate e d
{-# ATP axiom replicate-0 #-}
{-# ATP axiom replicate-S #-}

-- Reducing lists

postulate
  foldr    : D → D → D → D
  foldr-[] : (f n : D) →      foldr f n []       ≡ n
  foldr-∷  : (f n d ds : D) → foldr f n (d ∷ ds) ≡ f ∙ d ∙ (foldr f n ds)
{-# ATP axiom foldr-[] #-}
{-# ATP axiom foldr-∷ #-}

-- Building lists

postulate
  iterate    : D → D → D
  iterate-eq : (f x : D) → iterate f x ≡ x ∷ iterate f (f ∙ x)
{-# ATP axiom iterate-eq #-}
