------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

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
  length-∷  : ∀ d ds → length (d ∷ ds) ≡ succ₁ (length ds)
{-# ATP axiom length-[] #-}
{-# ATP axiom length-∷ #-}

postulate
  _++_  : D → D → D
  ++-[] : ∀ ds →      []       ++ ds ≡ ds
  ++-∷  : ∀ d ds es → (d ∷ ds) ++ es ≡ d ∷ (ds ++ es)
{-# ATP axiom ++-[] #-}
{-# ATP axiom ++-∷ #-}

-- List transformations

postulate
  -- NB. The function map is not a higher-order function.
  map    : D → D → D
  map-[] : ∀ f →      map f []       ≡ []
  map-∷  : ∀ f d ds → map f (d ∷ ds) ≡ f · d ∷ map f ds
{-# ATP axiom map-[] #-}
{-# ATP axiom map-∷ #-}

postulate
  rev    : D → D → D
  rev-[] : ∀ es →      rev []       es ≡ es
  rev-∷  : ∀ d ds es → rev (d ∷ ds) es ≡ rev ds (d ∷ es)
{-# ATP axiom rev-[] #-}
{-# ATP axiom rev-∷ #-}

reverse : D → D
reverse ds = rev ds []
{-# ATP definition reverse #-}

postulate
  replicate   : D → D → D
  replicate-0 : ∀ d →   replicate zero     d  ≡ []
  replicate-S : ∀ d e → replicate (succ₁ e) d ≡ d ∷ replicate e d
{-# ATP axiom replicate-0 #-}
{-# ATP axiom replicate-S #-}

-- Reducing lists

postulate
  -- NB. The function foldr is not a higher-order function.
  foldr    : D → D → D → D
  foldr-[] : ∀ f n  →     foldr f n []       ≡ n
  foldr-∷  : ∀ f n d ds → foldr f n (d ∷ ds) ≡ f · d · (foldr f n ds)
{-# ATP axiom foldr-[] #-}
{-# ATP axiom foldr-∷ #-}

-- Building lists

postulate
  -- NB. The function iterate is not a higher-order function.
  iterate    : D → D → D
  iterate-eq : ∀ f x → iterate f x ≡ x ∷ iterate f (f · x)
{-# ATP axiom iterate-eq #-}
