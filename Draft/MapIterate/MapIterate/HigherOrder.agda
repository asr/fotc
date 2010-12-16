------------------------------------------------------------------------------
-- Formalization of the map-iterate property (using the higher-order
-- bisimilar relation)
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

-- The map-iterate property [1]
-- map f (iterate f x) ≡ iterate f (f · x)

-- [1] Jeremy Gibbons and Graham Hutton. Proof methods for corecursive
-- programs. Fundamenta Informaticae, XX:1–14, 2005.

module Draft.MapIterate.MapIterate.HigherOrder where

open import LTC.Base

open import Draft.Bisimulation.HigherOrder using ( _≈_ ; GFP-eq₂ ; BISI )

open import LTC.Data.List using ( iterate ; map )

------------------------------------------------------------------------------

-- The map and iterate producen using the higher-order greatest fixed-point.
≈-map-iterate : (f x : D) → map f (iterate f x) ≈ iterate f (f · x)
≈-map-iterate f x =
  GFP-eq₂ BISI
          (map f (iterate f x))
          (iterate f (f · x))
          ( f · x
          , f · x
          , map f (iterate f (f · x))
          , iterate f ( f · (f · x))
          , refl
          , ≈-map-iterate f (f · x)  -- Agda bug: If the option
                                     -- --no-termination-check is
                                     -- removed, this line should be
                                     -- in light salmon.
          , prf₁
          , prf₂
          )
  where
    postulate
      prf₁ : map f (iterate f x) ≡ f · x ∷ map f (iterate f (f · x))
      prf₂ : iterate f (f · x) ≡ f · x ∷ iterate f (f · (f · x))
