------------------------------------------------------------------------------
-- Formalization of the map-iterate property
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

-- The map-iterate property [1]
-- map f (iterate f x) ≡ iterate f (f ∙ x)

-- [1] Jeremy Gibbons and Graham Hutton. Proof methods for corecursive
-- programs. Fundamenta Informaticae, XX:1–14, 2005.

module Draft.MapIterate.MapIterate where

open import LTC.Base

open import LTC.Data.List using ( iterate ; map )
open import LTC.Data.Stream.Bisimilarity -- using ( _≈_ ; ≈-GFP-eq₂ ; BISI )

------------------------------------------------------------------------------

-- The map-iterate property using the first-order greatest fixed-point.
≈-map-iterate : (f x : D) → map f (iterate f x) ≈ iterate f (f ∙ x)
≈-map-iterate f x = {!!}
  -- ≈-GFP-eq₂ {map f (iterate f x)}
  --           {iterate f (f ∙ x)}
  --           ( f ∙ x
  --           , f ∙ x
  --           , map f (iterate f (f ∙ x))
  --           , iterate f ( f ∙ (f ∙ x))
  --           , refl
  --           , ≈-map-iterate f (f ∙ x)  -- Agda bug: If the option
  --                                      -- --no-termination-check is
  --                                      -- removed, this line should be
  --                                      -- in light salmon.
  --           , prf₁
  --           , prf₂
  --           )
  -- where
  --   postulate
  --     prf₁ : map f (iterate f x) ≡ f ∙ x ∷ map f (iterate f (f ∙ x))
  --   {-# ATP prove prf₁ #-}

  --   postulate
  --     prf₂ : iterate f (f ∙ x) ≡ f ∙ x ∷ iterate f (f ∙ (f ∙ x))
  --   {-# ATP prove prf₂ #-}
