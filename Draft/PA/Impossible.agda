------------------------------------------------------------------------------
-- Test the consistency of Draft.PA.Base
------------------------------------------------------------------------------

module Draft.PA.Impossible where

open import Draft.PA.Base

------------------------------------------------------------------------------

postulate
  impossible : (x₁ x₂ : PA) → x₁ ≡ x₂
{-# ATP prove impossible #-}
