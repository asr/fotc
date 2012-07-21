------------------------------------------------------------------------------
-- Testing the Agda pragma --universal-quantified-functions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Fails because requires the above pragma.

module PragmaRequired3 where

postulate
  D   : Set
  fix : (D → D) → D
  _≡_ : D → D → Set

postulate fix-f : (f : D → D) → fix f ≡ f (fix  f)
{-# ATP axiom fix-f #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
