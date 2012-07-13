------------------------------------------------------------------------------
-- Testing Agda internal terms: Def
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module AgdaInternalTerms.DefTerm1 where

------------------------------------------------------------------------------

postulate
  D   : Set
  _≡_ : D → D → Set
  P   : D → Set
  a   : D

-- A definition with one argument.
postulate foo : P a
{-# ATP axiom foo #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate bar : ∀ d → d ≡ d
{-# ATP prove bar #-}
