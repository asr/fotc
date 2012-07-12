------------------------------------------------------------------------------
-- Testing Agda internal terms: Pi _ (NoAns _ _)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module AgdaInternalTerms.PiNoAbsTerm where

postulate
  D   : Set
  A ⊥ : Set
  N   : D → Set
  _≡_ : D → D → Set

-- The following axiom uses the internal Agda term @Pi _ (NoAns _ _)@.
postulate foo : (x : D) → A
{-# ATP axiom foo #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate bar : A → A
{-# ATP prove bar #-}
