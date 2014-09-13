------------------------------------------------------------------------------
-- Twice funcion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Twice where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base

------------------------------------------------------------------------------

module HigherOrder where

  -- We cannot translate this function as a definition because it is
  -- higher-order.
  twice : (D → D) → D → D
  twice f x = f (f x)
  -- {-# ATP definition twice #-}

  postulate twice-succ : ∀ n → twice succ₁ n ≡ succ₁ (succ₁ n)
  -- {-# ATP prove twice-succ #-}

module FirstOrderAxiom where

  postulate
    twice    : D → D → D
    twice-eq : ∀ f x → twice f x ≡ f · (f · x)
  {-# ATP axiom twice-eq #-}

  twice-succI : ∀ n → twice succ n ≡ succ · (succ · n)
  twice-succI n = twice succ n      ≡⟨ twice-eq succ n ⟩
                  succ · (succ · n) ∎

  postulate twice-succATP : ∀ n → twice succ n ≡ succ · (succ · n)
  {-# ATP prove twice-succATP #-}

module FirstOrderDefinition where

  twice : D → D → D
  twice f x = f · (f · x)
  {-# ATP definition twice #-}

  twice-succI : ∀ n → twice succ n ≡ succ · (succ · n)
  twice-succI n = refl

  postulate twice-succATP : ∀ n → twice succ n ≡ succ · (succ · n)
  {-# ATP prove twice-succATP #-}
