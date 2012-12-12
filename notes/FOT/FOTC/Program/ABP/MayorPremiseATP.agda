------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.ABP.MayorPremiseATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

postulate
  mayorPremise : ∀ {b os₀ os₁ is} → Bit b → Fair os₀ → Fair os₁ → Stream is →
                 B is (transfer b os₀ os₁ is)
-- {-# ATP prove mayorPremise #-}
