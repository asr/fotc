------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MayorPremiseATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- Although the interactive proof is easy, as expected the ATPs could not
-- prove the theorem.

-- 2012-02-23: The ATPs (see README.agda) do not prove the theorem (180 sec).
-- postulate
--   mayorPremise' : ∀ {b fs₀ fs₁ is} → Bit b → Fair fs₀ → Fair fs₁ → Stream is →
--                   is B abptransfer b fs₀ fs₁ is
-- {-# ATP prove mayorPremise' #-}

mayorPremise : ∀ {b fs₀ fs₁ is} →
               Bit b → Fair fs₀ → Fair fs₁ → Stream is →
               is B abptransfer b fs₀ fs₁ is
mayorPremise {b} {fs₀} {fs₁} {is} Bb Ffs₀ Ffs₁ Sis =
  ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ prf
  where
  -- We get the type of prf via auto.
  postulate prf : Stream is ∧
                    Bool b ∧
                    Fair fs₀ ∧
                    Fair fs₁ ∧
                    has (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ≡
                    abpsend · b · is ·
                    hds (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ∧
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ≡
                    corrupt · fs₀ ·
                    has (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ∧
                    hcs (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ≡
                    abpack · b ·
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ∧
                    hds (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ≡
                    corrupt · fs₁ ·
                    hcs (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
                    ∧
                    abptransfer b fs₀ fs₁ is ≡
                    abpout · b ·
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                    (corrupt · fs₁) is
  {-# ATP prove prf #-}
