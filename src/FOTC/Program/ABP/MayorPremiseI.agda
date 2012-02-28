------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MayorPremiseI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

mayorPremise : ∀ {b fs₀ fs₁ is} →
               Bit b → Fair fs₀ → Fair fs₁ → Stream is →
               is B abptransfer b fs₀ fs₁ is
mayorPremise {b} {fs₀} {fs₁} {is} Bb Ffs₀ Ffs₁ Sis =
  ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $
  Sis
  , Bb
  , Ffs₀
  , Ffs₁
  , has-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hbs-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hcs-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hds-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀) (corrupt · fs₁) is
  , trans (abptransfer-eq b fs₀ fs₁ is)
          (transfer-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · fs₀)
                       (corrupt · fs₁) is)
