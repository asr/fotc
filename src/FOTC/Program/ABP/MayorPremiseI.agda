------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

module FOTC.Program.ABP.MayorPremiseI where

open import FOTC.Base
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

mayorPremise : ∀ {b os₀ os₁ is} →
               Bit b → Fair os₀ → Fair os₁ → Stream is →
               is B abptransfer b os₀ os₁ is
mayorPremise {b} {os₀} {os₁} {is} Bb Fos₀ Fos₁ Sis =
  b
  , os₀
  , os₁
  , has (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hcs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hds (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , Sis
  , Bb
  , Fos₀
  , Fos₁
  , has-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hbs-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hcs-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , hds-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀) (corrupt · os₁) is
  , trans (abptransfer-eq b os₀ os₁ is)
          (transfer-eq (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                       (corrupt · os₁) is)
