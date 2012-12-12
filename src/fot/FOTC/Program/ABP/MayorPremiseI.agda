------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MayorPremiseI where

open import FOTC.Base
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

mayorPremise : ∀ {b os₀ os₁ is} →
               Bit b → Fair os₀ → Fair os₁ → Stream is →
               B is (transfer b os₀ os₁ is)
mayorPremise {b} {os₀} {os₁} {is} Bb Fos₀ Fos₁ Sis =
  b
  , os₀
  , os₁
  , has (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hbs (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hcs (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hds (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , Sis
  , Bb
  , Fos₀
  , Fos₁
  , has-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hbs-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hcs-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , hds-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
  , trans (transfer-eq b os₀ os₁ is)
          (genTransfer-eq (send · b) (ack · b) (out · b) (corrupt · os₀)
                          (corrupt · os₁) is)
