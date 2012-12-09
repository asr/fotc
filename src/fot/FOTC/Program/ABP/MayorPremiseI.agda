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

mayorPremise : ∀ {b fs₀ fs₁ is} →
               Bit b → Fair fs₀ → Fair fs₁ → Stream is →
               B is (transfer b fs₀ fs₁ is)
mayorPremise {b} {fs₀} {fs₁} {is} Bb Ffs₀ Ffs₁ Sis =
  b
  , fs₀
  , fs₁
  , has (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hbs (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hcs (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hds (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , Sis
  , Bb
  , Ffs₀
  , Ffs₁
  , has-eq (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hbs-eq (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hcs-eq (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , hds-eq (send · b) (ack · b) (out · b) (corrupt · fs₀) (corrupt · fs₁) is
  , trans (transfer-eq b fs₀ fs₁ is)
          (genTransfer-eq (send · b) (ack · b) (out · b) (corrupt · fs₀)
                          (corrupt · fs₁) is)
