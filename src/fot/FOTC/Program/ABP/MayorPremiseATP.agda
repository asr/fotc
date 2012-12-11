------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MayorPremiseATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- Although the interactive proof is easy, as expected the ATPs could not
-- prove the theorem.

-- 11 December 2012: The ATPs could not prove the theorem (240 sec).
-- postulate
--   mayorPremise' : ∀ {b fs₀ fs₁ is} → Bit b → Fair fs₀ → Fair fs₁ → Stream is →
--                   B is (transfer b fs₀ fs₁ is)
-- {-# ATP prove mayorPremise' #-}

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
  , prf

  where
  -- We got the type of prf via auto.
  postulate prf : Stream is ∧
                  Bool b ∧
                  Fair fs₀ ∧
                  Fair fs₁ ∧
                  has (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ≡
                  send · b · is ·
                  hds (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ∧
                  hbs (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ≡
                  corrupt · fs₀ ·
                  has (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ∧
                  hcs (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ≡
                  ack · b ·
                  hbs (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ∧
                  hds (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ≡
                  corrupt · fs₁ ·
                  hcs (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
                  ∧
                  transfer b fs₀ fs₁ is
                  ≡
                  out · b ·
                  hbs (send · b) (ack · b) (out · b) (corrupt · fs₀)
                  (corrupt · fs₁) is
  {-# ATP prove prf #-}
