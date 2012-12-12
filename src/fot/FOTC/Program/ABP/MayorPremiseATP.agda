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
--   mayorPremise' : ∀ {b os₀ os₁ is} → Bit b → Fair os₀ → Fair os₁ → Stream is →
--                   B is (transfer b os₀ os₁ is)
-- {-# ATP prove mayorPremise' #-}

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
  , prf

  where
  -- We got the type of prf via auto.
  postulate prf : Stream is ∧
                  Bool b ∧
                  Fair os₀ ∧
                  Fair os₁ ∧
                  has (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ≡
                  send · b · is ·
                  hds (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ∧
                  hbs (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ≡
                  corrupt · os₀ ·
                  has (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ∧
                  hcs (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ≡
                  ack · b ·
                  hbs (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ∧
                  hds (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ≡
                  corrupt · os₁ ·
                  hcs (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
                  ∧
                  transfer b os₀ os₁ is
                  ≡
                  out · b ·
                  hbs (send · b) (ack · b) (out · b) (corrupt · os₀)
                  (corrupt · os₁) is
  {-# ATP prove prf #-}
