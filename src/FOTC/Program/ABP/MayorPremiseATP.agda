------------------------------------------------------------------------------
-- ABP mayor premise
------------------------------------------------------------------------------

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

-- postulate
--   mayorPremise' : ∀ {b os₀ os₁ is} → Bit b → Fair os₀ → Fair os₁ → Stream is →
--                   is B abptransfer b os₀ os₁ is
-- E 1.4: CPU time limit exceeded, terminating (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
-- Metis 2.3 (release 20110531): SZS status Unknown (using timeout 180 sec).
-- SPASS 3.7: Ran out of time (using timeout 180 sec).
-- Vampire 0.6 (revision 903): Time limit (180 sec).
-- {-# ATP prove mayorPremise' #-}

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
  , prf

  where
  -- We get the type of prf via auto.
  postulate prf : Stream is ∧
                    Bool b ∧
                    Fair os₀ ∧
                    Fair os₁ ∧
                    has (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ≡
                    abpsend · b · is ·
                    hds (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ∧
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ≡
                    corrupt · os₀ ·
                    has (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ∧
                    hcs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ≡
                    abpack · b ·
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ∧
                    hds (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ≡
                    corrupt · os₁ ·
                    hcs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
                    ∧
                    abptransfer b os₀ os₁ is ≡
                    abpout · b ·
                    hbs (abpsend · b) (abpack · b) (abpout · b) (corrupt · os₀)
                    (corrupt · os₁) is
  {-# ATP prove prf #-}
