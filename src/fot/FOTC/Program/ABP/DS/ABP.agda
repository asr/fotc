------------------------------------------------------------------------------
-- The alternating bit protocol (ABP)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module define the auxiliary state for the ABP and the
-- bisimulation used by Dybjer and Sander (1989).
--
-- References:
--
-- • Dybjer, Peter and Sander, Herbert P. (1989). A Functional
--   Programming Approach to the Speciﬁcation and Veriﬁcation of
--   Concurrent Systems. In: Formal Aspects of Computing 1,
--   pp. 303–319.

module FOTC.Program.ABP.DS.ABP where

open import FOTC.Base
-- open import FOTC.Base.Loop
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- ABP relations

-- Auxiliary state for the ABP.
S' : D → D → D → D → D → D → D → D → D → D → Set
S' b i' is' os₁' os₂' as' bs' cs' ds' js' =
  as' ≡ await b i' is' ds'  -- Typo in ds'.
  ∧ bs' ≡ corrupt os₁' · as'
  ∧ cs' ≡ ack (not b) · bs'
  ∧ ds' ≡ corrupt os₂' · (b ∷ cs')
  ∧ js' ≡ out (not b) · bs'
{-# ATP definition S' #-}

-- Auxiliary bisimulation.
B : D → D → Set
B is js = ∃[ b ] ∃[ os₁ ] ∃[ os₂ ] ∃[ as ] ∃[ bs ] ∃[ cs ] ∃[ ds ]
            Stream is
            ∧ Bit b
            ∧ Fair os₁
            ∧ Fair os₂
            ∧ S b is os₁ os₂ as bs cs ds js
{-# ATP definition B #-}
