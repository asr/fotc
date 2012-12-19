------------------------------------------------------------------------------
-- The FOTC streams of total natural numbers type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Stream.

module FOT.FOTC.Data.Nat.Stream.Type where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The FOTC streams type (co-inductive predicate for total streams).

-- Functional for the StreamN predicate.
-- StreamNF : (D → Set) → D → Set
-- StreamNF P ns = ∃[ n' ] ∃[ ns' ] N n' ∧ P ns' ∧ ns ≡ n' ∷ ns'

-- Stream is the greatest fixed-point of StreamF (by Stream-unf and
-- Stream-coind).

postulate StreamN : D → Set

postulate
-- StreamN is a post-fixed point of StreamNF, i.e.
--
-- StreamN ≤ StreamNF StreamN.
  StreamN-unf : ∀ {ns} → StreamN ns →
                ∃[ n' ] ∃[ ns' ] N n' ∧ StreamN ns' ∧ ns ≡ n' ∷ ns'
{-# ATP axiom StreamN-unf #-}

-- StreamN is the greatest post-fixed point of StreamNF, i.e
--
-- ∀ P. P ≤ StreamNF P ⇒ P ≤ StreamN.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  StreamN-coind :
    (A : D → Set) →
    -- A is post-fixed point of StreamNF.
    (∀ {ns} → A ns → ∃[ n' ] ∃[ ns' ] N n' ∧ A ns' ∧ ns ≡ n' ∷ ns') →
    -- StreamN is greater than A.
    ∀ {ns} → A ns → StreamN ns

-- Because a greatest post-fixed point is a fixed-point, then the
-- StreamN predicate is also a pre-fixed point of the functional
-- StreamNF, i.e.
--
-- StreamNF StreamN ≤ StreamN.
StreamN-gfp₃ : ∀ {ns} →
               (∃[ n' ] ∃[ ns' ] N n' ∧ StreamN ns' ∧ ns ≡ n' ∷ ns') →
               StreamN ns
StreamN-gfp₃ h = StreamN-coind A helper h
  where
  A : D → Set
  A ns = ∃[ n' ] ∃[ ns' ] N n' ∧ StreamN ns' ∧ ns ≡ n' ∷ ns'

  helper : ∀ {ns} → A ns → ∃[ n' ] ∃[ ns' ] N n' ∧ A ns' ∧ ns ≡ n' ∷ ns'
  helper (_ , _ , Nn' , SNns' , h₁) = _ , _ , Nn' , (StreamN-unf SNns') , h₁
