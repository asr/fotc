------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality

------------------------------------------------------------------------------

≈N-pre-fixed : ∀ {m n} →
               (m ≡ zero ∧ n ≡ zero
                 ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n')) →
               m ≈N n
≈N-pre-fixed {m} {n} h = ≈N-coind (λ o _ → o ≡ o) h' refl
  where
  postulate
    h' : m ≡ m →
         m ≡ zero ∧ n ≡ zero
           ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≡ m')
  {-# ATP prove h' #-}

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind (λ m _ → m ≡ m) h refl
  where
  postulate
    h : n ≡ n →
        n ≡ zero ∧ n ≡ zero
          ∨ (∃[ n' ] ∃[ n'' ] n ≡ succ₁ n' ∧ n ≡ succ₁ n'' ∧ n' ≡ n')
  {-# ATP prove h #-}

postulate ≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
{-# ATP prove ≡→≈N ≈N-refl #-}

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
