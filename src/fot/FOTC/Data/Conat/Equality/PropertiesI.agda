------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- relation _≈N_ is also a pre-fixed point of the functional ≈NF, i.e.
--
-- ≈NF _≈N_ ≤ _≈N_ (see FOTC.Data.Conat.Equality).
≈N-pre-fixed : ∀ {m n} →
               (m ≡ zero ∧ n ≡ zero
                 ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n')) →
               m ≈N n
≈N-pre-fixed {m} {n} h = ≈N-coind (λ o _ → o ≡ o) h' refl
  where
  h' : m ≡ m →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≡ m')
  h' _ with h
  ... | inj₁ prf                         = inj₁ prf
  ... | inj₂ (m' , n' , prf₁ , prf₂ , _) = inj₂ (m' , n' , prf₁ , prf₂ , refl)

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind (λ m _ → m ≡ m) h refl
  where
  h : n ≡ n →
      n ≡ zero ∧ n ≡ zero
        ∨ (∃[ n' ] ∃[ n'' ] n ≡ succ₁ n' ∧ n ≡ succ₁ n'' ∧ n' ≡ n')
  h _ with Conat-unf Cn
  ... | inj₁ prf            = inj₁ (prf , prf)
  ... | inj₂ (n' , prf , _) = inj₂ (n' , n' , prf , prf , refl)

≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈N Cm _ refl = ≈N-refl Cm

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
