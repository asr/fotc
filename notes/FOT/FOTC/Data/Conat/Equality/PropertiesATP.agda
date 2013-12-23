------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.Equality.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality

------------------------------------------------------------------------------

≈N-pre-fixed : (∀ {m n} → m ≡ zero ∧ n ≡ zero
                 ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≈N n')) →
               ∀ {m n} → m ≈N n
≈N-pre-fixed h = ≈N-coind (λ o _ → o ≡ o) h' refl
  where
  postulate h' : ∀ {m n} → m ≡ m →
                 m ≡ zero ∧ n ≡ zero
                   ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ m' ≡ m')
  -- TODO (22 December 2013): The translation failed because we do not
  -- know how erase a term.
  -- {-# ATP prove h' #-}
