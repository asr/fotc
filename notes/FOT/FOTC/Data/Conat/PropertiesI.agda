{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-unf Cn
... | inj₁ prf              = subst N (sym prf) nzero
... | inj₂ (n' , prf , Cn') = subst N (sym prf) (nsucc (Conat→N Cn'))

-- A different proof of ∞-Conat using a non-trivial predicate. Adapted
-- from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ ∞

  h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h An = inj₂ (∞ , trans An ∞-eq , refl)

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
