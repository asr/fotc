{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.PropertiesI
open import FOTC.Data.Nat

------------------------------------------------------------------------------

-- 09 January 2014. Doesn't type check with --without-K.
--
{-# NO_TERMINATION_CHECK #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-out Cn
... | inj₁ prf               = subst N (sym prf) nzero
... | inj₂ (n' , refl , Cn') = nsucc (Conat→N Cn')
