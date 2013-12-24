{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.PropertiesI
open import FOTC.Data.Nat

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-unf Cn
... | inj₁ prf              = subst N (sym prf) nzero
... | inj₂ (n' , prf , Cn') = subst N (sym prf) (nsucc (Conat→N Cn'))
