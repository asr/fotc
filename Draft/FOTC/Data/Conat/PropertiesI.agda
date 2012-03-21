{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT 21 March 2012.

module Draft.FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-gfp₁ Cn
... | inj₁ prf              = subst N (sym prf) zN
... | inj₂ (n' , Cn' , prf) = subst N (sym prf) (sN (Conat→N Cn'))
