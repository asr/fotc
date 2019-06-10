{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.Conat.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Conat
open import Interactive.FOTC.Data.Conat.Properties
open import Interactive.FOTC.Data.Nat

------------------------------------------------------------------------------
-- 25 April 2014, Failed with --without-K.
--
{-# TERMINATING #-}
Conat→N : ∀ {n} → Conat n → N n
Conat→N Cn with Conat-out Cn
... | inj₁ prf               = subst N (sym prf) nzero
... | inj₂ (n' , refl , Cn') = nsucc (Conat→N Cn')
