------------------------------------------------------------------------------
-- Properties for the nest function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Nest.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.Type
open import Combined.FOTC.Program.Nest.Nest

------------------------------------------------------------------------------

nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 nzero = prf
  where postulate prf : nest zero ≡ zero
        {-# ATP prove prf #-}
nest-x≡0 (nsucc {n} Nn) = prf (nest-x≡0 Nn)
  where postulate prf : nest n ≡ zero → nest (succ₁ n) ≡ zero
        {-# ATP prove prf #-}

postulate nest-N : ∀ {n} → N n → N (nest n)
{-# ATP prove nest-N nest-x≡0 #-}
