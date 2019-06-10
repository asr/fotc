------------------------------------------------------------------------------
-- Properties for the nest function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Nest.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.Nest.Nest

------------------------------------------------------------------------------

-- TODO (2019-06-09): Missing proof.
nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 nzero = prf
  where postulate prf : nest zero ≡ zero
nest-x≡0 (nsucc {n} Nn) = prf (nest-x≡0 Nn)
  where postulate prf : nest n ≡ zero → nest (succ₁ n) ≡ zero

-- TODO (2019-06-09): Missing proof.
postulate nest-N : ∀ {n} → N n → N (nest n)
