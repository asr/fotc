------------------------------------------------------------------------------
-- The ABP using Agda standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.ABP.ABP-SL where

open import Coinduction
open import Data.Bool
open import Data.Product
open import Data.Stream
open import Relation.Nullary

------------------------------------------------------------------------------

Bit : Set
Bit = Bool

-- Data type used to model the fair unreliable transmission channel.
data Err (A : Set) : Set where
  ok    : (x : A) → Err A
  error : Err A

-- The mutual sender functions.
sendA  : {A : Set} → Bit → Stream A → Stream (Err Bit) → Stream (A × Bool)
awaitA : {A : Set} → Bit → Stream A → Stream (Err Bit) → Stream (A × Bit)

sendA b (i ∷ is) ds = (i , b) ∷ ♯ awaitA b (i ∷ is) ds

awaitA b (i ∷ is) (ok b' ∷ ds) with b ≟ b'
... | yes p = sendA (not b) (♭ is) (♭ ds)
... | no ¬p = (i , b) ∷ ♯ (awaitA b (i ∷ is) (♭ ds))
awaitA b (i ∷ is) (error ∷ ds) = (i , b) ∷ ♯ (awaitA b (i ∷ is) (♭ ds))

-- The receiver functions.
ackA : {A : Set} → Bit → Stream (Err (A × Bit)) → Stream Bit
ackA b (ok (_ , b') ∷ bs) with b ≟ b'
... | yes p = b ∷ ♯ (ackA (not b) (♭ bs))
... | no ¬p = not b ∷ ♯ (ackA b (♭ bs))
ackA b (error ∷ bs) = not b ∷ ♯ (ackA b (♭ bs))

{-# NO_TERMINATION_CHECK #-}
outA : {A : Set} → Bit → Stream (Err (A × Bit)) → Stream A
outA b (ok (i , b') ∷ bs) with b ≟ b'
... | yes p = i ∷ ♯ (outA (not b) (♭ bs))
... | no ¬p = outA b (♭ bs)
outA b (error ∷ bs) = outA b (♭ bs)

-- Model the fair unreliable tranmission channel.
corruptA : {A : Set} → Stream Bit → Stream A → Stream (Err A)
corruptA (true ∷ os)  (_ ∷ xs) = error ∷ ♯ (corruptA (♭ os) (♭ xs))
corruptA (false ∷ os) (x ∷ xs) = ok x ∷ ♯ (corruptA (♭ os) (♭ xs))

-- The ABP transfer function.
{-# NO_TERMINATION_CHECK #-}
abpTransA : {A : Set} → Bit → Stream Bit → Stream Bit → Stream A → Stream A
abpTransA {A} b os₁ os₂ is = outA b bs
  where
  as : Stream (A × Bit)
  bs : Stream (Err (A × Bit))
  cs : Stream Bit
  ds : Stream (Err Bit)

  as = sendA b is ds
  bs = corruptA os₁ as
  cs = ackA b bs
  ds = corruptA os₂ cs
