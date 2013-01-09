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
send  : {A : Set} → Bit → Stream A → Stream (Err Bit) → Stream (A × Bool)
await : {A : Set} → Bit → Stream A → Stream (Err Bit) → Stream (A × Bit)

send b (i ∷ is) ds = (i , b) ∷ ♯ await b (i ∷ is) ds

await b (i ∷ is) (ok b₀ ∷ ds) with b ≟ b₀
... | yes p = send (not b) (♭ is) (♭ ds)
... | no ¬p = (i , b) ∷ ♯ (await b (i ∷ is) (♭ ds))
await b (i ∷ is) (error ∷ ds) = (i , b) ∷ ♯ (await b (i ∷ is) (♭ ds))

-- The receiver functions.
ack : {A : Set} → Bit → Stream (Err (A × Bit)) → Stream Bit
ack b (ok (_ , b₀) ∷ bs) with b ≟ b₀
... | yes p = b ∷ ♯ (ack (not b) (♭ bs))
... | no ¬p = not b ∷ ♯ (ack b (♭ bs))
ack b (error ∷ bs) = not b ∷ ♯ (ack b (♭ bs))

{-# NO_TERMINATION_CHECK #-}
out : {A : Set} → Bit → Stream (Err (A × Bit)) → Stream A
out b (ok (i , b₀) ∷ bs) with b ≟ b₀
... | yes p = i ∷ ♯ (out (not b) (♭ bs))
... | no ¬p = out b (♭ bs)
out b (error ∷ bs) = out b (♭ bs)

-- Model the fair unreliable tranmission channel.
corrupt : {A : Set} → Stream Bit → Stream A → Stream (Err A)
corrupt (true ∷ os)  (_ ∷ xs) = error ∷ ♯ (corrupt (♭ os) (♭ xs))
corrupt (false ∷ os) (x ∷ xs) = ok x ∷ ♯ (corrupt (♭ os) (♭ xs))

-- The ABP transfer function.
{-# NO_TERMINATION_CHECK #-}
trans : {A : Set} → Bit → Stream Bit → Stream Bit → Stream A → Stream A
trans {A} b os₀ os₁ is = out b bs
  where
  as : Stream (A × Bit)
  bs : Stream (Err (A × Bit))
  cs : Stream Bit
  ds : Stream (Err Bit)

  as = send b is ds
  bs = corrupt os₀ as
  cs = ack b bs
  ds = corrupt os₁ cs
