------------------------------------------------------------------------------
-- Some proofs related to exponentiation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Exponentiation where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

------------------------------------------------------------------------------

postulate
  _^_ : D → D → D
  ^-0 : ∀ n → n ^ zero      ≡ [1]
  ^-S : ∀ m n → m ^ succ₁ n ≡ m * m ^ n
{-# ATP axiom ^-0 ^-S #-}

thm : ∀ {n} → N n → [5] ≤ n → n ^ [5] ≤ [5] ^ n
thm nzero h = prf
  where postulate prf : zero ^ [5] ≤ [5] ^ zero
        {-# ATP prove prf #-}
thm (nsucc {n} Nn) h = prf (thm Nn)
  where postulate prf : ([5] ≤ n → n ^ [5] ≤ [5] ^ n) →
                        (succ₁ n) ^ [5] ≤ [5] ^ (succ₁ n)
        -- 10 May 2013: The ATPs could not prove the theorem (240 sec).
        -- {-# ATP prove prf 5-N #-}
