---------------------------------------------------------------------------
-- The gcd is greatest that any common divisor
---------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Inequalities

module FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
  (x∣Sy→x≤Sy : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n)
  (0∤x       : ∀ {n} → ¬ (zero ∣ n))
  where

open import FOTC.Program.GCD.Partial.Definitions

---------------------------------------------------------------------------
-- Knowing that gcd is a common divisor of m and n and that any other
-- common divisor of m and n divides it, we can prove that gcd is the
-- largest common divisor.

-- It requires the totality of gcd, ie. N gcd.
gcdGACD : ∀ {m n gcd} → N gcd → CD m n gcd → Divisible m n gcd → GACD m n gcd
gcdGACD nzero             (0∣m , _) = ⊥-elim (0∤x 0∣m)
gcdGACD (nsucc {gcd} Ngcd) _        =
  λ Divisible-mnSgcd c Nc CDmnc → x∣Sy→x≤Sy Nc Ngcd
                     (Divisible-mnSgcd c Nc CDmnc)
