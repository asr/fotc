---------------------------------------------------------------------------
-- The 'gcd' is greatest that any common divisor
---------------------------------------------------------------------------

open import LTC.Base

open import LTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Divisibility using ( _∣_ )
open import LTC-PCF.Data.Nat.Inequalities using ( LE )

module LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor
  ( x∣1+y→x≤1+y : ∀ {m n} → N m → N n → m ∣ (succ n) → LE m (succ n)
  )
  where

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat.Divisibility.Properties using ( 0∤x )

open import LTC-PCF.Program.GCD.Definitions using ( CD ; Divisible ; GACD )

---------------------------------------------------------------------------
-- Knowing that 'gcd' is a common divisor of 'm' and 'n', and that
-- any other common divisor of 'm' and 'n' divides it, we can
-- prove that 'gcd' is the largest common divisor.

-- We need 'N d'.

gcd-GACD : ∀ {m n gcd} → N gcd → CD m n gcd → Divisible m n gcd → GACD m n gcd
gcd-GACD zN              (0∣m , _) = ⊥-elim $ 0∤x 0∣m
gcd-GACD (sN {gcd} Ngcd) _         =
  λ Divisible-mnSgcd c Nc CDmnc → x∣1+y→x≤1+y Nc Ngcd (Divisible-mnSgcd c Nc CDmnc)
