---------------------------------------------------------------------------
-- The 'gcd' is greatest that any common divisor
---------------------------------------------------------------------------

module Examples.GCD.IsGreatestAnyCommonDivisor where

open import LTC.Base

open import Common.Function using ( _$_ )

open import Examples.GCD.IsCommonDivisor using ( CD )
open import Examples.GCD.IsDivisible using ( Divisible )

open import LTC.Data.Nat.Divisibility.Properties using ( 0∤x ; x∣S→x≤S )
open import LTC.Data.Nat.Inequalities using ( LE )
open import LTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The LTC natural numbers type.
        )

---------------------------------------------------------------------------
-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD a b gcd = (c : D) → N c → CD a b c → LE c gcd

-- Knowing that 'gcd' is a common divisor of 'm' and 'n', and that
-- any other common divisor of 'm' and 'n' divides it, we can
-- prove that 'gcd' is the largest common divisor.

-- We need 'N d'.

gcd-GACD : {m n gcd : D} → N gcd → CD m n gcd → Divisible m n gcd →
           GACD m n gcd
gcd-GACD zN             (0∣m , _) = ⊥-elim $ 0∤x 0∣m
gcd-GACD (sN {gcd} Ngcd) _        =
  λ Divisible-mnSgcd c Nc CDmnc → x∣S→x≤S Nc Ngcd (Divisible-mnSgcd c Nc CDmnc)
