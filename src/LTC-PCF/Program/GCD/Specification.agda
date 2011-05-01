------------------------------------------------------------------------------
-- The gcd (parametric) specification
------------------------------------------------------------------------------

open import LTC-PCF.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )

open import LTC-PCF.Program.GCD.Definitions
  using ( x≠0≠y ; CD ; Divisible ; GACD )
open import LTC-PCF.Program.GCD.GCD using ( gcd )

module LTC-PCF.Program.GCD.Specification
  (gcd-N         : ∀ {m n} → N m → N n → x≠0≠y m n → N (gcd m n))
  (gcd-CD        : ∀ {m n} → N m → N n → x≠0≠y m n → CD m n (gcd m n))
  (gcd-Divisible : ∀ {m n} → N m → N n → x≠0≠y m n →
                   Divisible m n (gcd m n))
  (gcd-GACD      : ∀ {m n gcd} → N gcd → CD m n gcd → Divisible m n gcd →
                   GACD m n gcd)
  where

------------------------------------------------------------------------------
-- Greatest common divisor.
record GCD (a b gcd : D) : Set where
  constructor is
  field
    -- The gcd is a common divisor.
    commonDivisor : CD a b gcd

    -- The gcd is greatest that any common divisor.
    greatest : GACD a b gcd

-- The 'gcd' is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → x≠0≠y m n → GCD m n (gcd m n)
gcd-GCD Nm Nn m≠0≠n = is (gcd-CD Nm Nn m≠0≠n)
                         (gcd-GACD (gcd-N Nm Nn m≠0≠n)
                                   (gcd-CD Nm Nn m≠0≠n)
                                   (gcd-Divisible Nm Nn m≠0≠n))
