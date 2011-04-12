------------------------------------------------------------------------------
-- The gcd (parametric) specification
------------------------------------------------------------------------------

open import FOTC.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC natural numbers type.
        )

open import FOTC.Program.GCD.Definitions
  using ( ¬x≡0∧y≡0 ; CD ; Divisible ; GACD )
open import FOTC.Program.GCD.GCD using ( gcd )

module FOTC.Program.GCD.Specification
  (gcd-N         : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → N (gcd m n))
  (gcd-CD        : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → CD m n (gcd m n))
  (gcd-Divisible : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n →
                   Divisible m n (gcd m n))
  (gcd-GACD      : ∀ {m n gcd} → N gcd → CD m n gcd → Divisible m n gcd →
                   GACD m n gcd)
  where

------------------------------------------------------------------------------
-- Greatest commun divisor.
record GCD (a b gcd : D) : Set where
  constructor is
  field
    -- The gcd is a common divisor.
    commonDivisor : CD a b gcd

    -- Greatest that any common divisor.
    greatest : GACD a b gcd

-- The 'gcd' is the GCD.
gcd-GCD : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → GCD m n (gcd m n)
gcd-GCD Nm Nn m≠0≠n = is (gcd-CD Nm Nn m≠0≠n)
                         (gcd-GACD (gcd-N Nm Nn m≠0≠n)
                                   (gcd-CD Nm Nn m≠0≠n)
                                   (gcd-Divisible Nm Nn m≠0≠n))
