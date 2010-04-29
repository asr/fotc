------------------------------------------------------------------------------
-- Specification of the Euclid's algorithm for calculate the greatest
-- common divisor of two natural numbers (using equational reasoning)
------------------------------------------------------------------------------

module Examples.GCD.Properties.IsGCD-ER where

open import LTC.Minimal

open import Examples.GCD
open import Examples.GCD.Properties.IsCommonDivisorER
open import Examples.GCD.Properties.IsDivisibleER
open import Examples.GCD.Properties.IsN-ER

open import LTC.Data.N
open import LTC.Relation.Divisibility.Postulates using ( x∣S→x≤S )
open import LTC.Relation.Divisibility.PropertiesER
open import LTC.Relation.Inequalities

---------------------------------------------------------------------------
-- The 'gcd' is greatest that any common divisor
---------------------------------------------------------------------------

-- Greatest that any common divisor.
GACD : D → D → D → Set
GACD a b g = (c : D) → N c → CD a b c → LE c g

-- Knowing that 'g' is a common divisor of 'm' and 'n', and that
-- any other common divisor of 'm' and 'n' divides it, we can
-- prove that 'g' is the largest common divisor.

-- We need 'N d'.
-- TODO: Why the dependent type '$' doesn't work in '⊥-elim (0∤n d∣m)'?

gcd-GACD : {m n g : D} → N g → CD m n g → Divisible m n g → GACD m n g
gcd-GACD zN     ( 0∣m , _) = ⊥-elim (0∤x 0∣m )
gcd-GACD (sN {g} Ng) _     =
  λ Divisible-mnSg c Nc CDmnc → x∣S→x≤S Nc Ng (Divisible-mnSg c Nc CDmnc)

-----------------------------------------------------------------------
-- The 'gcd' is the GCD.
-----------------------------------------------------------------------

-- Greatest commun divisor.
GCD : D → D → D → Set
GCD a b g = CD a b g ∧ GACD a b g

gcd-GCD : {m n : D} → N m → N n →
          ¬ ((m ≡ zero) ∧ (n ≡ zero))
          → GCD m n (gcd m n)
gcd-GCD {m} {n} Nm Nn m≠0≠n =
  ( CDmngcd , (gcd-GACD (gcd-N Nm Nn m≠0≠n)
                        CDmngcd
                        (gcd-Divisible Nm Nn m≠0≠n)) )

  where CDmngcd : CD m n (gcd m n)
        CDmngcd = gcd-CD Nm Nn m≠0≠n
