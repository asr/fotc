------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
-- using the Euclid's algorithm
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.GCD where

open import LTC-PCF.Base

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities

------------------------------------------------------------------------------

{-
It is possible to define two different versions of gcd based on which
(partial) order on natural numbers we are considering. In one version,
'gcd 0 0' is defined and in the other version, it isn't defined.
-}

-- Instead of define
-- 'gcdh : ((D → D → D) → (D → D → D)) → D → D → D', we use the LTC
-- abstraction ('lam') and application ('·') to avoid use a polymorphic fixed
-- point operator.

-- Version using lambda-abstraction.

-- gcdh : D → D
-- gcdh g = lam (λ d → lam (λ e →
--            if (isZero e)
--               then (if (isZero d)
--                        then error
--                        else d)
--               else (if (isZero d)
--                        then e
--                        else (if (gt d e)
--                                 then g · (d ∸ e) · e
--                                 else g · d · (e ∸ d)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

gcd-helper₁ : D → D → D → D
gcd-helper₁ d g e = if (isZero e)
                       then (if (isZero d)
                                then loop
                                else d)
                       else (if (isZero d)
                                then e
                                else (if (d > e)
                                         then g · (d ∸ e) · e
                                         else g · d · (e ∸ d)))
{-# ATP definition gcd-helper₁ #-}

gcd-helper₂ : D → D → D
gcd-helper₂ g d = lam (gcd-helper₁ d g)
{-# ATP definition gcd-helper₂ #-}

gcdh : D → D
gcdh g = lam (gcd-helper₂ g)
{-# ATP definition gcdh #-}

gcd : D → D → D
gcd d e = fix gcdh · d · e
{-# ATP definition gcd #-}
