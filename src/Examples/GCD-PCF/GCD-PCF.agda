------------------------------------------------------------------------------
-- Definition of the greatest common divisor of two natural numbers
-- using the Euclid's algorithm
------------------------------------------------------------------------------

module Examples.GCD-PCF.GCD-PCF where

open import LTC.Base

open import LTC-PCF.DataPCF.NatPCF using ( _-_ )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( gt )

------------------------------------------------------------------------------

{-
It is possible to define two different versions of gcd based on which
(partial) order on natural numbers we are considering. In one version,
'gcd 0 0' is defined and in the other version, it isn't defined.
-}

-- Instead of define
-- 'gcdh : ((D → D → D) → (D → D → D)) → D → D → D', we use the LTC
-- abstraction ('lam') and application ('∙') to avoid use a polymorphic fixed
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
--                                 then g ∙ (d - e) ∙ e
--                                 else g ∙ d ∙ (e - d)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

gcd-aux₁ : D → D → D → D
gcd-aux₁ d g e = if (isZero e)
                    then (if (isZero d)
                             then error
                             else d)
                         else (if (isZero d)
                           then e
                           else (if (gt d e)
                                    then g ∙ (d - e) ∙ e
                                    else g ∙ d ∙ (e - d)))
{-# ATP definition gcd-aux₁ #-}

gcd-aux₂ : D → D → D
gcd-aux₂ g d = lam (gcd-aux₁ d g)
{-# ATP definition gcd-aux₂ #-}

gcdh : D → D
gcdh g = lam (gcd-aux₂ g)
{-# ATP definition gcdh #-}

gcd : D → D → D
gcd d e = fix gcdh ∙ d ∙ e
{-# ATP definition gcd #-}

------------------------------------------------------------------------------
-- Common functions used by the gcd example

¬x≡0∧y≡0 : D → D → Set
¬x≡0∧y≡0 d e = ¬ (d ≡ zero ∧ e ≡ zero)
