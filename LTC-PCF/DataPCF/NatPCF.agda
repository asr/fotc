------------------------------------------------------------------------------
-- Natural numbers (PCF version)
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF where

open import LTC.Minimal

open import LTC-PCF.DataPCF.NatPCF.RecPCF using ( rec )

infixl 7 _*_
infixl 6 _+_ _-_

------------------------------------------------------------------------------
-- The LTC natural numbers type.
open import LTC.Data.Nat.Type public

------------------------------------------------------------------------------
-- Arithmetic operations

-------------------------------------------------
-- Addition with recursion on the first argument.

-- Version using lambda-abstraction.
-- _+_ : D → D → D
-- m + n = rec m n (lam (λ x → lam (λ y → succ y)))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

+-aux : D → D
+-aux _ = lam succ
{-# ATP definition +-aux #-}

_+_ : D → D → D
m + n = rec m n (lam +-aux)
{-# ATP definition _+_ #-}

----------------
-- Substraction.

-- Version using lambda-abstraction.
-- _-_ : D → D → D
-- m - n = rec n m (lam (λ x → lam (λ y → pred y)))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

minus-aux : D → D
minus-aux _ = lam pred
{-# ATP definition minus-aux #-}

_-_ : D → D → D
m - n = rec n m (lam minus-aux)
{-# ATP definition _-_ #-}

-------------------------------------------------------
-- Multiplication with recursion on the first argument.

-- Version using lambda-abstraction.
-- _*_ : D → D → D
-- m * n = rec m zero (lam (λ _ → lam (λ y → n + y)))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

*-aux₁ : D → D → D
*-aux₁ n y = n + y
{-# ATP definition *-aux₁ #-}

*-aux₂ : D → D → D
*-aux₂ n x = lam (*-aux₁ n)
{-# ATP definition *-aux₂ #-}

_*_ : D → D → D
m * n = rec m zero (lam (*-aux₂ n))
{-# ATP definition _*_ #-}
