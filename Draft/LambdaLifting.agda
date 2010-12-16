------------------------------------------------------------------------------
-- Example of lambda-lifting
------------------------------------------------------------------------------

module Draft.LambdaLifting where

open import LTC.Base

open import LTC.Data.Nat using ( _*_ )

------------------------------------------------------------------------------

-- The original fach
-- fach : D → D
-- fach f = lam (λ n → if (isZero n) then (succ zero) else n * (f · (pred n)))

-- Lambda-lifting via super-combinators (Hughes. Super-combinators. 1982).

α : D → D → D
α f n = if (isZero n) then (succ zero) else n * (f · (pred n))
{-# ATP definition α #-}

fach : D → D
fach f = lam (α f)
{-# ATP definition fach #-}

fac : D → D
fac n = fix fach · n
{-# ATP definition fac #-}

postulate
  fac0 : fac zero ≡ succ zero
{-# ATP prove fac0 #-}

postulate
  fac1 : fac (succ zero) ≡ succ zero
{-# ATP prove fac1 #-}

postulate
  fac2 : fac (succ (succ zero)) ≡ succ (succ zero)
{-# ATP prove fac2 #-}
