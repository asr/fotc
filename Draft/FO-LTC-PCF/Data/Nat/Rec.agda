---------------------------------------------------------------------------
-- The @rec@ definition using the fixed-point combinator
---------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Data.Nat.Rec where

open import Draft.FO-LTC-PCF.Base

---------------------------------------------------------------------------
-- Version using λ-abstraction.
-- rech : D → D
-- rech r = lam (λ n → lam (λ a → lam (λ f →
--              (if (isZero n)
--                then a
--                else f · (pred n) · (r · (pred n) · a · f)))))

-- rec : D → D → D → D
-- rec n a f = fix rech · n · a · f

-- Version using lambda-lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

private
  rec-helper₁ : D → D → D → D → D
  rec-helper₁ n a r f = if (iszero₁ n)
                           then a
                           else f · (pred₁ n) · (r · (pred₁ n) · a · f)
  {-# ATP definition rec-helper₁ #-}

  rec-helper₂ : D → D → D → D
  rec-helper₂ n r a = lam (rec-helper₁ n a r)
  {-# ATP definition rec-helper₂ #-}

  -- rech : D → D
  -- rech r = lam (λ n → lam (β n r))

  rec-helper₃ : D → D → D
  rec-helper₃ r n = lam (rec-helper₂ n r)
  {-# ATP definition rec-helper₃ #-}

rech : D → D
rech r = lam (rec-helper₃ r)
{-# ATP definition rech #-}

rec : D → D → D → D
rec n a f = fix rech · n · a · f
{-# ATP definition rec #-}
