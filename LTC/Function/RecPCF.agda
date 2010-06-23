---------------------------------------------------------------------------
-- The 'rec' definition using the fixed point combinator
---------------------------------------------------------------------------

module LTC.Function.RecPCF where

open import LTC.Minimal

---------------------------------------------------------------------------

-- Version using lambda-abstraction
-- rech : D → D
-- rech r = lam (λ n → lam (λ a → lam (λ f →
--              (if (isZero n)
--                then a
--                else f ∙ (pred n) ∙ (r ∙ (pred n) ∙ a ∙ f)))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

private
  rec-aux₁ : D → D → D → D → D
  rec-aux₁ n a r f = if (isZero n)
                        then a
                        else f ∙ (pred n) ∙ (r ∙ (pred n) ∙ a ∙ f)
  {-# ATP definition rec-aux₁ #-}

  rec-aux₂ : D → D → D → D
  rec-aux₂ n r a = lam ( rec-aux₁ n a r )
  {-# ATP definition rec-aux₂ #-}

  -- rech : D → D
  -- rech r = lam (λ n → lam (β n r))

  rec-aux₃ : D → D → D
  rec-aux₃ r n = lam (rec-aux₂ n r)
  {-# ATP definition rec-aux₃ #-}

rech : D → D
rech r = lam (rec-aux₃ r)
{-# ATP definition rech #-}

rec : D → D → D → D
rec n a f = fix rech ∙ n ∙ a ∙ f
{-# ATP definition rec #-}
