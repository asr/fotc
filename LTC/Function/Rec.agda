---------------------------------------------------------------------------
-- The 'rec' definition using the fixed point combinator
---------------------------------------------------------------------------

module LTC.Function.Rec where

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
  α : D → D → D → D → D
  α n a r f = if (isZero n)
                 then a
                 else f ∙ (pred n) ∙ (r ∙ (pred n) ∙ a ∙ f)
  {-# ATP definition α #-}

  -- rech : D → D
  -- rech r = lam (λ n → lam (λ a → lam ( α n a r )))

  β : D → D → D → D
  β n r a = lam ( α n a r )
  {-# ATP definition β #-}

  -- rech : D → D
  -- rech r = lam (λ n → lam (β n r))

  δ : D → D → D
  δ r n = lam (β n r)
  {-# ATP definition δ #-}

rech : D → D
rech r = lam (δ r)
{-# ATP definition rech #-}

rec : D → D → D → D
rec n a f = fix rech ∙ n ∙ a ∙ f
{-# ATP definition rec #-}
