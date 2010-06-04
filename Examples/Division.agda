------------------------------------------------------------------------------
-- Definition of division using repeated subtraction
------------------------------------------------------------------------------

module Examples.Division where

open import LTC.Minimal

open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

------------------------------------------------------------------------------

-- Version using lambda-abstraction.
-- divh : D → D
-- divh g = lam (λ i → lam (λ j →
--              if (lt i j)
--                then zero
--                else (succ (g ∙ (i - j) ∙ j))))

-- Version using lambda lifting via super-combinators.
-- (Hughes. Super-combinators. 1982)

div-aux₁ : D → D → D → D
div-aux₁ i g j = if (lt i j) then zero else (succ (g ∙ (i - j) ∙ j))
{-# ATP definition div-aux₁ #-}

div-aux₂ : D → D → D
div-aux₂ g i = lam (div-aux₁ i g)
{-# ATP definition div-aux₂ #-}

divh : D → D
divh g = lam (div-aux₂ g)
{-# ATP definition divh #-}

div : D → D → D
div i j = fix divh ∙ i ∙ j
{-# ATP definition div #-}
