------------------------------------------------------------------------------
-- Definition of division using repeated subtraction
------------------------------------------------------------------------------

module Examples.Division where

open import LTC.Minimal

open import LTC.Function.ArithmeticPCF
open import LTC.Relation.InequalitiesPCF

------------------------------------------------------------------------------

divh : D → D
divh g = lam (λ i → lam (λ j →
             if (lt i j)
               then zero
               else (succ (g ∙ (i - j) ∙ j))))

div : D → D → D
div i j = fix divh ∙ i ∙ j
