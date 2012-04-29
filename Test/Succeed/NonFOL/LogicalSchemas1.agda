------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Requires option @--non-fol-formula-quantification@.

module Test.Succeed.NonFOL.LogicalSchemas1 where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}

        -- Non-FOL translation: FOL universal quantified propositional
        -- function.

        -- If we have a bounded variable quantified on a function of a
        -- @Set@ to a @Set₁@, for example, the variable/predicate @P@ in
        --
        -- @(P : D → Set) → (x : D) → P x → P x@
        --
        -- we are quantifying on this variable/function

        -- (see @termToFormula (Pi domTy (Abs _ tyAbs))@),

        -- therefore we need to apply this variable/predicate to the
        -- others variables. See an example in
        -- Test.Succeed.AgdaInternalTerms.Var1.agda.
