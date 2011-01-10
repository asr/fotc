------------------------------------------------------------------------------
-- Common entities used in the translation from Agda to FOL Formulas
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Common ( varsToArgs ) where

-- Agda library imports
import Agda.Syntax.Common
    ( Arg(Arg)
    , Hiding(NotHidden)
    , Nat
    , Relevance(Relevant)
    )
import Agda.Syntax.Internal ( Term(Var) )

------------------------------------------------------------------------------

varsToArgs ∷ Nat → [ Arg Term ]
varsToArgs 0 = []
varsToArgs n = Arg NotHidden Relevant (Var (n - 1) []) : varsToArgs (n - 1)
