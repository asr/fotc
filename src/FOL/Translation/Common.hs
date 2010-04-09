------------------------------------------------------------------------------
-- Common entities used in the translation from Agda to FOL Formulas
------------------------------------------------------------------------------

module FOL.Translation.Common where

-- Agda library imports

import Agda.Syntax.Common ( Arg(Arg), Hiding(NotHidden), Nat )
import Agda.Syntax.Internal ( Type, Term(Var) )

------------------------------------------------------------------------------

type AgdaTerm = Term
type AgdaType = Type

varsToArgs :: Nat -> [ Arg Term ]
varsToArgs 0 = []
varsToArgs n = (Arg NotHidden (Var (n - 1) [])) : varsToArgs (n - 1)
