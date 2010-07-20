------------------------------------------------------------------------------
-- Functions on Agda internal syntax entities
------------------------------------------------------------------------------

module MyAgda.Syntax.Internal ( incTermVariables) where

-- Agda libray imports
import Agda.Syntax.Common ( Arg(Arg) )
import Agda.Syntax.Internal ( Term(Var) )

------------------------------------------------------------------------------

incTermVariables :: Arg Term -> Arg Term
incTermVariables (Arg h (Var n args)) = Arg h (Var (n + 1) args)
incTermVariables argTerm              = argTerm
