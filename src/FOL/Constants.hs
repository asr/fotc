-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants where

-- FOL constant names -----------------------------------------------------

folTrue, folFalse, folNot, folAnd, folImplies, folOr, folEquiv :: String
folForAll, folExists, folEquals :: String

folTrue    = "True"
folFalse   = "False"
folNot     = "Not"
folAnd     = "And"
folImplies = "Implies"
folOr      = "Or"
folEquiv   = "Equiv"
folExists  = "Exists"
folForAll  = "ForAll"
folEquals  = "=="

{-
folConstants = [  fol_And, fol_Or, fol_Implies, fol_Equiv
                , fol_Not, fol_Equals, fol_ForAll, fol_Exists
                , fol_Prop, fol_True, fol_False
                ]

isFOLConstant :: String -> Bool
isFOLConstant x = x `elem` folConstants
-}
