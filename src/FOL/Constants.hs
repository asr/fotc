-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants where

-- FOL constant names -----------------------------------------------------

trueFOL, falseFOL, notFOL, andFOL, impliesFOL, orFOL, equivFOL :: String
forAllFOL, existsFOL, equalsFOL :: String

trueFOL    = "True"
falseFOL   = "False"
notFOL     = "Not"
andFOL     = "And"
impliesFOL = "Implies"
orFOL      = "Or"
equivFOL   = "Equiv"
existsFOL  = "Exists"
forAllFOL  = "ForAll"
equalsFOL  = "≡"

{-
folConstants = [  fol_And, fol_Or, fol_Implies, fol_Equiv
                , fol_Not, fol_Equals, fol_ForAll, fol_Exists
                , fol_Prop, fol_True, fol_False
                ]

isFOLConstant :: String -> Bool
isFOLConstant x = x `elem` folConstants
-}
