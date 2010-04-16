-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants where

-- FOL constant names -----------------------------------------------------

trueFOL, falseFOL, notFOL, andFOL, orFOL, existsFOL, equalsFOL :: String
trueFOL   = "True"
falseFOL  = "⊥"
notFOL    = "¬"
andFOL    = "∧"
orFOL     = "∨"
existsFOL = "∃D"
equalsFOL = "≡"

-- These FOL constanst are not used because we use the Agda versions.

-- impliesFOL, equivFOL , forAllFOL :: String
-- impliesFOL = "Implies"
-- equivFOL   = "Equiv"
-- forAllFOL  = "ForAll"

{-
folConstants = [  fol_And, fol_Or, fol_Implies, fol_Equiv
                , fol_Not, fol_Equals, fol_ForAll, fol_Exists
                , fol_Prop, fol_True, fol_False
                ]

isFOLConstant :: String -> Bool
isFOLConstant x = x `elem` folConstants
-}
