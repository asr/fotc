-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants where

-----------------------------------------------------------------------------
-- The FOL constant names.
trueFOL, falseFOL, notFOL, andFOL, orFOL, existsFOL, equalsFOL :: String
trueFOL   = "⊤"
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
