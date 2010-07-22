-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants
    ( trueFOL
    , falseFOL
    , notFOL
    , andFOL
    , orFOL
    , equivFOL
    , existsFOL
    , equalsFOL
    ) where

-----------------------------------------------------------------------------
-- The FOL constant names.
trueFOL, falseFOL, notFOL, andFOL, orFOL, equivFOL :: String
trueFOL   = "⊤"
falseFOL  = "⊥"
notFOL    = "¬"
andFOL    = "∧"
orFOL     = "∨"
equivFOL  = "↔"

existsFOL, equalsFOL :: String
existsFOL = "∃D"
equalsFOL = "≡"

-- These FOL constanst are not used because we use the Agda versions.
-- impliesFOL, forAllFOL :: String
-- impliesFOL = "Implies"
-- forAllFOL  = "ForAll"
