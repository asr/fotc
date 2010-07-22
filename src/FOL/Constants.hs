-- Adapted from agdaLight ( Plugins.FOL.Constants ).

{- | Identifiers recognized by the FOL translator. -}

module FOL.Constants
    ( trueFOL
    , falseFOL
    , notFOL
    , andFOL
    , orFOL
    , impliesFOL
    , equivFOL
    , existsFOL
    , equalsFOL
    ) where

-----------------------------------------------------------------------------
-- The FOL constant names.
-- The user can use two symbols for the implication, the impliesFOL
-- (⇒) and the Agda function space (→).
trueFOL, falseFOL, notFOL, andFOL, orFOL, impliesFOL, equivFOL :: String
trueFOL    = "⊤"
falseFOL   = "⊥"
notFOL     = "¬"
andFOL     = "∧"
orFOL      = "∨"
impliesFOL = "⇒"
equivFOL   = "↔"

existsFOL, equalsFOL :: String
existsFOL = "∃D"
equalsFOL = "≡"

-- These FOL constanst are not used because we use the Agda versions.
-- forAllFOL :: String
-- forAllFOL  = "ForAll"
