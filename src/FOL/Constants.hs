-----------------------------------------------------------------------------
-- The FOL constants
-----------------------------------------------------------------------------

-- Adapted from agdaLight (Plugins.FOL.Constants)

module FOL.Constants
    ( trueFOL
    , falseFOL
    , notFOL
    , andFOL
    , orFOL
    , impliesFOL
    , equivFOL
    , existsFOL
    , forAllFOL
    , equalsFOL
    ) where

-----------------------------------------------------------------------------
-- Identifiers recognized by the FOL translator.
trueFOL, falseFOL, notFOL, andFOL, orFOL, impliesFOL, equivFOL :: String
trueFOL    = "⊤"
falseFOL   = "⊥"
notFOL     = "¬"
andFOL     = "∧"
orFOL      = "∨"
impliesFOL = "⇒" -- Also it can be used the Agda functional space.
equivFOL   = "↔"

existsFOL, forAllFOL, equalsFOL :: String
existsFOL = "∃D"
forAllFOL = "∀D" -- Also it can be used the Agda functional space.
equalsFOL = "≡"
