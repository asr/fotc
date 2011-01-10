-----------------------------------------------------------------------------
-- The FOL constants
-----------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

-- Adapted from agdaLight (Plugins.FOL.Constants)

module FOL.Constants
    ( folTrue
    , folFalse
    , folNot
    , folAnd
    , folOr
    , folImplies
    , folEquiv
    , folExists
    , folForAll
    , folEquals
    ) where

-----------------------------------------------------------------------------
-- Identifiers recognized by the FOL translator.
folTrue, folFalse, folNot, folAnd, folOr, folImplies, folEquiv ∷ String
folTrue    = "⊤"
folFalse   = "⊥"
folNot     = "¬"
folAnd     = "∧"
folOr      = "∨"
folImplies = "⇒"  -- Also it can be used the Agda functional space.
folEquiv   = "↔"

folExists, folForAll, folEquals ∷ String
folExists = "∃D"
folForAll = "∀D"  -- Also it can be used the Agda functional space.
folEquals = "≡"
