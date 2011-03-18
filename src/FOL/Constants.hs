-----------------------------------------------------------------------------
-- The FOL constants
-----------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

-- Adapted from AgdaLight (Plugins.FOL.Constants).

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
folImplies = "⇒"  -- The Agda functional space can be used instead.
folEquiv   = "↔"

folExists, folForAll, folEquals ∷ String
folExists = "∃"
folForAll = "⋀"  -- The Agda dependent functional space can be used instead.
folEquals = "≡"
