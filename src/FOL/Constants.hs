{-# LANGUAGE UnicodeSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      : FOL.Constants
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- The FOL constants.
-----------------------------------------------------------------------------

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
