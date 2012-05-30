-----------------------------------------------------------------------------
-- |
-- Module      : FOL.Constants
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- The FOL constants.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
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

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

------------------------------------------------------------------------------
-- | Identifiers recognized by the FOL translator.
folTrue, folFalse, folNot, folAnd, folOr, folImplies, folEquiv ∷ String
folTrue    = "⊤"
folFalse   = "⊥"
folNot     = "¬"
folAnd     = "∧"
folOr      = "∨"
folImplies = "⇒"  -- The non-dependent function space @→@ can be used instead.
folEquiv   = "↔"

-- | Identifiers recognized by the FOL translator.
folExists, folForAll, folEquals ∷ String
folExists = "∃"
folForAll = "⋀"  -- The dependent function space @∀ x → A@ can be used instead.
folEquals = "≡"
