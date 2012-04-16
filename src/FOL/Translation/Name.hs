------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Concrete.Name
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of things about Agda concrete names.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Name ( concatName ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.List ( concatMap )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Concrete.Name ( NamePart(Id, Hole) )

------------------------------------------------------------------------------

takeId ∷ NamePart → String
takeId Hole         = []
takeId (Id strName) = strName

-- | Use the parts of a name to produce a new function name, e.g. the
-- function @if_then_else_@ is called @ifthenelseq@.
concatName ∷ [NamePart] → String
concatName = concatMap takeId
