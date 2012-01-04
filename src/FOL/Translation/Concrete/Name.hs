------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Concrete.Name
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2011
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of things about Agda concrete names.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Concrete.Name ( concatName ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Concrete.Name ( NamePart(Id, Hole) )

------------------------------------------------------------------------------

takeId ∷ NamePart → String
takeId Hole         = []
takeId (Id strName) = strName

-- We use the parts of a name to produce a new function name,
-- e.g. the function 'if_then_else_' is called 'ifthenelse'.
concatName ∷ [NamePart] → String
concatName = concatMap takeId
