------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Common
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Common entities used in the translation from Agda to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Common ( varsToArgs ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg)
  , Hiding(NotHidden)
  , Nat
  , Relevance(Relevant)
  )
import Agda.Syntax.Internal ( Term(Var) )

------------------------------------------------------------------------------

varsToArgs ∷ Nat → [Arg Term]
varsToArgs 0 = []
varsToArgs n = Arg NotHidden Relevant (Var (n - 1) []) : varsToArgs (n - 1)
