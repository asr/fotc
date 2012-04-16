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

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Common ( varsToArgs ) where

------------------------------------------------------------------------------
-- Haskell imports

-- TODO: 2012-04-16. Why is it necessary?
#if __GLASGOW_HASKELL__ == 612
import Data.Eq ( Eq((==)) )
#endif

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif
import GHC.Num ( Num((-)) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg)
  , Hiding(NotHidden)
  , Nat
  , Relevance(Relevant)
  )

import Agda.Syntax.Internal ( var, Term )

------------------------------------------------------------------------------

varsToArgs ∷ Nat → [Arg Term]
varsToArgs 0 = []
varsToArgs n = Arg NotHidden Relevant (var (n - 1)) : varsToArgs (n - 1)
