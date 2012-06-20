------------------------------------------------------------------------------
-- |
-- Module      : Utils.Show
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Utilities related to 'Show'.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Utils.Show ( showListLn, showLn ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( Monad((>>=)) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Function ( (.) )
import Data.List     ( (++) )

import Text.Show ( Show(show) )

------------------------------------------------------------------------------
-- | Version of 'show' adding a newline character.
showLn ∷ Show a ⇒ a → String
showLn = (++ "\n") . show

-- | Version of 'show' on lists where the elements are separated by
-- newline characters.
showListLn ∷ Show a ⇒ [a] → String
showListLn xs = xs >>= showLn  -- From Autoproc.Procmail.
