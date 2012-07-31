------------------------------------------------------------------------------
-- |
-- Module      : Utils.Monad
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Monads utilities
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.Monad
  ( die
  , failureMsg
  , pair
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import System.Environment ( getProgName )
import System.Exit        ( exitFailure )
import System.IO          ( hPutStrLn, stderr )

------------------------------------------------------------------------------
-- | Sequences a pair of monadic computations.
pair ∷ Monad m ⇒ m a → m b → m (a,b)
pair mx my = mx >>= \x → my >>= \y → return (x,y)

-- | Failure message.
failureMsg ∷ String → IO ()
failureMsg err = do
  progName ← getProgName
  hPutStrLn stderr $ progName ++ ": " ++ err

-- | Exit with an error message.
die ∷ String → IO a
die err = failureMsg err >> exitFailure
