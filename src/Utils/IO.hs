------------------------------------------------------------------------------
-- |
-- Module      : Utils.IO
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- IO utilities
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Utils.IO ( failureMsg )
where

------------------------------------------------------------------------------
-- Haskell imports

import System.Environment ( getProgName )
import System.IO          ( hPutStrLn, stderr )

------------------------------------------------------------------------------

-- | Failure message.
failureMsg ∷ String → IO ()
failureMsg err = do
  progName ← getProgName
  hPutStrLn stderr $ progName ++ ": " ++ err
