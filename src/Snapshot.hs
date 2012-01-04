------------------------------------------------------------------------------
-- |
-- Module      : Snapshot
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Snapshot test.
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Snapshot ( snapshotTest ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( throwError )
import Control.Monad.Trans ( liftIO )
import Data.Functor        ( (<$>) )
import System.Directory    ( doesFileExist )
import System.FilePath     ( replaceDirectory )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base      ( getTOpts, T )
import Options         ( Options, optOutputDir, optSnapshotDir )
import Monad.Reports   ( reportS )
import Utils.Directory ( diff )

------------------------------------------------------------------------------

snapshotTest ∷ FilePath → T ()
snapshotTest file = do

  outputDir   ← optOutputDir <$> getTOpts
  snapshotDir ← optSnapshotDir <$> getTOpts

  let snapshotFile ∷ FilePath
      snapshotFile = replaceDirectory file snapshotDir

  if outputDir == snapshotDir
    then throwError "The --output-dir cannot be the same than the --snapshot-dir"
    else do
      b ← liftIO $ doesFileExist snapshotFile
      if not b
        then throwError $ "The file " ++ snapshotFile ++ " does not exist"
        else do
          diffOutput ← liftIO $ diff file snapshotFile
          if diffOutput
            then throwError $
                 "The files " ++ file ++ " and " ++ snapshotFile
                 ++ " are different"
            else reportS "" 1 $
                 "The files " ++ file ++ " and " ++ snapshotFile
                 ++ " are the same"
