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

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}

module Snapshot ( snapshotTest ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>=), fail) )
#endif

import Control.Monad.Error ( MonadError(throwError) )
import Control.Monad.Trans ( liftIO )

import Data.Bool     ( not )
import Data.Eq       ( Eq((==)) )
import Data.Function ( ($) )
import Data.List     ( (++) )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif

import System.FilePath ( replaceDirectory )
import System.IO       ( FilePath )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.FileName ( doesFileExistCaseSensitive )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base      ( getTOpt, T )
import Options         ( Options(optOutputDir, optSnapshotDir) )
import Monad.Reports   ( reportS )
import Utils.Directory ( diff )

------------------------------------------------------------------------------
-- | Compare the generated TPTP files against a snapshot of them in
-- the directory indicated by the flag @--snapshot-dir@.
snapshotTest ∷ FilePath → T ()
snapshotTest file = do
  outputDir   ← getTOpt optOutputDir
  snapshotDir ← getTOpt optSnapshotDir

  let snapshotFile ∷ FilePath
      snapshotFile = replaceDirectory file snapshotDir

  if outputDir == snapshotDir
    then throwError "The --output-dir cannot be the same than the --snapshot-dir"
    else do
      b ← liftIO $ doesFileExistCaseSensitive snapshotFile
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
