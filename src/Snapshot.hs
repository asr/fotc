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
{-# LANGUAGE UnicodeSyntax #-}

module Snapshot ( snapshotTest ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( MonadError(throwError) )
import Control.Monad.Trans ( liftIO )

import System.FilePath ( combine, joinPath, splitPath )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Utils.FileName ( doesFileExistCaseSensitive )
import Agda.Utils.Monad    ( ifM, whenM )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base ( getTOpt, T )

import Options
  ( Options(optOutputDir, optSnapshotDir, optSnapshotNoError)
  )

import Utils.Directory ( diff )

------------------------------------------------------------------------------
-- | Compare the generated TPTP files against a snapshot of them in
-- the directory indicated by the flag @--snapshot-dir@.
snapshotTest ∷ FilePath → T ()
snapshotTest file = do
  outputDir   ← getTOpt optOutputDir
  snapshotDir ← getTOpt optSnapshotDir

  -- The original file without the output directory.
  let auxFile ∷ FilePath
      auxFile = joinPath $ drop (length $ splitPath outputDir) $ splitPath file

      snapshotFile ∷ FilePath
      snapshotFile = combine snapshotDir auxFile

  if outputDir == snapshotDir
    then throwError "The --output-dir cannot be the same than the --snapshot-dir"
    else do
      b ← liftIO $ doesFileExistCaseSensitive snapshotFile
      if not b
        then throwError $ "The file " ++ snapshotFile ++ " does not exist"
        else
          whenM (liftIO $ diff file snapshotFile) $ do
            let msg ∷ String
                msg = "The files are different:\n" ++ file ++ "\n" ++ snapshotFile

            -- This message is not included in the error test.
            ifM (getTOpt optSnapshotNoError)
                (liftIO $ putStrLn msg)
                (throwError msg)
