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

module Snapshot ( snapshotTest )
where

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

import Monad.Base ( askTOpt, T )

import Options
  ( Options(optOutputDir, optSnapshotDir, optSnapshotNoError)
  )

import Utils.Directory ( diff )

------------------------------------------------------------------------------
-- | Compare the generated TPTP files against a snapshot of them in
-- the directory indicated by the flag @--snapshot-dir@.
snapshotTest ∷ FilePath → T ()
snapshotTest file = do
  outputDir   ← askTOpt optOutputDir
  snapshotDir ← askTOpt optSnapshotDir

  -- The original file without the output directory.
  let auxFile ∷ FilePath
      auxFile = joinPath $ drop (length $ splitPath outputDir) $ splitPath file

      snapshotFile ∷ FilePath
      snapshotFile = combine snapshotDir auxFile

  if outputDir == snapshotDir
    then throwError "The options `--output-dir' and `--snapshot-dir' cannot be the same"
    else do
      b ← liftIO $ doesFileExistCaseSensitive snapshotFile
      if not b
        then throwError $ "The file " ++ snapshotFile ++ " does not exist"
        else
          whenM (liftIO $ diff file snapshotFile) $ do
            let msg ∷ String
                msg = "The files are different:\n" ++ file ++ "\n" ++ snapshotFile

            ifM (askTOpt optSnapshotNoError)
                (liftIO $ putStrLn msg)
                (throwError msg)
