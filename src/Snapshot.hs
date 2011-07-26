------------------------------------------------------------------------------
-- Snapshot test
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Snapshot ( snapshotTest ) where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.Error ( throwError )
import Control.Monad.State ( get )
import Control.Monad.Trans ( liftIO )

import System.Directory ( doesFileExist )
import System.FilePath  ( replaceDirectory )

-- Local imports
import Monad.Base      ( T, TState(tOpts) )
import Options         ( Options(optOutputDir, optSnapshotDir) )
import Monad.Reports   ( reportS )
import Utils.Directory ( diff )

------------------------------------------------------------------------------

snapshotTest ∷ FilePath → T ()
snapshotTest file = do

  state ← get

  let opts ∷ Options
      opts = tOpts state

      outputDir ∷ FilePath
      outputDir = optOutputDir opts

      snapshotDir ∷ FilePath
      snapshotDir = optSnapshotDir opts

      snapshotFile ∷ FilePath
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
                 "The files " ++ file ++ " and " ++ snapshotFile ++
                 " are different"
            else reportS "" 1 $
                 "The files " ++ file ++ " and " ++ snapshotFile ++
                 " are the same"
