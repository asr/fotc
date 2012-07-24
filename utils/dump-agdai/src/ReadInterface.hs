{-# LANGUAGE UnicodeSyntax #-}

module ReadInterface where

------------------------------------------------------------------------------
-- Haskell imports
import System.Directory ( getCurrentDirectory )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports  ( readInterface )

import Agda.Interaction.Options
  ( CommandLineOptions
  , defaultOptions
  , optIncludeDirs
  )

import Agda.TypeChecking.Monad.Base    ( Interface, runTCM )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions )
import Agda.Utils.FileName             ( absolute, filePath, mkAbsolute )

------------------------------------------------------------------------------

stdlibPath ∷ String
stdlibPath = "/home/asr/src/agdas/agda-upstream/std-lib/src/"

myReadInterface :: FilePath → IO Interface
myReadInterface file = do

  absFile    ← absolute file
  currentDir ← getCurrentDirectory

  -- It is necessary to set up all the include directories used to
  -- read the Agda interface file.
  let opts ∷ CommandLineOptions
      opts = defaultOptions
             { optIncludeDirs =
                 Right [ mkAbsolute currentDir
                       , mkAbsolute stdlibPath
                       ]
             }

  r ← runTCM $ do
    setCommandLineOptions opts
    -- makeIncludeDirsAbsolute $ mkAbsolute currentDir
    -- makeIncludeDirsAbsolute $ mkAbsolute std_lib_path
    readInterface $ filePath $ toIFile absFile

  case r of
    Right (Just i) → return i
    Right Nothing  → error "Error reading the interface file."
    Left _         → error "Error from runTCM."
