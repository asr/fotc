------------------------------------------------------------------------------
-- Handling of Agda interface files (*.agdai)
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module MyAgda.Interface where

-- Haskell imports
-- import Data.Map ( Map )
import qualified Data.Map as Map
import System.Directory ( getCurrentDirectory )

-- Agda library imports
import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports ( readInterface )
import Agda.Interaction.Options
    ( CommandLineOptions
    , defaultOptions
    , optInputFile
    )
import Agda.Syntax.Abstract ( ModuleName )
import Agda.TypeChecking.Monad.Base
    ( axATP
    , Defn(Axiom)
    , Interface(iImportedModules)
    , Definition
    , Definitions
    , iSignature
    , runTCM
    , Signature(sigDefinitions)
    , theDef
    )
import Agda.TypeChecking.Monad.Options ( makeIncludeDirsAbsolute
                                       , setCommandLineOptions
                                       , Target(PersistentOptions)
                                       )
import Agda.Utils.FileName ( absolute, filePath, mkAbsolute )

-- Local imports
#include "../undefined.h"

------------------------------------------------------------------------------

getAxiomsATP :: Interface -> Definitions
getAxiomsATP i =
    Map.filter isAxiomATP $ sigDefinitions $ iSignature i

getImportedModules :: Interface -> [ModuleName]
getImportedModules i = iImportedModules i

getInterface :: FilePath -> IO Interface
getInterface file = do
  let opts :: CommandLineOptions
      opts = defaultOptions { optInputFile = Just file }

  aFile <- absolute file
  currentDir   <- getCurrentDirectory
  let iFile :: FilePath
      iFile  = filePath $ toIFile aFile

  r <- runTCM $ do
         setCommandLineOptions PersistentOptions opts
         makeIncludeDirsAbsolute $ mkAbsolute currentDir
         readInterface iFile

  case r of
        Right (Just i) -> return i
        Right Nothing  -> error $ "Error reading the interface file " ++ iFile
        Left _         -> error "Error from runTCM"

isAxiomATP :: Definition -> Bool
isAxiomATP def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just ("axiom", _)   -> True
                   Just _              -> False
                   Nothing             -> False

      _       -> False

    where defn :: Defn
          defn = theDef def

