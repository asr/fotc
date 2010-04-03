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
import Agda.Syntax.Abstract.Name
    ( ModuleName
    , Name(nameBindingSite)
    , QName(qnameName)
    )
import Agda.Syntax.Common ( RoleATP(..))
import Agda.Syntax.Position
    ( Interval(iStart)
    , Position(posLine)
    , rangeToInterval
    )
import Agda.TypeChecking.Monad.Base
    ( axATP
    , conATP
    , Defn(Axiom, Constructor, Function)
    , Interface(iImportedModules)
    , Definition
    , Definitions
    , funATP
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
import Agda.Utils.Impossible ( Impossible(..)
                             , throwImpossible
                             )

-- Local imports
import Common.Types ( HintName )

#include "../undefined.h"

------------------------------------------------------------------------------

getRoleATP :: RoleATP -> Interface -> Definitions
getRoleATP role i = Map.filter (isRole role) $ sigDefinitions $ iSignature i
    where isRole :: RoleATP -> Definition -> Bool
          isRole AxiomATP      = isAxiomATP
          isRole ConjectureATP = isConjectureATP
          isRole HintATP       = isHintATP

getHintsATP :: Interface -> Definitions
getHintsATP i =
    Map.filter isAxiomATP $ sigDefinitions $ iSignature i

-- Invariant: The definition must correspond to an ATP conjecture
getConjectureHints :: Definition -> [HintName]
getConjectureHints def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just (ConjectureATP, hints) -> hints
                   Just _                      -> __IMPOSSIBLE__
                   Nothing                     -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

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
                   Just (AxiomATP, _) -> True
                   Just _             -> False
                   Nothing            -> False

      _       -> False

    where defn :: Defn
          defn = theDef def

-- ToDo: Unify with 'isAxiomATP'
isConjectureATP :: Definition -> Bool
isConjectureATP def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just (ConjectureATP, _) -> True
                   Just _                  -> False
                   Nothing                 -> False

      _       -> False

    where defn :: Defn
          defn = theDef def

isHintATP :: Definition -> Bool
isHintATP def =
    case defn of
      Constructor{} -> case conATP defn of
                         Just HintATP -> True
                         Just _       -> __IMPOSSIBLE__
                         Nothing      -> False

      Function{}    -> case funATP defn of
                         Just HintATP -> True
                         Just _       -> __IMPOSSIBLE__
                         Nothing      -> False

      _             -> False

    where defn :: Defn
          defn = theDef def

getQNameDefinition :: Interface -> QName -> Maybe Definition
getQNameDefinition i qName = Map.lookup qName $ sigDefinitions $ iSignature i

-- The line where a QNname is defined.
qNameLine :: QName -> Int
qNameLine q =
    case rangeToInterval $ nameBindingSite $ qnameName q of
      Nothing -> __IMPOSSIBLE__
      Just i  -> posLine $ iStart i