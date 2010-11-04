------------------------------------------------------------------------------
-- Handling of Agda interface files (*.agdai)
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaLib.Interface
    ( getClauses
    , getImportedInterfaces
    , getLocalHints
    , getQNameDefinition
    , getQNameInterface
    , getQNameType
    , getRoleATP
    , myGetInterface
    , myReadInterface
    , qNameLine
    )
    where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Reader ( ask )
import Control.Monad.Trans.State ( evalStateT, get, put, StateT )

import Data.Int ( Int32 )
-- import Data.Map ( Map )
import qualified Data.Map as Map ( filter, lookup )
import Data.Maybe ( fromMaybe )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports  ( getInterface, readInterface )
import Agda.Interaction.Options
    ( CommandLineOptions(optIncludeDirs)
    , defaultOptions
    , defaultPragmaOptions
    , PragmaOptions(optVerbose)
    , Verbosity
    )
import Agda.Syntax.Abstract.Name
    ( ModuleName(MName)
    , Name(nameBindingSite)
    , QName(QName)
    , qnameName
    )
import Agda.Syntax.Common
    ( RoleATP(AxiomATP, ConjectureATP, DefinitionATP, HintATP) )
import Agda.Syntax.Internal ( Clause, translatedClause, Type )
import Agda.Syntax.Position
    ( Interval(iStart)
    , Position(posLine)
    , rangeToInterval
    )
import Agda.TypeChecking.Monad.Base
    ( axATP
    , conATP
    , Defn(Axiom, Constructor, Function)
    , Interface(iImportedModules, iModuleName)
    , Definition(defType)
    , Definitions
    , funATP
    , funClauses
    , iSignature
    , runTCM
    , Signature(sigDefinitions)
    , theDef
    )
import Agda.TypeChecking.Monad.Options
    ( setCommandLineOptions
    , setPragmaOptions
    )
import Agda.Utils.FileName
    ( absolute
    , filePath
--    , mkAbsolute
    )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import qualified Agda.Utils.Trie as Trie ( singleton )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.Syntax.Abstract.Name ( removeLastNameModuleName )
import Common ( ER )
import Options ( Options(optAgdaIncludePath) )
import Reports ( reportSLn )

#include "../undefined.h"

------------------------------------------------------------------------------

getRoleATP :: RoleATP → Interface → Definitions
getRoleATP role i = Map.filter (isRole role) $ sigDefinitions $ iSignature i
    where
      isRole :: RoleATP → Definition → Bool
      isRole AxiomATP      = isAxiomATP
      isRole ConjectureATP = isConjectureATP
      isRole DefinitionATP = isDefinitionATP
      isRole HintATP       = isHintATP

-- getHintsATP :: Interface → Definitions
-- getHintsATP i = Map.filter isAxiomATP $ sigDefinitions $ iSignature i

-- Invariant: The Definition must correspond to an ATP conjecture.
getLocalHints :: Definition → [QName]
getLocalHints def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                    Just (ConjectureATP, hints) → hints
                    Just _                      → __IMPOSSIBLE__
                    Nothing                     → __IMPOSSIBLE__

       _       → __IMPOSSIBLE__

-- An empty list of relative include directories (Left []) is
-- interpreted as ["."] (from
-- Agda.TypeChecking.Monad.Options). Therefore the default of
-- Options.optAgdaIncludePath is [].
agdaCommandLineOptions :: ER CommandLineOptions
agdaCommandLineOptions = do

  opts <- lift ask

  let agdaIncludePaths :: [FilePath]
      agdaIncludePaths = optAgdaIncludePath opts

  return $ defaultOptions { optIncludeDirs = Left agdaIncludePaths }

-- TODO: It is not working.
agdaPragmaOptions :: PragmaOptions
agdaPragmaOptions =
  -- We do not want any verbosity from the Agda API.
  let agdaOptVerbose :: Verbosity
      agdaOptVerbose = Trie.singleton [] 0

  in defaultPragmaOptions { optVerbose = agdaOptVerbose }

myReadInterface :: FilePath → ER Interface
myReadInterface file = do

  optsCommandLine ← agdaCommandLineOptions

  -- The physical interface file.
  iFile ← liftIO $ fmap (filePath . toIFile) (absolute file)

  r ← liftIO $ runTCM $ do
         setCommandLineOptions optsCommandLine
         setPragmaOptions agdaPragmaOptions
         readInterface iFile

  case r of
        Right (Just i) → return i
        Right Nothing  → error $ "Error reading the interface file " ++ iFile
        Left  _        → error "Error from runTCM in myReadInterface"

myGetInterface :: ModuleName → ER (Maybe Interface)
myGetInterface x = do

  optsCommandLine ← agdaCommandLineOptions

  r ← liftIO $ runTCM $ do
         setCommandLineOptions optsCommandLine
         setPragmaOptions agdaPragmaOptions
         getInterface x

  case r of
        Right (i, _) → return (Just i)
        Left  _      → return Nothing

isAxiomATP :: Definition → Bool
isAxiomATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                    Just (AxiomATP, _ )      → True
                    Just (ConjectureATP, _ ) → False
                    Just _                   → __IMPOSSIBLE__
                    Nothing                  → False

       _       → False

-- TODO: Unify with 'isAxiomATP'
isConjectureATP :: Definition → Bool
isConjectureATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                    Just (AxiomATP, _ )      → False
                    Just (ConjectureATP, _ ) → True
                    Just _                   → __IMPOSSIBLE__
                    Nothing                  → False

       _       → False

isDefinitionATP :: Definition → Bool
isDefinitionATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Function{} → case funATP defn of
                      Just DefinitionATP → True
                      Just HintATP       → False
                      Just _             → __IMPOSSIBLE__
                      Nothing            → False

       _          → False

isHintATP :: Definition → Bool
isHintATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Constructor{} → case conATP defn of
                          Just HintATP → True
                          Just _       → __IMPOSSIBLE__
                          Nothing      → False

       Function{}    → case funATP defn of
                          Just DefinitionATP → False
                          Just HintATP       → True
                          Just _             → __IMPOSSIBLE__
                          Nothing            → False

       _             → False

getQNameDefinition :: Interface → QName → Definition
getQNameDefinition i qName =
    fromMaybe __IMPOSSIBLE__ $ Map.lookup qName $ sigDefinitions $ iSignature i

-- The modules names in a QName can to correspond to logical modules,
-- e.g. sub-modules, data types or records. This function finds the
-- interface associated with a QName.
getQNameInterface :: QName → ER Interface
getQNameInterface (QName qNameModule qName) =
  case qNameModule of
    (MName [])  → __IMPOSSIBLE__
    (MName _ )  → do
      im ← myGetInterface qNameModule
      case im of
        Nothing → getQNameInterface
                    (QName (removeLastNameModuleName qNameModule) qName)
        Just i  → return i

getQNameType :: Interface → QName → Type
getQNameType i qName = defType $ getQNameDefinition i qName

-- The line where a QNname is defined.
qNameLine :: QName → Int32
qNameLine q =
    case rangeToInterval $ nameBindingSite $ qnameName q of
      Nothing → __IMPOSSIBLE__
      Just i  → posLine $ iStart i

getClauses :: Definition → [Clause]
getClauses def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Function{} → map translatedClause $ funClauses defn
       _          → __IMPOSSIBLE__

------------------------------------------------------------------------------
-- Imported interfaces

allInterfaces :: [ModuleName] → StateT [ModuleName] ER [Interface]
allInterfaces []       = return []
allInterfaces (x : xs) = do
  visitedModules ← get

  if x `notElem` visitedModules
    then do
      put $ x : visitedModules

      im ← lift $ myGetInterface x

      let i :: Interface
          i = fromMaybe __IMPOSSIBLE__ im

      let iModules :: [ModuleName]
          iModules = iImportedModules i

      -- TODO: Test allInterfaces (xs ++ iModules)
      is1 ← allInterfaces xs
      is2 ← allInterfaces iModules
      return $ i : is1 ++ is2

    else return []

getImportedInterfacesAux :: Interface → StateT [ModuleName] ER [Interface]
getImportedInterfacesAux i = do
  let iModules :: [ModuleName]
      iModules = iImportedModules i

  allInterfaces iModules

-- Return the interfaces recursively imported by the main interface.
getImportedInterfaces :: Interface → ER [Interface]
getImportedInterfaces i = do
  interfaces ← evalStateT (getImportedInterfacesAux i) []
  lift $ reportSLn "ii" 20 $
           "Module names: " ++ show (map iModuleName interfaces)
  lift $ reportSLn "ii" 20 $
           "Total imported interfaces: " ++ show (length interfaces)
  return interfaces
