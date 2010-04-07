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
    ( Name(nameBindingSite)
    , QName(qnameName)
    )
import Agda.Syntax.Common ( RoleATP(..))
import Agda.Syntax.Internal ( Clause )
import Agda.Syntax.Position
    ( Interval(iStart)
    , Position(posLine)
    , rangeToInterval
    )
import Agda.TypeChecking.Monad.Base
    ( axATP
    , conATP
    , Defn(Axiom, Constructor, Function)
    , Interface
    , Definition
    , Definitions
    , funATP
    , funClauses
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
          isRole DefinitionATP = isDefinitionATP
          isRole HintATP       = isHintATP

getHintsATP :: Interface -> Definitions
getHintsATP i =
    Map.filter isAxiomATP $ sigDefinitions $ iSignature i

-- Invariant: The definition must correspond to an ATP conjecture
getConjectureHints :: Definition -> [HintName]
getConjectureHints def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} -> case axATP defn of
                    Just (ConjectureATP, hints) -> hints
                    Just _                      -> __IMPOSSIBLE__
                    Nothing                     -> __IMPOSSIBLE__

       _       -> __IMPOSSIBLE__

-- getImportedModules :: Interface -> [ModuleName]
-- getImportedModules i = iImportedModules i

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
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} -> case axATP defn of
                    Just (AxiomATP, _)      -> True
                    Just (ConjectureATP, _) -> False
                    Just _                  -> __IMPOSSIBLE__
                    Nothing                 -> False

       _       -> False

-- ToDo: Unify with 'isAxiomATP'
isConjectureATP :: Definition -> Bool
isConjectureATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Axiom{} -> case axATP defn of
                    Just (AxiomATP, _)      -> False
                    Just (ConjectureATP, _) -> True
                    Just _                  -> __IMPOSSIBLE__
                    Nothing                 -> False

       _       -> False

isDefinitionATP :: Definition -> Bool
isDefinitionATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Function{}    -> case funATP defn of
                          Just DefinitionATP -> True
                          Just HintATP       -> False
                          Just _             -> __IMPOSSIBLE__
                          Nothing            -> False

       _             -> False

isHintATP :: Definition -> Bool
isHintATP def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Constructor{} -> case conATP defn of
                          Just HintATP       -> True
                          Just _             -> __IMPOSSIBLE__
                          Nothing            -> False

       Function{}    -> case funATP defn of
                          Just DefinitionATP -> False
                          Just HintATP       -> True
                          Just _             -> __IMPOSSIBLE__
                          Nothing            -> False

       _             -> False

getQNameDefinition :: Interface -> QName -> Maybe Definition
getQNameDefinition i qName = Map.lookup qName $ sigDefinitions $ iSignature i

-- The line where a QNname is defined.
qNameLine :: QName -> Int
qNameLine q =
    case rangeToInterval $ nameBindingSite $ qnameName q of
      Nothing -> __IMPOSSIBLE__
      Just i  -> posLine $ iStart i

getClauses :: Definition -> [Clause]
getClauses def =
  let defn :: Defn
      defn = theDef def
  in case defn of
       Function{} -> funClauses defn
       _          -> __IMPOSSIBLE__
