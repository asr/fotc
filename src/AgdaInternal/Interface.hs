------------------------------------------------------------------------------
-- |
-- Module      : AgdaInternal.Interface
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Handling of Agda interface files (*.agdai).
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module AgdaInternal.Interface
  ( getATPAxioms
  , getATPConjectures
  , getATPHints
  , getClauses
  , getImportedInterfaces
  , getLocalHints
  , isATPDefinition
  , isProjection
  , myReadInterface
  , qNameDefinition
  , QNamesIn(qNamesIn)
  , qNameLine
  , qNameType
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.Error ( MonadError(throwError) )
import Control.Monad.State ( evalStateT, MonadState(get, put), StateT )
import Control.Monad.Trans ( MonadIO(liftIO), MonadTrans(lift) )

import Data.Functor ( (<$>) )
import Data.Int     ( Int32 )

import qualified Data.HashMap.Strict as HashMap ( filter, lookup )

import Data.Maybe ( fromMaybe, isJust )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports  ( getInterface, readInterface )

import Agda.Interaction.Options
  ( CommandLineOptions(optIncludeDirs, optPragmaOptions)
  , defaultOptions
  , defaultPragmaOptions
  , PragmaOptions(optVerbose)
  , Verbosity
  )

import Agda.Syntax.Abstract.Name
  ( ModuleName
  , Name(nameBindingSite)
  , QName(qnameName)
  )

import Agda.Syntax.Common
  ( Arg(Arg)
  , ATPRole(ATPAxiom, ATPConjecture, ATPDefinition, ATPHint)
  , Dom(Dom)
  )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Clause(Clause)
  , ClauseBody(Bind, Body, NoBody)
  , Term(Con, Def, DontCare, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Type(El)
  )

import Agda.Syntax.Position
  ( Interval(iStart)
  , Position(posLine)
  , rangeToInterval
  )

import Agda.TypeChecking.Monad.Base
  ( Defn(Axiom
        , axATP
        , conATP
        , Constructor
        , Function
        , funATP
        , funClauses
        , funProjection
        )
  , Definition(defType, theDef)
  , Definitions
  , Interface(iImportedModules, iModuleName)
  , runTCM
  , TCErr
  )

import Agda.TypeChecking.Monad.Options ( setCommandLineOptions )

import Agda.Utils.FileName
  ( absolute
  , doesFileExistCaseSensitive
  , filePath
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( unlessM )

import qualified Agda.Utils.Trie as Trie ( singleton )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base    ( getTDefs, getTOpt, T )
import Monad.Reports ( reportSLn )
import Options       ( Options(optAgdaIncludePath) )

#include "../undefined.h"

------------------------------------------------------------------------------

getATPRole ∷ ATPRole → Definitions → Definitions
getATPRole ATPAxiom      = HashMap.filter isATPAxiom
getATPRole ATPConjecture = HashMap.filter isATPConjecture
-- 31 May 2012. We don't have an example of this case.
--
-- getATPRole ATPDefinition = HashMap.filter isATPDefinition
getATPRole ATPDefinition = __IMPOSSIBLE__
getATPRole ATPHint       = HashMap.filter isATPHint

-- | Return the ATP axioms from a set of Agda 'Definitions'.
getATPAxioms ∷ Definitions → Definitions
getATPAxioms = getATPRole ATPAxiom

-- | Return the ATP conjectures from a set of Agda 'Definitions'.
getATPConjectures ∷ Definitions → Definitions
getATPConjectures = getATPRole ATPConjecture

-- getATPDefinitions ∷ Definitions → Definitions
-- getATPDefinitions = getATPRole ATPDefinition

-- | Return the ATP hints from a set of Agda 'Definitions'.
getATPHints ∷ Definitions → Definitions
getATPHints = getATPRole ATPHint

-- Invariant: The @Definition@ must correspond to an ATP conjecture.
-- | Return the ATP local hints associated with an ATP conjecture.
getLocalHints ∷ Definition → [QName]
getLocalHints def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                   Just (ATPConjecture, hints) → hints
                   Just _                      → __IMPOSSIBLE__
                   Nothing                     → __IMPOSSIBLE__

       _       → __IMPOSSIBLE__

-- We do not want any verbosity from the Agda API.
agdaPragmaOptions ∷ PragmaOptions
agdaPragmaOptions = let agdaOptVerbose ∷ Verbosity
                        agdaOptVerbose = Trie.singleton [] 0
                    in defaultPragmaOptions { optVerbose = agdaOptVerbose }

-- An empty list of relative include directories @(Left [])@ is
-- interpreted as @["."]@ (from
-- Agda.TypeChecking.Monad.Options). Therefore the default of
-- Options.optAgdaIncludePath is @[]@.
agdaCommandLineOptions ∷ T CommandLineOptions
agdaCommandLineOptions = do
  agdaIncludePaths ← getTOpt optAgdaIncludePath

  return $ defaultOptions { optIncludeDirs   = Left agdaIncludePaths
                          , optPragmaOptions = agdaPragmaOptions
                          }

-- | Read an Agda interface file.
myReadInterface ∷ FilePath → T Interface
myReadInterface file = do
  optsCommandLine ← agdaCommandLineOptions

  -- The physical Agda file (used only to test if the file exists).
  pFile ∷ FilePath ← liftIO $ fmap filePath (absolute file)

  unlessM (liftIO $ doesFileExistCaseSensitive pFile)
          (throwError $ "The file " ++ pFile ++ " does not exist")

  -- The physical Agda interface file.
  iFile ∷ FilePath ← liftIO $ fmap (filePath . toIFile) (absolute file)

  unlessM (liftIO $ doesFileExistCaseSensitive iFile)
          (throwError $ "The interface file " ++ iFile
                        ++ " does not exist. Use Agda to generate it")

  r ∷ Either TCErr (Maybe Interface) ← liftIO $ runTCM $
    do setCommandLineOptions optsCommandLine
       readInterface iFile

  case r of
    Right (Just i) → return i
    Right Nothing  → throwError $
                       "The reading of the interface file "
                       ++ iFile ++ " failed. "
                       ++ "It is possible that you used a different version "
                       ++ "of Agda to build the agda2atp tool and to "
                       ++ "type-check your module"
    Left  _        → throwError "From runTCM in myReadInterface"

myGetInterface ∷ ModuleName → T (Maybe Interface)
myGetInterface x = do
  optsCommandLine ← agdaCommandLineOptions

  r ← liftIO $ runTCM $ do
    setCommandLineOptions optsCommandLine
    getInterface x

  case r of
    Right (i, _) → return (Just i)
    -- 31 May 2012. We don't have an example of this case.
    --
    -- Left  _      → return Nothing
    Left _ → __IMPOSSIBLE__

-- | Return 'True' if an Agda 'Definition' is an ATP axiom.
isATPAxiom ∷ Definition → Bool
isATPAxiom def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                   Just (ATPAxiom, _)      → True
                   Just (ATPConjecture, _) → False
                   Just _                  → __IMPOSSIBLE__
                   Nothing                 → False

       Constructor{} → case conATP defn of
                         Just ATPAxiom → True
                         Just _        → __IMPOSSIBLE__
                         Nothing       → False

       _       → False

-- | Return 'True' if an Agda 'Definition' is an ATP conjecture.
isATPConjecture ∷ Definition → Bool
isATPConjecture def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Axiom{} → case axATP defn of
                   Just (ATPAxiom, _)      → False
                   Just (ATPConjecture, _) → True
                   Just _                  → __IMPOSSIBLE__
                   Nothing                 → False

       _       → False

-- | Return 'True' if an Agda 'Definition' is an ATP definition.
isATPDefinition ∷ Definition → Bool
isATPDefinition def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Function{} → case funATP defn of
                      Just ATPDefinition → True
                      -- 31 May 2012. We don't have an example of this
                      -- case.
                      --
                      -- Just ATPHint       → False
                      Just _       → __IMPOSSIBLE__
                      Nothing      → False

       _          → False

-- | Return 'True' if an Agda 'Definition' is an ATP hint.
isATPHint ∷ Definition → Bool
isATPHint def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Function{}    → case funATP defn of
                         Just ATPDefinition → False
                         Just ATPHint       → True
                         Just _             → __IMPOSSIBLE__
                         Nothing            → False

       _             → False

-- | Return the Agda 'Definition' associated with a 'QName'.
qNameDefinition ∷ QName → T Definition
qNameDefinition qName = do
  allDefs ← getTDefs
  return $ fromMaybe (__IMPOSSIBLE__) $ HashMap.lookup qName allDefs

-- | Return the 'Type' of a 'QNname'.
qNameType ∷ QName → T Type
qNameType qName = fmap defType $ qNameDefinition qName

-- | Return the line where a 'QNname' is defined.
qNameLine ∷ QName → Int32
qNameLine qName =
  case rangeToInterval $ nameBindingSite $ qnameName qName of
    Nothing → __IMPOSSIBLE__
    Just i  → posLine $ iStart i

-- | Return the 'Clause's associted with an Agda 'Definition'.
getClauses ∷ Definition → [Clause]
getClauses def =
  let defn ∷ Defn
      defn = theDef def
  in case defn of
       Function{} → funClauses defn
       _          → __IMPOSSIBLE__

-- | Return the 'QName's in an entity.
class QNamesIn a where
  qNamesIn ∷ a → [QName]

instance QNamesIn a ⇒ QNamesIn [a] where
  qNamesIn = concatMap qNamesIn

instance QNamesIn a ⇒ QNamesIn (Arg a) where
  qNamesIn (Arg _ _ e) = qNamesIn e

instance QNamesIn a ⇒ QNamesIn (Dom a) where
  qNamesIn (Dom _ _ e) = qNamesIn e

instance QNamesIn a ⇒ QNamesIn (Abs a) where
  qNamesIn (Abs _ e)   = qNamesIn e
  qNamesIn (NoAbs _ e) = qNamesIn e

instance QNamesIn Term where
  qNamesIn (Con qName args) = qName : qNamesIn args
  qNamesIn (Def qName args) = qName : qNamesIn args
  qNamesIn (Lam _ absTerm)  = qNamesIn absTerm
  qNamesIn (Pi domTy absTy) = qNamesIn domTy ++ qNamesIn absTy
  qNamesIn (Sort _)         = []
  qNamesIn (Var _ args)     = qNamesIn args

  qNamesIn (DontCare _) = __IMPOSSIBLE__
  qNamesIn (Level _)    = __IMPOSSIBLE__
  qNamesIn (Lit _)      = __IMPOSSIBLE__
  qNamesIn (MetaV _ _)  = __IMPOSSIBLE__

instance QNamesIn Type where
  qNamesIn (El _ term) = qNamesIn term

instance QNamesIn ClauseBody where
  qNamesIn (Body term)          = qNamesIn term
  qNamesIn (Bind absClauseBody) = qNamesIn absClauseBody
  -- 31 May 2012. We don't have an example of this case.
  --
  -- qNamesIn NoBody               = []
  qNamesIn NoBody = __IMPOSSIBLE__

instance QNamesIn Clause where
  qNamesIn (Clause _ _ _ _ body) = qNamesIn body

instance QNamesIn Definition where
  qNamesIn def = qNamesIn $ defType def

-- Adapted from Agda.TypeChecking.Monad.Signature.isProjection.
projection ∷ QName → T (Maybe (QName, Int))
projection qname = do
  defn ← theDef <$> qNameDefinition qname
  case defn of
    Function { funProjection = result } → return result
    _                                   → return Nothing

-- | Is it the 'Qname' a projection?
isProjection ∷ QName → T Bool
isProjection qname = isJust <$> projection qname

------------------------------------------------------------------------------
-- Imported interfaces

importedInterfaces ∷ ModuleName → StateT [ModuleName] T [Interface]
importedInterfaces x = do
  visitedModules ← get

  if x `notElem` visitedModules
    then do
      put $ x : visitedModules

      im ← lift $ myGetInterface x

      let i ∷ Interface
          i = fromMaybe (__IMPOSSIBLE__) im

      let iModules ∷ [ModuleName]
          iModules = iImportedModules i

      is ← fmap concat $ mapM importedInterfaces iModules
      return $ i : is
    else return []

-- | Return the Agda interface files recursively imported by the top
-- level interface file.
getImportedInterfaces ∷ Interface → T [Interface]
getImportedInterfaces i = do
  iInterfaces ← fmap concat $
                evalStateT (mapM importedInterfaces $ iImportedModules i) []
  reportSLn "ii" 20 $
    "Imported module names: " ++ show (map iModuleName iInterfaces)
  return iInterfaces
