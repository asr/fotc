{-# LANGUAGE CPP, FlexibleInstances #-}

module Main where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Trans.Reader ( ask, ReaderT, runReaderT )
import Control.Monad.Trans.State ( evalState )

-- import Control.Monad.Trans

import Data.Map ( Map )
import qualified Data.Map as Map
-- import Data.Maybe

import Prelude hiding ( print, putStr, putStrLn )

import System.Environment
import System.Exit

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Common ( RoleATP )
import Agda.Syntax.Internal ( Type )

import Agda.TypeChecking.Monad.Base
    ( axATP
    , Defn(Axiom)
    , Definition
    , Definitions
    , defType
    , Interface
    , iSignature
    , Signature(sigDefinitions)
    , theDef
    )

import Agda.Utils.Impossible ( catchImpossible
                             , Impossible(..)
                             , throwImpossible
                             )
import qualified Agda.Utils.IO.Locale as LocIO

------------------------------------------------------------------------------
-- Local imports
-- import FOL.Pretty
import Common.Types ( HintName, PostulateName )
import FOL.Monad ( initialVars )
import FOL.Translation
import FOL.Types
import MyAgda.Interface ( getInterface )
import Options ( Options, parseOptions )
import TPTP.Files
import TPTP.Monad
import TPTP.Translation
import TPTP.Types

#include "undefined.h"

------------------------------------------------------------------------------

printListLn :: Show a => [a] -> IO ()
printListLn []       = return ()
printListLn (x : xs) = do LocIO.putStrLn $ show x ++ "\n"
                          printListLn xs

isPostulatePragmaATP :: Definition -> Bool
isPostulatePragmaATP def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just _   -> True
                   Nothing  -> False

      _       -> False  -- Only the postulates can be a ATP pragma.

    where defn :: Defn
          defn = theDef def

isPostulateTheorem :: Definition -> Bool
isPostulateTheorem def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just ("theorem", _)   -> True
                   Just _                -> False
                   Nothing               -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

getPostulateRole :: Definition -> RoleATP
getPostulateRole def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just (role, _) -> role
                   Nothing        -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

-- Only the theorems have associated hints.
getPostulateHints :: Definition -> [HintName]
getPostulateHints def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just ("theorem", hints) -> hints
                   Just _                  -> __IMPOSSIBLE__
                   Nothing                 -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

getPostulates :: Interface -> Definitions
getPostulates i =
    Map.filter isPostulatePragmaATP $ sigDefinitions $ iSignature i

postulatesToFOLs :: Interface -> ReaderT Options IO ()
postulatesToFOLs i = do

  opts <- ask

  -- We get the ATP pragmas postulates.
  let postulatesDefs :: Definitions
      postulatesDefs = getPostulates i
  -- LocIO.print $ Map.keys postulatesDef

  -- We get the types of the postulates.
  let postulatesTypes :: Map PostulateName Type
      postulatesTypes = Map.map defType postulatesDefs

  liftIO $ LocIO.putStrLn "Postulates types:"
  liftIO $ printListLn $ Map.toList postulatesTypes

  -- The postulates types are translated to FOL formulas.
  formulas <- liftIO $
              mapM (\ty -> runReaderT (typeToFormula ty) (opts, initialVars))
                   (Map.elems postulatesTypes)

  -- The postulates are associated with their FOL formulas.
  let postulatesFormulas :: Map PostulateName Formula
      postulatesFormulas = Map.fromList $ zip (Map.keys postulatesTypes) formulas

  liftIO $ LocIO.putStrLn "FOL formulas:"
  liftIO $ printListLn $ Map.toList postulatesFormulas

  -- The postulates are associated with their roles.
  let postulatesRoles :: Map PostulateName RoleATP
      postulatesRoles = Map.map getPostulateRole postulatesDefs

  let afs :: [AnnotatedFormula]
      afs = evalState
              (mapM (\(pName, role, formula) ->
                       (postulateToTPTP pName role formula))
                    (zip3 (Map.keys postulatesFormulas)
                         (Map.elems postulatesRoles)
                         (Map.elems postulatesFormulas)))
              initialNames


  -- liftIO $ LocIO.putStrLn "TPTP formulas:"
  -- liftIO $ LocIO.print afs

  -- The postulates (which are theorems) are associated with their hints.
  let postulatesHints :: Map PostulateName [HintName]
      postulatesHints =
          Map.map getPostulateHints $
             Map.filter isPostulateTheorem postulatesDefs

  liftIO $ LocIO.putStrLn "Hints:"
  liftIO $ LocIO.print postulatesHints

  liftIO $ createFilesTPTP afs

runAgdaATP :: IO ()
runAgdaATP = do
  prgName <- getProgName
  argv <- getArgs --fmap head $ liftIO getArgs

  -- Reading the command line options.
  (opts, names) <- parseOptions argv prgName

  -- Gettting the interface.
  i <- getInterface $ head names

  runReaderT (postulatesToFOLs i) opts

main :: IO ()
main = catchImpossible runAgdaATP $
         \e -> do LocIO.putStr $ show e
                  exitFailure
