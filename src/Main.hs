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

import System.Directory ( getCurrentDirectory )
import System.Environment
import System.Exit

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports ( readInterface )
import Agda.Interaction.Options
    ( CommandLineOptions
    , defaultOptions
    , optInputFile
    )
import Agda.Syntax.Common ( RoleATP )
import Agda.Syntax.Internal ( QName, Type )

import Agda.TypeChecking.Monad.Base
    ( axATP
    , Defn(Axiom)
    , Definition
    , Definitions
    , defType
    , Interface
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
import Agda.Utils.Impossible ( catchImpossible
                             , Impossible(..)
                             , throwImpossible
                             )
import qualified Agda.Utils.IO.Locale as LocIO

------------------------------------------------------------------------------
-- Local imports
-- import FOL.Pretty
import FOL.Monad ( initialVars )
import FOL.Translation
import FOL.Types
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

isQNamePragma :: Definition -> Bool
isQNamePragma def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just _   -> True
                   Nothing  -> False

      _       -> False  -- Only the postulates can be a ATP pragma.

    where defn :: Defn
          defn = theDef def

getPragmaRole :: Definition -> RoleATP
getPragmaRole def =
    case defn of
      Axiom{} -> case axATP defn of
                   Just (role, _) -> role
                   Nothing        -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

getPragmas :: Interface -> Definitions
getPragmas i =
    Map.filter isQNamePragma $ sigDefinitions $ iSignature i

pragmaToFOLs :: Interface -> ReaderT Options IO ()
pragmaToFOLs i = do

  opts <- ask

  -- We get the ATP pragma QNames
  let pragmaQnames :: Definitions
      pragmaQnames = getPragmas i
  -- LocIO.print $ Map.keys pragmaQnames

  -- We get the types of the ATP pragma QNames.
  let qNamesTypes :: Map QName Type
      qNamesTypes = Map.map defType pragmaQnames

  liftIO $ LocIO.putStrLn "Types:"
  liftIO $ printListLn $ Map.toList qNamesTypes

  -- The Agda types of the ATP pragmas QNames are translated to FOL formulas.
  formulas <- liftIO $
              mapM (\ty -> runReaderT (typeToFormula ty) (opts, initialVars))
                   (Map.elems qNamesTypes)

  -- The ATP pragmas QNames are associated with their FOL formulas.
  let qNamesFOLFormulas :: Map QName Formula
      qNamesFOLFormulas = Map.fromList $ zip (Map.keys qNamesTypes) formulas

  liftIO $ LocIO.putStrLn "FOL formulas:"
  liftIO $ printListLn $ Map.toList qNamesFOLFormulas

  -- The ATP pragmas QNames are associated with their roles.
  let qNamesPragmaRole :: Map QName RoleATP
      qNamesPragmaRole = Map.map getPragmaRole pragmaQnames

  let afs :: [AnnotatedFormula]
      afs = evalState
              (mapM (\(qName, role, formula) ->
                       (pragmaToTPTP qName role formula))
                    (zip3 (Map.keys qNamesFOLFormulas)
                         (Map.elems qNamesPragmaRole)
                         (Map.elems qNamesFOLFormulas)))
              initialNames


  -- liftIO $ LocIO.putStrLn "TPTP formulas:"
  -- liftIO $ LocIO.print afs

  liftIO $ createFilesTPTP afs

getInterface :: FilePath -> IO Interface
getInterface agdaFile = do
  let opts :: CommandLineOptions
      opts = defaultOptions { optInputFile = Just agdaFile }

  aFile <- absolute agdaFile
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

runAgdaATP :: IO ()
runAgdaATP = do
  prgName <- getProgName
  argv <- getArgs --fmap head $ liftIO getArgs

  -- Reading the command line options.
  (opts, names) <- parseOptions argv prgName

  -- Gettting the interface.
  i <- getInterface $ head names

  runReaderT (pragmaToFOLs i) opts

main :: IO ()
main = catchImpossible runAgdaATP $
         \e -> do LocIO.putStr $ show e
                  exitFailure
