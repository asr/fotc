{-# LANGUAGE CPP, FlexibleInstances #-}

module Main where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.Reader
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
import Agda.Syntax.Internal ( QName, Type )

import Agda.TypeChecking.Monad.Base
    ( axExternalDef
    , Defn(Axiom)
    , Definition
    , Definitions
    , defType
    , ExternalRole
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
import FOL.Translation
import FOL.Types
import Monad ( initialVars )
import Options ( Options, parseOptions )
import TPTP.Translation
import TPTP.Types

#include "undefined.h"

------------------------------------------------------------------------------

printListLn :: Show a => [a] -> IO ()
printListLn []       = return ()
printListLn (x : xs) = do LocIO.putStrLn $ show x ++ "\n"
                          printListLn xs

isQNameExternal :: Definition -> Bool
isQNameExternal def =
    case defn of
      Axiom{} -> case axExternalDef defn of
                   Just _   -> True
                   Nothing  -> False

      _       -> False  -- Only the postulates can be EXTERNAL.

    where defn :: Defn
          defn = theDef def

getExternalRole :: Definition -> ExternalRole
getExternalRole def =
    case defn of
      Axiom{} -> case axExternalDef defn of
                   Just role   -> role
                   Nothing  -> __IMPOSSIBLE__

      _       -> __IMPOSSIBLE__

    where defn :: Defn
          defn = theDef def

getExternals :: Interface -> Definitions
getExternals i =
    Map.filter isQNameExternal $ sigDefinitions $ iSignature i

externalsToFOLs :: Interface -> ReaderT Options IO ()
externalsToFOLs i = do

  opts <- ask

  let externalsQnames :: Definitions
      externalsQnames = getExternals i
  -- LocIO.print $ Map.keys externalQnames

  let qNamesTypes :: Map QName Type
      qNamesTypes = Map.map defType externalsQnames

  liftIO $ LocIO.putStrLn "Types:"
  liftIO $ printListLn $ Map.toList qNamesTypes

  formulas <- liftIO $
              mapM (\ty -> runReaderT (typeToFormula ty) (opts, initialVars))
                   (Map.elems qNamesTypes)

  let qNamesFOLFormulas :: Map QName Formula
      qNamesFOLFormulas = Map.fromList $ zip (Map.keys qNamesTypes) formulas

  liftIO $ LocIO.putStrLn "FOL formulas:"
  liftIO $ printListLn $ Map.toList qNamesFOLFormulas

  let qNamesExternalsRole :: Map QName ExternalRole
      qNamesExternalsRole = Map.map getExternalRole externalsQnames

  let linesTPTP :: [LineTPTP]
      linesTPTP =
          map (\(qName, role, formula) -> externalToTPTP qName role formula) $
              zip3 (Map.keys qNamesFOLFormulas)
                   (Map.elems qNamesExternalsRole)
                   (Map.elems qNamesFOLFormulas)

  liftIO $ LocIO.putStrLn "TPTP formulas:"
  liftIO $ LocIO.print linesTPTP

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

  runReaderT (externalsToFOLs i) opts

main :: IO ()
main = catchImpossible runAgdaATP $
         \e -> do LocIO.putStr $ show e
                  exitFailure
