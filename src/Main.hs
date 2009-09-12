{-# LANGUAGE FlexibleInstances #-}

module Main where

import Agda.Interaction.FindFile ( toIFile )
import Agda.Interaction.Imports ( readInterface )
import Agda.Interaction.Options
    ( CommandLineOptions
    , defaultOptions
    , optInputFile
    )
import Agda.Syntax.Internal ( QName, Type )
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
    ( makeIncludeDirsAbsolute
    , setCommandLineOptions
    , Target(PersistentOptions)
    )
import Agda.Utils.FileName ( absolute, filePath, mkAbsolute )
import Agda.Utils.Impossible ( catchImpossible )
-- import Agda.Utils.Pretty

import Control.Monad.Reader
import Control.Monad.Trans

import Data.Map ( Map )
import qualified Data.Map as Map
-- import Data.Maybe

-- import FOL.Pretty
import FOL.Translation
import FOL.Types

import Monad ( initialVars )

import Options ( Options, parseOptions )

import Prelude hiding ( print, putStr, putStrLn )

import System.Directory ( getCurrentDirectory )
import System.Environment
import System.Exit
import qualified System.IO.UTF8 as UTF8
import System.IO.Unsafe ( unsafePerformIO )

printListLn :: Show a => [a] -> IO ()
printListLn []       = return ()
printListLn (x : xs) = do UTF8.putStrLn $ show x ++ "\n"
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

getExternalDefinitions :: Interface -> Definitions
getExternalDefinitions i =
    Map.filter isQNameExternal $ sigDefinitions $ iSignature i

agdaExternalsToFOL :: Interface -> ReaderT Options IO ()
agdaExternalsToFOL i = do

  opts <- ask

  let externalQnames :: Definitions
      externalQnames = getExternalDefinitions i
  -- UTF8.print $ Map.keys externalQnames
  let qNamesTypes :: Map QName Type
      qNamesTypes = Map.map defType externalQnames

  liftIO $ UTF8.putStrLn "Types:"
  liftIO $ printListLn $ Map.toList qNamesTypes

  let qNamesFOLFormulas :: Map QName Formula
      qNamesFOLFormulas =
          Map.map (\ty -> unsafePerformIO $ runReaderT (typeToFormula ty) (opts, initialVars))
                  qNamesTypes

  liftIO $ UTF8.putStrLn "FOL formulas:"
  liftIO $ printListLn $ Map.toList qNamesFOLFormulas


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

  runReaderT (agdaExternalsToFOL i) opts

main :: IO ()
main = catchImpossible runAgdaATP $
         \e -> do UTF8.putStr $ show e
                  exitFailure
