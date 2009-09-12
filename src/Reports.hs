{-# LANGUAGE CPP #-}

module Reports where

import Control.Monad ( when )
import Control.Monad.Reader ( ask )
import Control.Monad.Trans ( liftIO )

import Agda.Utils.Impossible ( Impossible (Impossible), throwImpossible )

import Monad ( T )

import Options ( Options, optVerbose )

import qualified System.IO.UTF8 as UTF8

import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.List ( wordsBy )

#include "undefined.h"
-----------------------------------------------------------------------------
-- Nice way to report things via the verbose option.
-- Adapted from Agda.TypeChecking.Monad.Options.

getVerbosity :: T (Trie String Int)
getVerbosity = do
-- ToDo optVerbose <$> commandLineOptions.
  (opts, _) <- ask
  return $ optVerbose opts

type VerboseKey = String

-- | Precondition: The level must be non-negative.
verboseS :: VerboseKey -> Int -> T () -> T ()
verboseS k n action | n < 0     =  __IMPOSSIBLE__
                    | otherwise = do
    t <- getVerbosity
    let ks = wordsBy (`elem` ".:") k
        m  = maximum $ 0 : Trie.lookupPath ks t
    when (n <= m) action

reportLn :: VerboseKey -> Int -> String -> T ()
reportLn k n s = verboseS k n $ liftIO $ UTF8.putStrLn (s ++ "\n")
