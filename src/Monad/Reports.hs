-----------------------------------------------------------------------------
-- Reports via the verbose option
-----------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module Monad.Reports ( reportS, reportSLn, VerboseKey ) where

-- Haskell imports
import Control.Monad       ( when )
import Control.Monad.State ( get )
import Control.Monad.Trans ( liftIO )

-- Agda library imports
import Agda.Interaction.Options ( Verbosity )
import Agda.Utils.Impossible    ( Impossible (Impossible), throwImpossible )
-- import Agda.Utils.Trie ( Trie )
import qualified Agda.Utils.Trie as Trie ( lookupPath )
import Agda.Utils.List ( wordsBy )

-- Local imports
import Monad.Base  ( T, TState(tOpts) )
import Options     ( Options(optVerbose) )

#include "../undefined.h"

-----------------------------------------------------------------------------
-- Nice way to report things via the verbose option.
-- Adapted from Agda.TypeChecking.Monad.Options.

type VerboseKey = String

getVerbosity :: T Verbosity
getVerbosity = do
  state ← get
  return $ optVerbose $ tOpts state

-- | Precondition: The level must be non-negative.
verboseS :: VerboseKey → Int → T () → T ()
verboseS k n action | n < 0     =  __IMPOSSIBLE__
                    | otherwise = do
    t ← getVerbosity
    let ks = wordsBy (`elem` ".:") k
        m  = maximum $ 0 : Trie.lookupPath ks t
    when (n <= m) action

reportS :: VerboseKey → Int → String → T ()
reportS k n s = verboseS k n $ liftIO $ putStr (s ++ "\n")

reportSLn :: VerboseKey → Int → String → T ()
reportSLn k n s = verboseS k n $ liftIO $ putStrLn (s ++ "\n")
